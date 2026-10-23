// import { useState } from 'react'
// import heroImg from './assets/hero.png'
// import reactLogo from './assets/react.svg'
// import viteLogo from './assets/vite.svg'
import CodeMirror from '@uiw/react-codemirror'
import { EditorView, Decoration, keymap } from '@codemirror/view'
import { EditorState, StateField, Prec } from "@codemirror/state";
import type {Tooltip} from "@codemirror/view"
import { showTooltip} from "@codemirror/view"
import type {Diagnostic} from "@codemirror/lint";
import { linter } from "@codemirror/lint";
import './App.css'
import { blackboardTheme } from "./CodeTheme.tsx"

function parse_test(s, cursor_position) {
  return globalThis.parse_test(s, cursor_position);
}

// const my_obj = globalThis.my_obj;

type error = {
    message: string, 
    range: number[],
};

// var block_contexts : string = "";
// var cursor_position : number = 0;
// var runes : number[][] = [];
// var delimiters : number[][] = [];
// var parseerrors : error[] = [];
// var completions : string[] = [];

function print(s) {
  console.log(s)
}

type parse_info = {
  cursor_position : number;
  runes : number[][];
  delimiters : number[][];
  parseerrors : error[];
  completions : string[];
}

function process(state : EditorState) : parse_info {
  let cursor_position = state.selection.ranges[0].from;
  let parse_result = parse_test(state.doc.toString(), cursor_position);
  return {
    cursor_position : cursor_position,
    runes : parse_result.runes,
    delimiters : parse_result.delimiters,
    parseerrors : parse_result.parseerrors,
    completions : parse_result.completions,
  }
}

const parseInfoField =  StateField.define<parse_info>({
  create(state) {
    return process(state)
  },

  update(_pi, tr) {
    return process(tr.state)
  },
})

function decorateDelims(state : EditorState) {
  function decorateDelim(x : number[]) {
    return Decoration.mark({class: "delimiter"}).range(x[0], x[1])
  };
  return Decoration.set(state.field(parseInfoField).delimiters.map(decorateDelim))
}

const delimiterExtension = EditorView.decorations.compute([parseInfoField], state => decorateDelims(state))


function render_diagnostics(view : EditorView) : readonly Diagnostic[] {
  const info = view.state.field(parseInfoField);
  const diagnostics: Diagnostic[] = [];
  info.runes.map(e => diagnostics.push({from: e[0], to: e[1], severity: "error", message: "unrecognized character", markClass: "rune"}));
  info.parseerrors.map(e => diagnostics.push({from: e.range[0], to: e.range[1], severity: "error", message: e.message, markClass: "shard"}));
  return diagnostics
}

const linterExtension = linter(render_diagnostics, {delay: 0});

function getCursorTooltips(state): readonly Tooltip[] {
  const info = state.field(parseInfoField);
  if(info.completions.length == 0) return [];
  return [{
        pos: info.cursor_position,
        above: true,
        strictSide: true,
        arrow: true,
        create: () => {
          let dom = document.createElement("div")
          dom.className = "cm-tooltip-cursor"
          dom.textContent = info.completions.join(" ")
          return {dom}
        }
      }]
}

const completionExtension = showTooltip.computeN([parseInfoField], state => getCursorTooltips(state))

function insertCompletion(view : EditorView) {
  const info = view.state.field(parseInfoField);
  if(info.completions.length == 0) { return false } 
  view.dispatch({
    changes: {
        from: info.cursor_position,
        to: info.cursor_position,
        insert: info.completions[0]
    },
    selection: {anchor: info.cursor_position + info.completions[0].length}
  });
  return true
}

const insertCompletionExtension = keymap.of([{key: "Tab", run:insertCompletion}])

function MainCodeblock() {
  return <CodeMirror
      value={""}
      height="800px"
      theme={blackboardTheme}
      extensions={[
        // mintlang(),
        EditorView.theme({
          '.cm-editor': {
            // width: '100%',
            width: '600px',
            maxWidth: '600px'
          },
          '.cm-scroller': {
            overflow: 'false'  // Enable horizontal scrolling
          },
          '.cm-content': {
            whiteSpace: 'pre'  // Prevent text wrapping
          },
          '.cm-line': {
            whiteSpace: 'pre'  // Prevent line wrapping
          }
        }),
        parseInfoField,
        linterExtension,
        delimiterExtension,
        completionExtension,
        Prec.highest(insertCompletionExtension),
        // cursorTooltipField,
        // EditorView.decorations.of(Decoration.set(
        //   errors
        //     .map(error => 
        //       Decoration.mark({
        //         class: "semantic-error"
        //       }).range(error[1], error[2])
        //     )
        // )),
        ]}
      //   EditorView.decorations.of(Decoration.set(
      //     holes
      //       .sort((a, b) => (a[0].valueOf() - b[0].valueOf()))
      //       .map(h => 
      //         Decoration.mark({
      //           class: "hole"
      //         }).range(h[0].valueOf(), h[0].valueOf()+1)
      //       )
      //   )),
      //   autoReplace,
      // ]}
      basicSetup={{
        history: true,
        foldGutter: false,
        dropCursor: false,
        allowMultipleSelections: false,
      }}
      onChange={(_val, _viewUpdate) => {
        // block_contexts = val;
      }}
      onCreateEditor={(_view) => { }}
      onUpdate={(_viewUpdate) => { 
        // insertCompletion(_viewUpdate.view)
        // cursor_position = viewUpdate.view.state.selection.ranges[0].from; 
        // process(block_contexts, cursor_position);
      }}
    />;
}

function App() {
  // const [count, setCount] = useState(0)
  const block = MainCodeblock();
  return (<>
    <h1>Blackboard</h1>
    {block}
    </>
  )
}

export default App
