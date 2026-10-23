// import { useState } from 'react'
// import heroImg from './assets/hero.png'
// import reactLogo from './assets/react.svg'
// import viteLogo from './assets/vite.svg'
import CodeMirror from '@uiw/react-codemirror'
import { EditorView, Decoration } from '@codemirror/view'
import { EditorState } from "@codemirror/state";
import type {Diagnostic} from "@codemirror/lint";
import { linter } from "@codemirror/lint";
import './App.css'
import { blackboardTheme } from "./CodeTheme.tsx"

function lex_test(s) {
  return globalThis.lex_test(s);
}

function parse_test(s) {
  return globalThis.parse_test(s);
}

// const my_obj = globalThis.my_obj;

var runes : number[][] = [];
var delimiters : number[][] = [];
var shards : number[][] = [];

type errors_type = number[][];

function print(s) {
  console.log(s)
}

function clean_errors(es : any) : errors_type {
  if(es == 0) {
    return [];
  } else {
    var re : any[][] = [];
    for(var i = 0; i < es.length; i ++) {
      re = re.concat([es[i]])
    }
    return re
  }
}

function process(s : string) {
  let parse_result = parse_test(s);
  runes = parse_result.runes;
  delimiters = parse_result.delimiters;
  shards = parse_result.shards;
}

function render_diagnostics(_view : EditorView) : readonly Diagnostic[] {
  const diagnostics: Diagnostic[] = [];
  runes.map(e => diagnostics.push({from: e[0], to: e[1], severity: "error", message: "unrecognized character", markClass: "rune"}));
  delimiters.map(e => diagnostics.push({from: e[0], to: e[1], severity: "hint", message: "", markClass: "delimiter"}));
  shards.map(e => diagnostics.push({from: e[0], to: e[1], severity: "error", message: "unmatched delimiter", markClass: "shard"}));
  return diagnostics
}

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
        linter(render_diagnostics),
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
      onChange={(val, _viewUpdate) => {
        process(val)
      }}
      onCreateEditor={(_view) => { }}
      onUpdate={(_viewUpdate) => { }}
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
