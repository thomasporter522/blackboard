// import { useState } from 'react'
// import heroImg from './assets/hero.png'
// import reactLogo from './assets/react.svg'
// import viteLogo from './assets/vite.svg'
import { useState, useEffect } from 'react';
import CodeMirror from '@uiw/react-codemirror'
import { EditorView, Decoration, keymap } from '@codemirror/view'
import { EditorState, StateField, Prec } from "@codemirror/state";
import type {Tooltip} from "@codemirror/view"
import { showTooltip} from "@codemirror/view"
import type {Diagnostic} from "@codemirror/lint";
import { linter } from "@codemirror/lint";
import './App.css'
import Markdown from 'react-markdown'

import { blackboardTheme } from "./CodeTheme.tsx"

const init_text = `assume 
x : type
valid by 
check
end
construct
z : type
by
given M : prop,
given H : type -> M,
?
end
?`

function dia_test_init() { return globalThis.dia_test_init() }

function dia_test_case(s) { return globalThis.dia_test_case(s) }

function dia_opt_player(s) { return globalThis.dia_opt_player(s) }

function dia_opt_player_select(s, i) { return globalThis.dia_opt_player_select({state: s, choice : i}) }

function dia_opt_player_can_select_hidden(s, i) { return globalThis.dia_opt_player_can_select_hidden({state: s, choice : i}) }

function dia_opt_player_select_hidden(s, i) { return globalThis.dia_opt_player_select_hidden({state: s, choice : i}) }

function dia_opt_puter(s) { return globalThis.dia_opt_puter(s); }

function parse_test(s, cursor_position) { return globalThis.parse_test(s, cursor_position); }

type error = {
    message: string, 
    range: number[],
    underline : Boolean,
};

type goal = {
    statement: string, 
    context: string[],
    range: number[],
};

function print(s) {
  console.log(s)
}

type parse_info = {
  cursor_position : number;
  runes : number[][];
  delimiters : number[][];
  parseerrors : error[];
  elaberrors : error[];
  checkerrors : error[];
  completions : string[];
  victories : number[][];
  goals : goal[];
}

function process(state : EditorState) : parse_info {
  let cursor_position = state.selection.ranges[0].from;
  let parse_result = parse_test(state.doc.toString(), cursor_position);
  return {
    cursor_position : cursor_position,
    runes : parse_result.runes,
    delimiters : parse_result.delimiters,
    parseerrors : parse_result.parseerrors,
    elaberrors : parse_result.elaberrors,
    checkerrors : parse_result.checkerrors,
    completions : parse_result.completions,
    victories : parse_result.victories,
    goals : parse_result.goals,
  }
}

const parseInfoField = StateField.define<parse_info>({
  create(state) {
    return process(state)
  },

  update(pi, tr) {
    return (tr.docChanged || tr.selection) ? process(tr.state) : pi
  },
})


function decorateDelims(state : EditorState) {
  function decorateDelim(x : number[]) {
    return Decoration.mark({class: "delimiter"}).range(x[0], x[1])
  };
  return Decoration.set(state.field(parseInfoField).delimiters.map(decorateDelim))
}

function decorateVictories(state : EditorState) {
  function decorateVictory(x : number[]) {
    return Decoration.mark({class: "victory"}).range(x[0], x[1])
  };
  return Decoration.set(state.field(parseInfoField).victories.map(decorateVictory))
}

function decorateInteractions(state : EditorState) {
  function decorateInteraction(x : goal) {
    return Decoration.mark({class: "interaction"}).range(x.range[0], x.range[1])
  };
  return Decoration.set(state.field(parseInfoField).goals.filter(x => x.range[0] < x.range[1]).map(decorateInteraction))
}

const delimiterExtension = EditorView.decorations.compute([parseInfoField], state => decorateDelims(state))
const victoryExtension = EditorView.decorations.compute([parseInfoField], state => decorateVictories(state))
const interactionExtension = EditorView.decorations.compute([parseInfoField], state => decorateInteractions(state))

function render_message(_view : EditorView, diaState, setDiaState, messageText : string, range: number[]) : Node {
  const node = document.createElement("div");
  const sigil =  document.createElement("span");
  sigil.textContent = "⚠ ";
  sigil.className = "error-sigil";
  node.appendChild(sigil);
  const message = document.createElement("span");
  message.textContent = messageText;
  node.appendChild(message);
  const asker =  document.createElement("button");
  asker.onclick = _ => setDiaState(diaState => dia_opt_player_select_hidden(diaState, "explain_error"));
  asker.textContent = " ⓘ";
  asker.className = "error-asker";
  if(dia_opt_player_can_select_hidden(diaState, "explain_error")) {
    node.appendChild(asker);
  }
  return node
}

function render_diagnostics(view : EditorView, diaState, setDiaState) : readonly Diagnostic[] {
  const info = view.state.field(parseInfoField);
  const diagnostics: Diagnostic[] = [];
  info.runes.map(e => diagnostics.push({from: e[0], to: e[1], severity: "error", message: "IMPOSSIBLE", renderMessage: view => render_message(view, diaState, setDiaState, "unrecognized character", e), markClass: "color-error"}));
  info.parseerrors.map(e => diagnostics.push({from: e.range[0], to: e.range[1], severity: "error", message: "IMPOSSIBLE", renderMessage: view => render_message(view, diaState, setDiaState, e.message, e.range), markClass: e.underline ? "line-error" : "color-error"}));
  info.elaberrors.map(e => diagnostics.push({from: e.range[0], to: e.range[1], severity: "error", message: "IMPOSSIBLE", renderMessage: view => render_message(view, diaState, setDiaState, e.message, e.range), markClass: e.underline ? "line-error" : "color-error"}));
  info.checkerrors.map(e => diagnostics.push({from: e.range[0], to: e.range[1], severity: "error", message: "IMPOSSIBLE", renderMessage: view => render_message(view, diaState, setDiaState, e.message, e.range), markClass: e.underline ? "line-error" : "color-error"}));
  return diagnostics
}

function linterExtension(diaState, setDiaState) {
  return linter(view => render_diagnostics(view, diaState, setDiaState), {delay: 0});
}

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
  const body = view.state.doc.toString();
  const prefix = 
    info.cursor_position-1 >= body.length ? "" : 
    info.cursor_position-1 < 0 ? "" : 
    (body[info.cursor_position-1] == "\n" 
      || body[info.cursor_position-1] == " "
      || body[info.cursor_position-1] == "\t") ? "" : " "
  const inserted = prefix + info.completions[0];
  view.dispatch({
    changes: {
        from: info.cursor_position,
        to: info.cursor_position,
        insert: inserted
    },
    selection: {anchor: info.cursor_position + inserted.length}
  });
  return true
}

const insertCompletionExtension = keymap.of([{key: "Tab", run:insertCompletion}])

function extensions(diaState, setDiaState) {
  return [
  // mintlang(),
  EditorView.theme({
    '.cm-editor': {
      width: '600px',
      maxWidth: '600px'
    },
    '.cm-scroller': {  overflow: 'false' },
    '.cm-content': { whiteSpace: 'pre' },
    '.cm-line': { whiteSpace: 'pre' }
  }),
  parseInfoField,
  linterExtension(diaState, setDiaState),
  interactionExtension,
  victoryExtension,
  delimiterExtension,
  completionExtension,
  Prec.highest(insertCompletionExtension),
  ];
}


function MainCodeblock(setInfo, extensions) {
  return <div className='mainBlock'><CodeMirror
      value={init_text}
      height="600px"
      theme={blackboardTheme}
      extensions={extensions}
      basicSetup={{
        history: true,
        foldGutter: false,
        dropCursor: false,
        allowMultipleSelections: false,
        closeBrackets: false,
      }}
      onChange={(_val, _viewUpdate) => {
        // block_contexts = val;
      }}
      onCreateEditor={(view) => { setInfo(view.state.field(parseInfoField)) }}
      onUpdate={(viewUpdate) => { 
        setInfo(viewUpdate.view.state.field(parseInfoField))
      }}
    /></div>;
}

function displayGoal(g : goal) {
  const contextEntries = g.context.toReversed().map((s, i) => <div key={i} className='contextEntry'>{s}</div>);
  return <><h3>Goal</h3>{g.statement}<h3>Context</h3>{contextEntries}</>
}

function infoBarInfo(info : parse_info) {
  if (info == null) return <></>;
  const infolist = info.goals.filter(goal => goal.range[0] <= info.cursor_position && info.cursor_position <= goal.range[1]);
  return infolist.length > 0 ? displayGoal(infolist[0]) : 
    info.goals.length > 1 ? <><h3>{info.goals.length} goals remaining</h3></> :
    info.goals.length == 1 ? <><h3>1 goal remaining</h3></> : <><h3>No goals remaining</h3></>
}

function InfoBar(info : parse_info) {
  return <div className='infobar'> {infoBarInfo(info)} </div>;
}

function DiaButton(key, setDiaState, next, text) {
  return <button key={key} className="diaButton" onClick={_ => {setDiaState(next)}}>{text}</button>;
}

function NextOptionBox(nextDiaState, setDiaState) {
  return DiaButton(0, setDiaState, nextDiaState, ">");
}

function OptionBox(diaState, setDiaState) {
  return dia_opt_player(diaState)[0].map((s, i) => DiaButton(i, setDiaState, dia_opt_player_select(diaState, i), "> " + s) );
}

function updateDialogue(diaState, setDiaState, setPuterMessage, setDiaButtons) {
  const diaCase = dia_test_case(diaState);
  if(diaCase == 0) { setPuterMessage("DONE."); setDiaButtons(<></>); }
  if(diaCase == 1) { setDiaButtons(OptionBox(diaState, setDiaState))};
  if(diaCase == 2) {
    const [_, message, newDiaState] = dia_opt_puter(diaState);
    setPuterMessage(message);
    const newDiaCase = dia_test_case(newDiaState);
    if(newDiaCase == 1) { setDiaState(newDiaState); }
    else { setDiaButtons(NextOptionBox(newDiaState, setDiaState))};
  }
  if(diaCase > 2) throw new Error("IMPOSSIBLE DIA CASE");
}

function DialogueBox(puterMessage, diaButtons) {
  return <div className='diabox'> <div className='puterMessage'><Markdown>{puterMessage}</Markdown></div> <div className='diaButtons'> {diaButtons} </div> </div>;
}

function App() {
  const [diaState, setDiaState] = useState(dia_test_init)
  const [puterMessage, setPuterMessage] = useState("")
  const [diaButtons, setDiaButtons] = useState(<></>)
  const [info, setInfo] = useState<parse_info>(null);
  const block = MainCodeblock(setInfo, extensions(diaState, setDiaState));
  const dialogue = DialogueBox(puterMessage, diaButtons);
  const infobar = InfoBar(info);
  
  useEffect(() => updateDialogue(diaState, setDiaState, setPuterMessage, setDiaButtons), [diaState]);
  return (<>
    <div className='page'>
      <div className='topSection'>
        <h1>Blackboard</h1>
      </div>
      <div className='nontopSection'>
        <div className='leftSection'>
        </div>
        <div className='middleSection'>
          {block}
          {dialogue}
        </div>
        <div className='rightSection'>
          {infobar}
        </div>
      </div>
    </div>
    </>
  )
}

export default App
