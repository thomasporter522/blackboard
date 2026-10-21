// import { useState } from 'react'
// import heroImg from './assets/hero.png'
// import reactLogo from './assets/react.svg'
// import viteLogo from './assets/vite.svg'
import CodeMirror from '@uiw/react-codemirror'
import { EditorView, Decoration } from '@codemirror/view'
import { EditorState } from "@codemirror/state";
import './App.css'
import { blackboardTheme } from "./CodeTheme.tsx"


function print(s) {
  console.log(s)
}

// function DisplayCodeBlock({ code, height = "auto" }: { code: string, height?: string }) {
//     const lineCount = code.split('\n').length + 1
//     const calculatedHeight = `${(lineCount) * 20}px` // 20px per line + 1 extra line
    
//     return (
//       <CodeMirror
//         value={code}
//         height={height === "auto" ? calculatedHeight : height}
//         // theme={}
//         extensions={[
//           EditorView.theme({
//             '.cm-content': {
//               padding: '3px !important',
//               margin: '0px !important',
//               minHeight: '0px !important'
//             },
//           })
//         ]}
//         basicSetup={{
//           lineNumbers: false,
//           foldGutter: false,
//           dropCursor: false,
//           allowMultipleSelections: false,
//           searchKeymap: false,
//           autocompletion: false,
//           closeBrackets: false,
//           history: false
//         }}
//         editable={false}
//       />
//     )
//   }

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
        })]}
      //   EditorView.decorations.of(Decoration.set(
      //     semanticErrors
      //       .filter(error => (error.type !== "hole"))
      //       .filter(error => (error.from < error.to))
      //       .sort((a, b) => a.from - b.from)
      //       .map(error => 
      //         Decoration.mark({
      //           class: "semantic-error"
      //         }).range(error.from, error.to)
      //       )
      //   )),
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
      onChange={(val, viewUpdate) => {
        print("change")
      }}
      onCreateEditor={(view) => {
        print("create")
      }}
      onUpdate={(viewUpdate) => {
        print("update")
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
