import { EditorView } from '@codemirror/view'
import { HighlightStyle, syntaxHighlighting } from '@codemirror/language'
import { tags as t } from '@lezer/highlight'


const blackboardEditorTheme = EditorView.theme({
  '&': {
    color: 'var(--text)',
    backgroundColor: 'var(--bg)',
    fontSize: '15pt'
  },
  '& *': {
    fontFamily: "'FiraCode' !important"
  },
  '.cm-content': {
    padding: '16px',
    minHeight: '200px'
  },
  '.cm-focused': {
    outline: 'none'
  },
  '.cm-editor': {
    borderRadius: '0px',
  },
  '.cm-line': {
    padding: '0 2px',
    lineHeight: '1.6'
  },
  '.cm-cursor': {
    borderLeft: '2px var(--orang))'
  },
  '.cm-selectionBackground': {
    backgroundColor: 'var(--select) !important',
    opacity: '0.3',
  },
  '.cm-activeLine': {
    backgroundColor: 'transparent' ,
  },
  // gutters
  '.cm-gutters': {
    backgroundColor: 'var(--bg)', // Background of the gutter area
    color: 'var(--beam)', // Line number text color
    border: 'none',
    borderRight: '2px solid var(--beam)',
  },
  '.cm-activeLineGutter': {
    backgroundColor: 'inherit', // Active line number background
    color: 'inherit' // Active line number text color
  },
}, { dark: true })

export const blackboardTheme = [
  blackboardEditorTheme,
//   syntaxHighlighting(blackboardHighlightStyle)
]