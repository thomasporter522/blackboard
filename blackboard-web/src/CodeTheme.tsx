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
    border: '2px var(--orang))'
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
    backgroundColor: 'var(--bg)',
    color: 'var(--beam)',
    border: 'none',
    borderRight: '2px solid var(--beam)',
  },
  // tooltips
  '.cm-tooltip-cursor': {
    "font-size" : 'var(--completion-font-size)',
    color: 'var(--delim-color)',
    backgroundColor: 'var(--bg)',
    borderRadius: "3px 3px 3px 0px",
    // border: '0.5px solid var(--beam)',
    border: '1px solid var(--beam)',
    transform: "translateX(13px) translateY(14px)",
    padding: '0px 5px 0px 5px',
  },
  '.cm-tooltip-above .cm-tooltip-arrow': {
    transform: "translateX(-8px)",
    '&:before': {
      borderTopColor: "var(--beam)",
      borderLeftWidth: "0",
    },
  },
  // errors
  '.cm-diagnostic-error': {
    backgroundColor: 'var(--bg)',
    border: '1px solid var(--beam)',
  },
  '.cm-lintPoint-error': {
    '&::after': {
      width: '4px',
      height: '3.5px',
      border: 'none',
      borderTop: '2.5px solid var(--mark-color)',
    }
  },
  
}, { dark: true })

export const blackboardTheme = [
  blackboardEditorTheme,
//   syntaxHighlighting(blackboardHighlightStyle)
]