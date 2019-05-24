"
" VIM mode for editing ATS source
" Author: Yuri D'Elia <wavexx AT thregr DOT org>
" Copyright (C) 2010 Yuri D'Elia
"

" ATS syntax plugin for VIM >= 6.x
if exists("b:current_syntax") && b:current_syntax == "ats"
  finish
endif

syn case match

" Comments
syn match atsCommentCPP "\/\/.*"
syn region atsCommentOC start="(\*" end="\*)" contains=atsCommentOC
syn region atsCommentEOF start="\/\/\/\/" end="\%$"

hi link atsCommentCPP Comment
hi link atsCommentOC Comment
hi link atsCommentEOF Comment


" Common definitions
syn match atsTypeDecl ":" skipwhite nextgroup=atsTypeType
syn match atsTypeType "[[:alnum:]_]\+" contained

hi link atsTypeType Type

" Strings
syn match atsCharacter "'\\\d\d\d'\|'\\[\'ntbr]'\|'.'"
syn region atsString start=+"+ skip=+\\\\\|\\"+ end=+"+

hi link atsCharacter Character
hi link atsString String


" Functions
syn keyword Keyword extern implement

syn match atsFun "\<\(fn\|fun\)\>" skipwhite nextgroup=atsTemplArgs,atsFunName
syn region atsTemplArgs start="{" end="}" contained skipwhite contains=atsArgList
syn match atsFunName "[[:alnum:]_]\+" contained skipwhite nextgroup=atsFunStaArgs,atsFunArgs,atsFunRet
syn region atsFunStaArgs start="{" end="}" contained skipwhite contains=atsArgList
syn region atsFunArgs start="(" end=")" contained skipwhite contains=atsArgList
syn match atsFunRet "" contained skipwhite nextgroup=atsTypeDecl

hi link atsFun Keyword
hi link atsFunName Function

" Argument lists
syn match atsArgList "[[:alnum:]_]\+" contained skipwhite nextgroup=atsTypeDecl,atsArgListComma
syn match atsArgListComma "," contained skipwhite nextgroup=atsArgList

hi link atsArgList Identifier


" Includes
syn match atsLoadCmd "\<\(sta\|dyn\)load\>" skipwhite nextgroup=atsLoadNS,atsLoadPath
syn match atsLoadNS "[[:alnum:]_]\+" contained skipwhite nextgroup=atsLoadEq
syn match atsLoadEq "=" contained skipwhite nextgroup=atsLoadPath
syn region atsLoadPath start=+"+ end=+"+ contained

hi link atsLoadNS Identifier
hi link atsLoadCmd Keyword
hi link atsLoadPath Include

" C blocks
syn region atsCReg start="%{[#$^]\?" end="%}"
hi link atsCReg PreProc

syn match Include "#include\>.*"
syn match Define "#define\>.*"


" TODO: improperly parsed syntax
syn keyword Conditional if then else case case+ of =>
syn keyword Statement let where in begin end and
syn keyword Repeat for while
syn keyword Keyword typedef viewtypedef true false val var
syn keyword Operator _

let b:current_syntax = "ats"

" end of [ats.vim]
