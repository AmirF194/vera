" Vera filetype settings

if exists("b:did_ftplugin")
	finish
endif
let b:did_ftplugin = 1

setlocal commentstring=--\ %s
setlocal comments=:--
setlocal matchpairs+=<:>

" Undo the above when the filetype changes, so a buffer switched away from
" veralang does not keep Vera's comment leader or angle-bracket matching.
" 'matchpairs' is restored by assignment rather than by removing "<:>",
" which would also strip it from a filetype that legitimately set it.
let b:undo_ftplugin = 'setlocal commentstring< comments< matchpairs<'
