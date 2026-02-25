let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x [@exists]) : int) ((l [@exists]) : ilist) ((s_15 [@exists]) : int) ->
     s > 0 && s_15 >= 0 && s_15 < s
     && s_15 == s - 1
     && len l s_15 && uniq l true
     && (mem l x false)
     && is_cons v && head v == x && tail v == l
    : [%v: ilist])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x [@exists]) : int) ((s_15 [@exists]) : int) ((l [@exists]) : ilist) ->
     s > 0 && s_15 >= 0 && s_15 < s
     && s_15 == s - 1
     && len l s_15 && uniq l true
     && (mem l x false)
     && (not (is_nil v))
     && len v s && uniq v true
    : [%v: ilist])
    [@under]
