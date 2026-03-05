let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((s == 0 && is_leaf v
    || (s > 0
        && (is_leaf v
            || (fun ((s_2 [@exists]) : int)
                    ((lt [@exists]) : itree)
                    ((u1 [@exists]) : int)
                    ((s_3 [@exists]) : int)
                    ((rt [@exists]) : itree)
                    ((u2 [@exists]) : int)
                    ((n [@exists]) : int) ->
                  s_2 == s - 1 && 0 <= s_2
                  && depth lt u1 && u1 <= s_2
                  && s_3 == s - 1 && 0 <= s_3
                  && depth rt u2 && u2 <= s_3
                  && is_node v && value v == n && left v == lt && right v == rt)))
     : [%v: itree])
     [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((u [@exists]) : int) ->
      depth v u && u <= s
     : [%v: itree])
     [@under])