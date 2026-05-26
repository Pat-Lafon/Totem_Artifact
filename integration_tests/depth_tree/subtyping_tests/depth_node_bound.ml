let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((idx1_0 [@exists]) : int)
        ((x_3 [@exists]) : bool)
        ((idx20_7 [@exists]) : itree)
        ((s_6 [@exists]) : int)
        ((idx20 [@exists]) : itree)
        ((u1 [@exists]) : int)
        ((idx20_8 [@exists]) : itree)
        ((s_7 [@exists]) : int)
        ((idx20_9 [@exists]) : itree)
        ((u2 [@exists]) : int)
        ((idx63 [@exists]) : itree) ->
      ((x_3) #==> (s == 0)) && ((s == 0) #==> (x_3))
      && ((not x_3) #==> (s > 0)) && ((s > 0) #==> (not x_3))
      && not x_3
      && 0 <= s_6 && s_6 >= 0 && s_6 < s && s_6 == (s - 1)
      && depth idx20 u1 && u1 <= s_6
      && idx20_7 == idx20
      && 0 <= s_7 && s_7 >= 0 && s_7 < s && s_7 == (s - 1)
      && depth idx20_9 u2 && u2 <= s_7
      && idx20_8 == idx20_9
      && is_node idx63 && (value idx63) == idx1_0
      && (left idx63) == idx20_7 && (right idx63) == idx20_8
      && v == idx63
    : [%v: itree])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((x_3 [@exists]) : bool)
        ((u [@exists]) : int) ->
      ((x_3) #==> (s == 0)) && ((s == 0) #==> (x_3))
      && ((not x_3) #==> (s > 0)) && ((s > 0) #==> (not x_3))
      && not x_3
      && not (is_leaf v) && not (s == 0)
      && depth v u && u <= s
    : [%v: itree])
    [@under])
