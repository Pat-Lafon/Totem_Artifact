let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((x_0 [@exists]) : bool)
        ((x_1 [@exists]) : bool)
        ((s_2 [@exists]) : int)
        ((lt [@exists]) : itree)
        ((u1 [@exists]) : int)
        ((s_3 [@exists]) : int)
        ((rt [@exists]) : itree)
        ((u2 [@exists]) : int)
        ((n [@exists]) : int) ->
      ((x_0) #==> (s == 0)) && ((s == 0) #==> (x_0))
      && ((not x_0) #==> (s > 0)) && ((s > 0) #==> (not x_0))
      && ((x_0 && is_leaf v)
          || (not x_0
              && ((x_1 && is_leaf v)
                  || (not x_1
                      && 0 <= s_2 && s_2 >= 0 && s_2 < s && s_2 == (s - 1)
                      (* && depth lt u1 *) && u1 <= s_2
                      && 0 <= s_3 && s_3 >= 0 && s_3 < s && s_3 == (s - 1)
                      (* && depth rt u2*) && u2 <= s_3
                      && is_node v (* && (value v) == n
                      && (left v) == lt && (right v) == rt *)))))
    : [%v: itree])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((x_0 [@exists]) : bool)
        ((u [@exists]) : int) ->
      ((x_0) #==> (s == 0)) && ((s == 0) #==> (x_0))
      && ((not x_0) #==> (s > 0)) && ((s > 0) #==> (not x_0))
      && depth v u && u <= s
    : [%v: itree])
    [@under])