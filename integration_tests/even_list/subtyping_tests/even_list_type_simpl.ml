let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((x_0 [@exists]) : bool)
        ((x_1 [@exists]) : ilist)
        ((x_2 [@exists]) : int)
        ((x_4 [@exists]) : bool)
        ((x_5 [@exists]) : ilist)
        ((x_6 [@exists]) : int)
        ((s_2 [@exists]) : int)
        ((x_9 [@exists]) : ilist)
        ((n [@exists]) : int)
        ((x_10 [@exists]) : int) ->
      ((x_0) #==> (s == 0)) && ((s == 0) #==> (x_0))
      && ((not x_0) #==> (s > 0)) && ((s > 0) #==> (not x_0))
      && ((x_0
           && is_nil x_1
           && is_cons v && (head v) == (x_2 * 2) && (tail v) == x_1)
          || (not x_0
              && ((x_4
                   && is_nil x_5
                   && is_cons v && (head v) == (x_6 * 2) && (tail v) == x_5)
                  || (not x_4
                      && 0 <= s_2 && s_2 >= 0 && s_2 < s && s_2 == (s - 1)
                      && len x_9 n && n <= (s_2 + 1) && n > 0
                      && all_evens x_9 true
                      && is_cons v && (head v) == (x_10 * 2) && (tail v) == x_9))))
    : [%v: ilist])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((x_0 [@exists]) : bool)
        ((n [@exists]) : int) ->
      ((x_0) #==> (s == 0)) && ((s == 0) #==> (x_0))
      && ((not x_0) #==> (s > 0)) && ((s > 0) #==> (not x_0))
      && len v n && n <= (s + 1) && n > 0
      && all_evens v true
    : [%v: ilist])
    [@under])