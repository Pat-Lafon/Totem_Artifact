let[@assert] rty1 =
  let s = ((true : [%v: int]) [@over]) in
  ((s == 0 && is_cons v && is_even (head v) true && is_nil (tail v)
    : [%v: ilist])
    [@under])

let[@assert] rty2 =
  let s = ((true : [%v: int]) [@over]) in
  ((len v 1 && s == 0
    && (fun ((n [@exists]) : int) ->
          len v n && n <= (s + 1) && n > 0 && all_evens v true)
    && not (fun ((x_13 [@exists]) : bool)
                ((x_14 [@exists]) : ilist)
                ((x_16 [@exists]) : int) ->
              not (s == 0)
              && x_13
              && is_nil x_14
              && is_even x_16 true
              && is_cons v && (head v) == x_16 && (tail v) == x_14)
    && not (fun ((x_13 [@exists]) : bool)
                ((s_11 [@exists]) : int)
                ((x_18 [@exists]) : ilist)
                ((n [@exists]) : int)
                ((x_20 [@exists]) : int) ->
              not (s == 0)
              && not x_13
              && 0 <= s_11 && s_11 >= 0 && s_11 < s && s_11 == (s - 1)
              && len x_18 n && n <= (s_11 + 1) && n > 0
              && all_evens x_18 true
              && is_even x_20 true
              && is_cons v && (head v) == x_20 && (tail v) == x_18)
    : [%v: ilist])
    [@under])