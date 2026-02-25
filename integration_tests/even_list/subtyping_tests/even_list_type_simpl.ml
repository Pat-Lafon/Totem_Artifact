let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((s > 0
    && fun ((s_2 [@exists]) : int)
         ((x_3 [@exists]) : ilist)
         ((n_inner [@exists]) : int)
         ((x_inner [@exists]) : int)
         ((x_5 [@exists]) : int) ->
       0 <= s_2 && s_2 == s - 1
       && len x_3 n_inner && n_inner <= s_2 + 1 && n_inner > 0 && n_inner > 1
      && all_evens x_3 true  && is_cons x_3  && head x_3 == x_inner && is_even x_inner true
       && is_even x_5 true && is_cons v && head v == x_5 && tail v == x_3
     : [%v: ilist])
     [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int)
       ((x [@exists]) : int) ->
      len v n && n <= s + 1 && n > 0 && n > 2
      && all_evens v true && is_cons v && head v == x && is_even x true
     : [%v: ilist])
     [@under])