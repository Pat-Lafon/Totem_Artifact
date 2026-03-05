let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((not (s == 0)
    && (fun ((idx7 [@exists]) : int)
            ((idx10_3 [@exists]) : ilist)
            ((idx10a [@exists]) : ilist)
            ((n_a [@exists]) : int)
            ((s_4a [@exists]) : int)
            ((idx10b [@exists]) : ilist)
            ((n_b [@exists]) : int)
            ((s_4b [@exists]) : int) ->

          0 <= s_4a && s_4a >= 0 && s_4a < s && s_4a == (s - 1)
           && len idx10a n_a && n_a <= (s_4a + 1) && n_a > 0
          (*&& all_evens idx10a true && is_even idx7 true*)
          && idx10_3 == idx10a
          && 0 <= s_4b && s_4b >= 0 && s_4b < s && s_4b == (s - 1)
          && len idx10b n_b && n_b <= (s_4b + 1) && n_b > 0
          (*&& all_evens idx10b true*)
          && v == idx10b )
    : [%v: ilist])
    [@under])

let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((not (s == 0)
    && (fun ((idx7 [@exists]) : int)
            ((idx10_3 [@exists]) : ilist)
            ((idx10a [@exists]) : ilist)
            ((n_a [@exists]) : int)
            ((s_4a [@exists]) : int)
            ((idx20 [@exists]) : ilist) ->
         0 <= s_4a && s_4a >= 0 && s_4a < s && s_4a == (s - 1)
          && len idx10a n_a && n_a <= (s_4a + 1) && n_a > 0
          (* &&  is_even idx7 true
          && all_evens idx10a true*)
          && idx10_3 == idx10a
         && is_cons idx20 && (head idx20) == idx7 && (tail idx20) == idx10_3
          && v == idx20)
    : [%v: ilist])
    [@under])