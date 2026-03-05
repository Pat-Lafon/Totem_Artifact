let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) ((x [@exists]) : int) ((x2 [@exists]) : int) ((l2 [@exists]) : ilist)  ->
       len v n && n <= s + 1 && n > 0 && s == 0 && is_cons v && tail v == l2 && is_nil l2 && all_evens l2 true && head v == x && is_even x true && all_evens v true
     : [%v: ilist])
     [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((s == 0
    &&
    fun ((x [@exists]) : int)
      ((x2 [@exists]) : int)
      ((l2 [@exists]) : ilist)
     -> is_cons v && head v == x && x == x2 * 2 && tail v == l2 && is_nil l2 && is_even x true
     : [%v: ilist])
     [@under])
