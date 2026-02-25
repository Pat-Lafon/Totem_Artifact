let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((s > 0
    && (not (is_nil v))
    && len v s
    && all_equal v x true
    : [%v: ilist])
    [@under])

let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((fun ((x_2 [@exists]) : int)
      ((_25 [@exists]) : ilist)
      ((s_6 [@exists]) : int)
      ((_x28 [@exists]) : ilist)
      ((_x68 [@exists]) : ilist)
     ->
       s > 0
       && (s_6 >= 0 && s_6 < s
          && s_6 == s - 1
          && len _x28 s_6
          && all_equal _x28 x true
          && _25 == _x28)
       && is_cons _x68 && head _x68 == x && tail _x68 == _25 && v == _x68
     : [%v: ilist])
     [@under])
