let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((fun ((s1 [@exists]) : int) ((l [@exists]) : ilist) ->
      s > 0 && s1 >= 0 && s1 < s
      && s1 == s - 1
      && len l s1
      && all_equal l x true
      && is_cons v && head v == x && tail v == l
     : [%v: ilist])
     [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((s > 0
    && (not (is_nil v))
    && len v s
    && all_equal v x true
    : [%v: ilist])
    [@under])
