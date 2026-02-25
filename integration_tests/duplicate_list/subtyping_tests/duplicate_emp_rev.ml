let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((is_nil v && len v s && all_equal v x true
    : [%v: ilist])
    [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((is_nil v : [%v: ilist]) [@under])
