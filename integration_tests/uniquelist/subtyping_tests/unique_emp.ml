let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (len v 0 && uniq v true : [%v: ilist]) [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (is_nil v : [%v: ilist]) [@under]
