let[@assert] rty1 =
  let s = (0 == v : [%v: int]) [@over] in
  (is_leaf v && depth v s : [%v: itree]) [@under]

let[@assert] rty2 =
  let s = (0 == v : [%v: int]) [@over] in
  (is_leaf v : [%v: itree]) [@under]
