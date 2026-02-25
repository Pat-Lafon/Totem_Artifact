let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((n [@exists]) : int) -> len v n && n <= s && s == 0 && all_evens v true : [%v: ilist]) [@under]

let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (s == 0 && is_nil v : [%v: ilist]) [@under]
