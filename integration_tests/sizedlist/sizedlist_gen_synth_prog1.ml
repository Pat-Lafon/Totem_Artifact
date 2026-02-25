let rec sizedlist_gen (s : int) : ilist =
  if sizecheck s then Err
  else if bool_gen () then []
  else int_gen () :: sizedlist_gen (subs s)

let[@assert] sizedlist_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((n [@exists]) : int) -> len v n && n <= s : [%v: ilist]) [@under]
