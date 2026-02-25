let rec sizedlist_gen (s : int) : ilist = if sizecheck s then [] else Err

let[@assert] sizedlist_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((n [@exists]) : int) -> len v n && n <= s : [%v: ilist]) [@under]
