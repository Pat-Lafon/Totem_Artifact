let rec duplicate_list_gen (s : int) (x : int) : ilist =
  if sizecheck s then [] else Err

let[@assert] duplicate_list_gen =
  let s = (v >= 0 : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (len v s && all_equal v x true
    : [%v: ilist])
    [@under]
