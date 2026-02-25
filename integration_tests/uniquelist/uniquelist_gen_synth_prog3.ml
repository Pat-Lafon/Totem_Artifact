let rec unique_list_gen (s : int) : ilist =
  if sizecheck s then Err
  else
    let (l : ilist) = unique_list_gen (subs s) in
    let (x : int) = int_gen () in
    if list_mem l x then Err else Err

let[@assert] unique_list_gen =
  let s = (v >= 0 : [%v: int]) [@over] in
  (len v s && uniq v true : [%v: ilist]) [@under]
