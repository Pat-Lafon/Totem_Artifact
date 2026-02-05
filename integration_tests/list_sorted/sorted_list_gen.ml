let rec sorted_list_gen (s : int) (x : int) : ilist =
  if sizecheck s then []
  else
    let (y : int) = int_gen () in
    if x <= y then
      let (size2 : int) = subs s in
      let (l : ilist) = sorted_list_gen size2 y in
      let (l2 : ilist) = y :: l in
      l2
    else Exn

let[@assert] sorted_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((len v s && sorted v true && (not (is_nil v)) #==> (fun ((u [@exists]) : int) -> head v == u && x <= u)
    : [%v: ilist])
    [@under])
