let rec rbtree_gen (inv : int) (clr : bool) (h : int) : irbtree =
  if sizecheck h then if clr then Err else Err else if clr then Err else Err

let[@assert] rbtree_gen =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (num_black v h true && no_red_red v true
   &&
   if clr then (is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true)))
   else (h == 0) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
    : [%v: irbtree])
    [@under]
