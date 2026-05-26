let rec rbtree_gen (inv : int) (clr : bool) (h : int) : irbtree =
  if sizecheck h then
    if clr then Rbtleaf
    else if bool_gen () then Rbtleaf
    else Rbtnode (true, Rbtleaf, int_gen (), Rbtleaf)
  else if clr then Err
  else
    let (c : bool) = bool_gen () in
    if c then
      let (lt3 : irbtree) = rbtree_gen (subs inv) true h in
      let (rt3 : irbtree) = rbtree_gen (subs inv) true h in
      Rbtnode (true, lt3, int_gen (), rt3)
    else
      let (lt4 : irbtree) = rbtree_gen (subs (subs inv)) false (subs h) in
      let (rt4 : irbtree) = rbtree_gen (subs (subs inv)) false (subs h) in
      Rbtnode (false, lt4, int_gen (), rt4)

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
