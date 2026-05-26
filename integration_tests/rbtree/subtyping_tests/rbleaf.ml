let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  ((h == 0
   && ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
   && ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true))))
   && clr)
   && num_black v h true && no_red_red v true
   &&
   if clr then (is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true)))
   else (h == 0) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
    : [%v: irbtree])
    [@under]

let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h == 0 && clr && is_rbtleaf v
   &&
   if clr then (is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true)))
   else (h == 0) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
    : [%v: irbtree])
    [@under]
