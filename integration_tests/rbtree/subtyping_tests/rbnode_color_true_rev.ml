let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h > 0 && clr
   && fun ((x_13 [@exists]) : int) ->
   inv - 1 >= 0
   && h - 1 >= 0
   && h - 1 + (h - 1) + 1 == inv - 1
   && fun ((lt2 [@exists]) : irbtree) ->
   no_red_red lt2 true
   && num_black lt2 (h - 1) true
   && ((h - 1 == 0) #==> ((is_rbtleaf lt2) || ((is_rbtnode lt2) && (not ((color lt2) == false)))))
   && inv - 1 < inv
   && h - 1 >= 0
   && h - 1 + (h - 1) + 1 == inv - 1
   && fun ((rt2 [@exists]) : irbtree) ->
   no_red_red rt2 true
   && num_black rt2 (h - 1) true
   && ((h - 1 == 0) #==> ((is_rbtleaf rt2) || ((is_rbtnode rt2) && (not ((color rt2) == false)))))
   && (is_rbtnode v) && ((color v) == false) && (value v) == x_13 && (left v) == lt2 && (right v) == rt2
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
  (h > 0 && clr && num_black v h true && no_red_red v true
   && ((clr) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true)))))
   &&
   if clr then (is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true)))
   else (h == 0) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
    : [%v: irbtree])
    [@under]
