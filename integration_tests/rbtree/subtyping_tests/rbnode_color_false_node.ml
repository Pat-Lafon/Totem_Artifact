let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  ((fun ((x_0 [@exists]) : bool) ((c [@exists]) : bool) ((h_0 [@exists]) : int)
        ((lt4 [@exists]) : irbtree) ((rt4 [@exists]) : irbtree)
        ((inv_1 [@exists]) : int) ((inv_2 [@exists]) : int)
        ((h_1 [@exists]) : int) ((x_13 [@exists]) : int)
        ((x_24 [@exists]) : int) ->
     h > 0 && (not clr) && (not c)
     && inv - 2 >= 0
     && inv - 2 < inv
     && h - 1 >= 0
     && h - 1 + (h - 1) + 1 == inv - 2
     && num_black lt4 (h - 1) true
     && no_red_red lt4 true
     && ((h - 1 == 0) #==> ((is_rbtleaf lt4) || ((is_rbtnode lt4) && (not ((color lt4) == false)))))
     && inv - 2 >= 0
     && inv - 2 < inv
     && h - 1 >= 0
     && h - 1 + (h - 1) + 1 == inv - 2
     && num_black rt4 (h - 1) true
     && no_red_red rt4 true
     && ((h - 1 == 0) #==> ((is_rbtleaf rt4) || ((is_rbtnode rt4) && (not ((color rt4) == false)))))
     && (is_rbtnode v) && ((color v) == false) && (value v) == x_24 && (left v) == lt4 && (right v) == rt4)
   || fun ((lt3 [@exists]) : irbtree) ((rt3 [@exists]) : irbtree)
     ((x_20 [@exists]) : int) ->
   h > 0 && (not clr)
   && inv - 1 >= 0
   && inv - 1 < inv
   && h >= 0
   && h + h == inv - 1
   && num_black lt3 h true && no_red_red lt3 true && num_black rt3 h true && no_red_red rt3 true
   && ((is_rbtleaf rt3) || ((is_rbtnode rt3) && (not ((color rt3) == true))))
   && ((is_rbtleaf lt3) || ((is_rbtnode lt3) && (not ((color lt3) == true))))
   && (value v) == x_20 && (left v) == lt3 && (right v) == rt3
   && ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
   && (is_rbtnode v) && ((color v) == true)
    : [%v: irbtree])
    [@under]

let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h > 0 && (not clr) && num_black v h true && no_red_red v true
   (*    && ((clr) #==> ((is_rbtleaf v) || (not ((color v) == true)))) *)
   && ((not clr) #==> ((h == 0) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))))
    : [%v: irbtree])
    [@under]
