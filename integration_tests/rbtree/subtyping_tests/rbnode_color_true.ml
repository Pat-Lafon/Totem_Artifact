let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (h > 0 && clr
   && fun ((inv_1 [@exists]) : int) ->
   inv_1 >= 0 && inv_1 < inv
   && inv_1 == inv - 1
   && fun ((h_0 [@exists]) : int) ->
   h_0 >= 0
   && h_0 + h_0 + 1 == inv_1
   && h_0 == h - 1
   && fun ((lt2 [@exists]) : irbtree) ->
   num_black lt2 h_0 true && no_red_red lt2 true
   && ((h_0 == 0) #==> ((is_rbtleaf lt2) || ((is_rbtnode lt2) && (not ((color lt2) == false)))))
   && fun ((inv_2 [@exists]) : int) ->
   inv_2 >= 0 && inv_2 < inv
   && inv_2 == inv - 1
   && fun ((h_1 [@exists]) : int) ->
   h_1 >= 0
   && h_1 + h_1 + 1 == inv_2
   && h_1 == h - 1
   && fun ((rt2 [@exists]) : irbtree) ->
   num_black rt2 h_1 true && no_red_red rt2 true
   && ((h_1 == 0) #==> ((is_rbtleaf rt2) || ((is_rbtnode rt2) && (not ((color rt2) == false)))))
   && fun ((x_13 [@exists]) : int) ->
   (is_rbtnode v) && ((color v) == false) && (value v) == x_13 && (left v) == lt2 && (right v) == rt2
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
  (h > 0 && clr && num_black v h true && no_red_red v true
   && ((clr) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == true)))))
    : [%v: irbtree])
    [@under]
