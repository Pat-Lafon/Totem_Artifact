let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (fun ((x_0 [@exists]) : bool) ((c [@exists]) : bool) ((h_0 [@exists]) : int)
       ((lt2 [@exists]) : irbtree) ((lt3 [@exists]) : irbtree)
       ((rt2 [@exists]) : irbtree) ((rt3 [@exists]) : irbtree)
       ((inv_1 [@exists]) : int) ((inv_2 [@exists]) : int)
       ((inv_3 [@exists]) : int) ((inv_4 [@exists]) : int)
       ((h_1 [@exists]) : int) ((h_2 [@exists]) : int) ((h_3 [@exists]) : int)
       ((x_13 [@exists]) : int) ((x_20 [@exists]) : int) ->
     (* iff x_0 (h == 0)
        && iff (not x_0) *)
     h > 0
     (* x_0
         && ((clr && is_rbtleaf v)
            || (not clr) && fun ((x_1 [@exists]) : bool) ->
               (x_1 && is_rbtleaf v)
               || (not x_1) && fun ((x_2 [@exists]) : irbtree) ->
                  is_rbtleaf x_2
                  && fun ((x_3 [@exists]) : int) ((x_4 [@exists]) : irbtree)
                    ->
                  is_rbtleaf x_4 && (is_rbtnode v) && ((color v) == true) && (value v) == x_3
                  && (left v) == x_4 && (right v) == x_2)
        || (not x_0)
           && *)
     (* clr && inv_1 >= 0 && inv_1 < inv
         && inv_1 == inv - 1
         && h_0 >= 0
         && (false #==> (h_0 + h_0 == inv_1))
         && ((not false) #==> (h_0 + h_0 + 1 == inv_1))
         && h_0 == h - 1
         && num_black lt2 h_0 true && no_red_red lt2 true
         && false #==> ((is_rbtleaf lt2) || ((is_rbtnode lt2) && (not ((color lt2) == true))))
         && ((not false) #==> (h_0 == 0 => (is_rbtleaf lt2) || ((is_rbtnode lt2) && (not ((color lt2) == false)))))
         && inv_2 >= 0 && inv_2 < inv
         && inv_2 == inv - 1
         && h_1 >= 0
         && (false #==> (h_1 + h_1 == inv_2))
         && ((not false) #==> (h_1 + h_1 + 1 == inv_2))
         && h_1 == h - 1
         && num_black rt2 h_1 true && no_red_red rt2 true
         && (false #==> ((is_rbtleaf rt2) || ((is_rbtnode rt2) && (not ((color rt2) == true)))))
         && ((not false) #==> ((h_1 == 0) #==> ((is_rbtleaf rt2) || ((is_rbtnode rt2) && (not ((color rt2) == false))))))
         && (is_rbtnode v) && ((color v) == false) && (value v) == x_13 && (left v) == lt2
         && (right v) == rt2
        || *) && (not clr)
     && c && inv_3 >= 0 && inv_3 < inv
     && inv_3 == inv - 1
     && h_2 >= 0
     && (true #==> (h_2 + h_2 == inv_3))
     && ((not true) #==> (h_2 + h_2 + 1 == inv_3))
     && h_2 == h && num_black lt3 h_2 true && no_red_red lt3 true
     && (true #==> ((is_rbtleaf lt3) || ((is_rbtnode lt3) && (not ((color lt3) == true)))))
     && ((not true) #==> ((h_2 == 0) #==> ((is_rbtleaf lt3) || ((is_rbtnode lt3) && (not ((color lt3) == false))))))
     && inv_4 >= 0 && inv_4 < inv
     && inv_4 == inv - 1
     && h_3 >= 0
     && (true #==> (h_3 + h_3 == inv_4))
     && ((not true) #==> (h_3 + h_3 + 1 == inv_4))
     && h_3 == h && num_black rt3 h_3 true && no_red_red rt3 true
     && (true #==> ((is_rbtleaf rt3) || ((is_rbtnode rt3) && (not ((color rt3) == true)))))
     && ((not true) #==> ((h_3 == 0) #==> ((is_rbtleaf rt3) || ((is_rbtnode rt3) && (not ((color rt3) == false))))))
     && (is_rbtnode v) && ((color v) == true) && (value v) == x_20 && (left v) == lt3 && (right v) == rt3
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

   && (is_rbtnode v) && ((color v) == true)
   (*    && ((clr) #==> ((is_rbtleaf v) || (not ((color v) == true)))) *)
   && ((not clr) #==> ((h == 0) #==> ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))))
    : [%v: irbtree])
    [@under]
