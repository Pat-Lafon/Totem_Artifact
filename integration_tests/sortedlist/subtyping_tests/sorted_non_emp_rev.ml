let[@assert] rty1 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  (((not (is_nil v))
    && len v s
    && sorted v true (*    && fun (u : int) -> (head v == u) #==> (x <= u) *)
    && (not (is_nil v)) #==> (fun ((u [@exists]) : int) -> head v == u && x <= u)
     : [%v: ilist])
     [@under])

let[@assert] rty2 =
  let s = ((0 <= v : [%v: int]) [@over]) in
  let x = ((true : [%v: int]) [@over]) in
  ((fun ((y [@exists]) : int)
      ((s1 [@exists]) : int)
      ((l [@exists]) : ilist)
     ->
       s > 0 && x <= y && 0 <= s1 && s1 < s
       && s1 == s - 1
       && len l s1 && sorted l true && is_cons v && head v == y && tail v == l
       (*    && fun (u : int) -> (head l == u) #==> (y <= u) *)
       && (not (is_nil l)) #==> (fun ((u [@exists]) : int) -> head l == u && y <= u)
     : [%v: ilist])
     [@under])

(* let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  ((not (is_nil v))
   && len v s && sorted v
   && fun (u : int) -> (head v == u) #==> (x <= u)
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (fun ((y [@exists]) : int) ((s1 [@exists]) : int) ((l [@exists]) : int list) ->
     s > 0 && x <= y && 0 <= s1 && s1 < s
     && s1 == s - 1
     && len l s1 && sorted l && is_cons v && head v == y && tail v == l
     && (fun (u : int) -> (head l == u) #==> (y <= u))
    : [%v: int list])
    [@under]
 *)
