let[@axiom] len_geq_0 (l : ilist) (n : int) = ((len l n))#==>((n >= 0))
let[@axiom] len_0 (l : ilist) (res : int) = ((len l res))#==>(((is_nil l))#==>((0 == res)))
let[@axiom] len_0_rev (l : ilist) (res : int) = ((is_nil l))#==>(((0 == res))#==>((len l res)))
let[@axiom] len_0_infer (l : ilist) (res : int) = ((len l res))#==>(((0 == res))#==>((is_nil l)))
let[@axiom] len_0_fwd_pattern (l : ilist) (res : int) = ((is_nil l))#==>(((len l res))#==>((0 == res)))
let[@axiom] len_1 (l : ilist) (xs : ilist) (res : int) = ((len l res))#==>((((is_cons l) && ((tail l) == xs)))#==>(fun ((res_0 [@exists]) : int) -> ((len xs res_0) && ((1 + res_0) == res))))
let[@axiom] len_1_rev (l : ilist) (xs : ilist) (res : int) = (((is_cons l) && ((tail l) == xs)))#==>((fun ((res_0 [@exists]) : int) -> ((len xs res_0) && ((1 + res_0) == res)))#==>((len l res)))
let[@axiom] len_1_fwd_pattern (l : ilist) (xs : ilist) (res : int) = (((is_cons l) && ((tail l) == xs)))#==>(((len l res))#==>(fun ((res_0 [@exists]) : int) -> ((len xs res_0) && ((1 + res_0) == res))))
let[@axiom] is_even_0 (x : int) (res : bool) = ((is_even x res))#==>(((x == 0))#==>((true == res)))
let[@axiom] is_even_0_rev (x : int) (res : bool) = ((x == 0))#==>(((true == res))#==>((is_even x res)))
let[@axiom] is_even_0_fwd_pattern (x : int) (res : bool) = ((x == 0))#==>(((is_even x res))#==>((true == res)))
let[@axiom] is_even_1 (x : int) (res : bool) = ((is_even x res))#==>(((not ((x == 0))))#==>(((x == 1))#==>((false == res))))
let[@axiom] is_even_1_rev (x : int) (res : bool) = ((not ((x == 0))))#==>(((x == 1))#==>(((false == res))#==>((is_even x res))))
let[@axiom] is_even_1_fwd_pattern (x : int) (res : bool) = ((x == 1))#==>(((not ((x == 0))))#==>(((is_even x res))#==>((false == res))))
let[@axiom] is_even_2 (x : int) (res : bool) = ((is_even x res))#==>(((not ((x == 0))))#==>(((not ((x == 1))))#==>(((x == (0 - 1)))#==>((false == res)))))
let[@axiom] is_even_2_rev (x : int) (res : bool) = ((not ((x == 0))))#==>(((not ((x == 1))))#==>(((x == (0 - 1)))#==>(((false == res))#==>((is_even x res)))))
let[@axiom] is_even_2_fwd_pattern (x : int) (res : bool) = ((x == (0 - 1)))#==>(((not ((x == 1))))#==>(((not ((x == 0))))#==>(((is_even x res))#==>((false == res)))))
let[@axiom] is_even_3 (x : int) (res : bool) = ((is_even x res))#==>(((not ((x == 0))))#==>(((not ((x == 1))))#==>(((not ((x == (0 - 1)))))#==>(((x > 1))#==>(fun ((res_1 [@exists]) : bool) -> ((is_even (x - 2) res_1) && (res_1 == res)))))))
let[@axiom] is_even_3_rev (x : int) (res : bool) = ((not ((x == 0))))#==>(((not ((x == 1))))#==>(((not ((x == (0 - 1)))))#==>(((x > 1))#==>((fun ((res_1 [@exists]) : bool) -> ((is_even (x - 2) res_1) && (res_1 == res)))#==>((is_even x res))))))
let[@axiom] is_even_3_fwd_pattern (x : int) (res : bool) = ((x > 1))#==>(((not ((x == (0 - 1)))))#==>(((not ((x == 1))))#==>(((not ((x == 0))))#==>(((is_even x res))#==>(fun ((res_1 [@exists]) : bool) -> ((is_even (x - 2) res_1) && (res_1 == res)))))))
let[@axiom] is_even_4 (x : int) (res : bool) = ((is_even x res))#==>(((not ((x == 0))))#==>(((not ((x == 1))))#==>(((not ((x == (0 - 1)))))#==>(((not ((x > 1))))#==>(fun ((res_2 [@exists]) : bool) -> ((is_even (x + 2) res_2) && (res_2 == res)))))))
let[@axiom] is_even_4_rev (x : int) (res : bool) = ((not ((x == 0))))#==>(((not ((x == 1))))#==>(((not ((x == (0 - 1)))))#==>(((not ((x > 1))))#==>((fun ((res_2 [@exists]) : bool) -> ((is_even (x + 2) res_2) && (res_2 == res)))#==>((is_even x res))))))
let[@axiom] is_even_4_fwd_pattern (x : int) (res : bool) = ((not ((x > 1))))#==>(((not ((x == (0 - 1)))))#==>(((not ((x == 1))))#==>(((not ((x == 0))))#==>(((is_even x res))#==>(fun ((res_2 [@exists]) : bool) -> ((is_even (x + 2) res_2) && (res_2 == res)))))))
let[@axiom] all_evens_0 (l : ilist) (res : bool) = ((all_evens l res))#==>(((is_nil l))#==>((true == res)))
let[@axiom] all_evens_0_rev (l : ilist) (res : bool) = ((is_nil l))#==>(((true == res))#==>((all_evens l res)))
let[@axiom] all_evens_0_fwd_pattern (l : ilist) (res : bool) = ((is_nil l))#==>(((all_evens l res))#==>((true == res)))
let[@axiom] all_evens_1 (l : ilist) (x : int) (xs : ilist) (res : bool) = ((all_evens l res))#==>((((is_cons l) && ((head l) == x) && ((tail l) == xs)))#==>(fun ((res_3 [@exists]) : bool) -> ((is_even x res_3))#==>(fun ((res_4 [@exists]) : bool) -> ((all_evens xs res_4) && (((res_3 && res_4) && res) || ((not ((res_3 && res_4))) && (not (res))))))))
(* let[@axiom] all_evens_1_rev (l : ilist) (x : int) (xs : ilist) (res : bool) = (((is_cons l) && ((head l) == x) && ((tail l) == xs)))#==>(fun ((res_3 [@exists]) : bool) -> ((fun ((res_4 [@exists]) : bool) -> (((is_even x res_3))&&(all_evens xs res_4) && (((res_3 && res_4) && res) || ((not ((res_3 && res_4))) && (not (res))))))#==>((all_evens l res)))) *)
let[@axiom] all_evens_1_fwd_pattern (l : ilist) (x : int) (xs : ilist) (res : bool) = (((is_cons l) && ((head l) == x) && ((tail l) == xs)))#==>(((all_evens l res))#==>(fun ((res_3 [@exists]) : bool) -> fun ((res_4 [@exists]) : bool) -> ((is_even x res_3) && (all_evens xs res_4) && (((res_3 && res_4) && res) || ((not ((res_3 && res_4))) && (not (res)))))))

let[@axiom] is_even_double (x : int) = (is_even (x*2) true)
let[@axiom] is_even_double (x : int) = (is_even (x*2 -1) false)

let[@axiom] is_even_det (x : int) (r1 : bool) (r2 : bool) =
  (is_even x r1 && is_even x r2) #==> (r1 == r2)

let[@axiom] all_evens_functional (l : ilist) (res : bool) (res2 : bool) = (all_evens l res) #==> ((all_evens l res2) #==> (res == res2))

let[@axiom] all_evens_or (l : ilist) (res[@exists]: bool) = ((all_evens l res))

let[@axiom] all_evens_1_rev (l : ilist) (x : int) (xs : ilist) (res : bool) (res_3 : bool) =
  (((is_cons l) && ((head l) == x) && ((tail l) == xs) && (is_even x res_3)))
  #==>
  ((fun ((res_4 [@exists]) : bool) ->
    ((all_evens xs res_4) &&
     (((res_3 && res_4) && res) || ((not ((res_3 && res_4))) && (not (res))))))
  #==> ((all_evens l res)))

let[@axiom] all_evens_1 (l : ilist) (x : int) (xs : ilist) (res : bool) = ((all_evens l true))#==>((((is_cons l) && ((head l) == x) && ((tail l) == xs)))#==>((is_even x true)&&(((all_evens xs true)))))