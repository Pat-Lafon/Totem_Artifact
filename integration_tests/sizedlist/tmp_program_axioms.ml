let[@axiom] len_0 (l : ilist) (res : int) = ((len l res))#==>(((is_nil l))#==>((0 == res)))
let[@axiom] len_0_rev (l : ilist) (res : int) = ((is_nil l))#==>(iff ((0 == res)) ((len l res)))

let[@axiom] len_0_rev_rev_rev (l : ilist) (res : int) = (((len l res))) #==> (((0 == res)) #==> ((is_nil l)))

let[@axiom] len_1_rev_rev (l : ilist) (xs : ilist) (res : int) = (((is_cons l) && ((tail l) == xs)))#==>(iff ((len l res)) (fun ((res_0 [@exists]) : int) -> (((len xs res_0) && ((1 + res_0) == res)))))

let[@axiom] len_geq_0 (l : ilist) (n : int) = ((len l n))#==>((n >= 0))