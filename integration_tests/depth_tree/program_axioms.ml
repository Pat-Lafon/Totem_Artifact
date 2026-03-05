let[@axiom] depth_geq_0 (t : itree) (n : int) = ((depth t n))#==>((n >= 0))
let[@axiom] depth_0 (t : itree) (res : int) = ((depth t res))#==>(((is_leaf t))#==>((0 == res)))
let[@axiom] depth_0_rev (t : itree) (res : int) = ((is_leaf t))#==>(((0 == res))#==>((depth t res)))
let[@axiom] depth_0_infer (t : itree) (res : int) = ((depth t res))#==>(((0 == res))#==>((is_leaf t)))
let[@axiom] depth_0_fwd_pattern (t : itree) (res : int) = ((is_leaf t))#==>(((depth t res))#==>((0 == res)))
let[@axiom] depth_1 (t : itree) (v : int) (l : itree) (r : itree) (res : int) = ((depth t res))#==>((((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(fun ((res_0 [@exists]) : int) -> (fun ((res_1 [@exists]) : int) -> ((depth l res_0) && (depth r res_1) && (res_0 > res_1)))#==>(((depth l res_0))#==>(((1 + res_0) == res)))))
let[@axiom] depth_1_rev (t : itree) (v : int) (l : itree) (r : itree) (res : int) = (((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(fun ((res_0 [@exists]) : int) -> (fun ((res_1 [@exists]) : int) -> ((depth l res_0) && (depth r res_1) && (res_0 > res_1)))#==>(((depth l res_0))#==>((((1 + res_0) == res))#==>((depth t res)))))
let[@axiom] depth_1_fwd_pattern (t : itree) (v : int) (l : itree) (r : itree) (res : int) = fun ((res_0 [@exists]) : int) -> (fun ((res_1 [@exists]) : int) -> ((depth l res_0) && (depth r res_1) && (res_0 > res_1)))#==>((((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(((depth t res))#==>(((depth l res_0) && ((1 + res_0) == res)))))
let[@axiom] depth_2 (t : itree) (v : int) (l : itree) (r : itree) (res : int) = ((depth t res))#==>((((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(fun ((res_0 [@exists]) : int) -> fun ((res_1 [@exists]) : int) -> ((((depth l res_0) && (depth r res_1) && (not ((res_0 > res_1)))) && (depth r res_1)))#==>(((1 + res_1) == res))))
let[@axiom] depth_2_rev (t : itree) (v : int) (l : itree) (r : itree) (res : int) = (((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(fun ((res_0 [@exists]) : int) -> fun ((res_1 [@exists]) : int) -> ((((depth l res_0) && (depth r res_1) && (not ((res_0 > res_1)))) && (depth r res_1)))#==>((((1 + res_1) == res))#==>((depth t res))))
let[@axiom] depth_2_fwd_pattern (t : itree) (v : int) (l : itree) (r : itree) (res : int) = fun ((res_0 [@exists]) : int) -> fun ((res_1 [@exists]) : int) -> (((depth l res_0) && (depth r res_1) && (not ((res_0 > res_1)))))#==>((((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(((depth t res))#==>(((depth r res_1) && ((1 + res_1) == res)))))

(**)

let[@axiom] depth_functional (t : itree) (res : int) (res2 : int) = (((depth t res) #==> ((depth t res2)#==>(res2 == res))))

let[@axiom] depth_1 (t : itree) (v : int) (l : itree) (r : itree) (res : int) = ((depth t res))#==>((((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(fun ((res_0 [@exists]) : int) -> fun ((res_1 [@exists]) : int) -> ((depth l res_0) && (depth r res_1) && (res_0 > res_1) #==> (((1 + res_0) == res)))))

let[@axiom] depth_1 (t : itree) (v : int) (l : itree) (r : itree) (res : int) = ((depth t res))#==>((((is_node t) && ((value t) == v) && ((left t) == l) && ((right t) == r)))#==>(fun ((res_0 [@exists]) : int) -> fun ((res_1 [@exists]) : int) -> ((depth l res_0) && (depth r res_1) && (not ((res_0 > res_1))) #==> (((1 + res_1) == res)))))

let[@axiom] depth_0_infer (t : itree) (res : int) = ((depth t res))#==>(((res > 0))#==>((is_node t)))