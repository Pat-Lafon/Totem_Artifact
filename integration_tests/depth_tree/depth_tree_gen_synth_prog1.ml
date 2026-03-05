let rec depth_tree_gen (s : int) : itree =
  if sizecheck s then Err
  else if bool_gen () then Leaf
  else
    let (ss : int) = subs s in
    let (lt : itree) = depth_tree_gen ss in
    let (rt : itree) = depth_tree_gen ss in
    let (n : int) = int_gen () in
    Node (n, lt, rt)

let[@assert] depth_tree_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((u [@exists]) : int) -> depth v u && u <= s : [%v: itree]) [@under]
