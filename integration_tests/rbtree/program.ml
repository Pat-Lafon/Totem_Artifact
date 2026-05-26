type [@grind] irbtree = Rbtleaf | Rbtnode of { color : bool; left : irbtree; value : int; right : irbtree }

let [@simp] [@grind] rec num_black (t : irbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode { color = c; left = l; value = _; right = r } ->
      if not c then num_black l (h - 1) && num_black r (h - 1)
      else num_black l h && num_black r h

let [@simp] [@grind] rec no_red_red (t : irbtree) : bool =
  match t with
  | Rbtleaf -> true
  | Rbtnode { color = c; left = l; value = _; right = r } ->
      if not c then no_red_red l && no_red_red r
      else
        match l with
        | Rbtnode { color = c'; left = _; value = _; right = _ } ->
            (match r with
            | Rbtnode { color = c''; left = _; value = _; right = _ } ->
                (not c') && (not c'') && no_red_red l && no_red_red r
            | Rbtleaf -> (not c') && no_red_red l)
        | Rbtleaf ->
            (match r with
            | Rbtnode { color = c''; left = _; value = _; right = _ } -> (not c'') && no_red_red r
            | Rbtleaf -> true)
