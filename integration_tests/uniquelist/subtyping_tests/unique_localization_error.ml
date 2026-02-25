let[@assert] rty1 =
  let s = ((true : [%v: int]) [@over]) in
  ((s == 0 && is_nil v
     : [%v: ilist])
     [@under])

let[@assert] rty2 =
  let s = ((true : [%v: int]) [@over]) in
  ((not (is_nil v) && not (s == 0)
    && len v s && uniq v true
    && len (tail v) (s - 1) && uniq (tail v) true
    && not (fun ((s_15 [@exists]) : int)
                ((l [@exists]) : ilist)
                ((x [@exists]) : int)
                ((x_9 [@exists]) : bool) ->
              s_15 == s - 1 && s_15 >= 0
              && len l s_15 && uniq l true
              && mem l x x_9 && x_9)
    && not (fun ((s_17 [@exists]) : int)
                ((l [@exists]) : ilist)
                ((x [@exists]) : int)
                ((x_9 [@exists]) : bool) ->
              s_17 == s - 1 && s_17 >= 0
              && len l s_17 && uniq l true
              && mem l x x_9 && not x_9)
     : [%v: ilist])
     [@under])