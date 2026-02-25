let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  ((* Current missing coverage*)
    (not (is_nil v))
    && (not (s == 0))
    && (len v s)
    && (uniq v true)

    (* Path 1: negate x_6 = true case *)
    && not (
      (fun ((x_6 [@exists]) : bool) ->
        (x_6) &&
        ((x_6) #==> (s == 0)) &&
        ((s == 0) #==> (x_6)) &&
        ((not (x_6) #==> (s > 0)) && ((s > 0) #==> (not (x_6))))))

    (* Path 2: negate x_6 = false case with prior element (x_9 = true) *)
    && not (
      (fun ((x_6 [@exists]) : bool) ->
        (not (x_6)) &&
        ((x_6) #==> (s == 0)) &&
        ((s == 0) #==> (x_6)) &&
        ((not (x_6) #==> (s > 0)) && ((s > 0) #==> (not (x_6)))) &&
        (fun ((s_15 [@exists]) : int) ->
          (s_15 >= 0) &&
          (s_15 < s) &&
          (s_15 == (s - 1)) &&
          (fun ((l [@exists]) : ilist) ->
            (len l s_15) &&
            (uniq l true) &&
            (fun ((x [@exists]) : int) ->
              (fun ((x_9 [@exists]) : bool) ->
                (mem l x x_9) &&
                (x_9)))))))

    (* Path 3: negate x_6 = false case with next element (x_9 = false) *)
    && not (
      (fun ((x_6_b [@exists]) : bool) ->
        (not (x_6_b)) &&
        ((x_6_b) #==> (s == 0)) &&
        ((s == 0) #==> (x_6_b)) &&
        ((not (x_6_b) #==> (s > 0)) && ((s > 0) #==> (not (x_6_b)))) &&
        (fun ((s_17 [@exists]) : int) ->
          (s_17 >= 0) &&
          (s_17 < s) &&
          (s_17 == (s - 1)) &&
          (fun ((l_b [@exists]) : ilist) ->
            (len l_b s_17) &&
            (uniq l_b true) &&
            (fun ((x_b [@exists]) : int) ->
              (fun ((x_9_b [@exists]) : bool) ->
                (mem l_b x_b x_9_b) &&
                (not (x_9_b))))))))

    : [%v: ilist])
    [@under]

let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x_6 [@exists]) : bool) ->
    (* Inferred body *)
   (iff (x_6) (s == 0))
    && (iff (not (x_6))  (s > 0))
    && (x_6)
    && (is_nil v)
    : [%v: ilist])
    [@under]
