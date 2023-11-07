(* an implementation of the Urn datatype described in
   Ode to a Random Urn *)
(* TODO: add a better reference *)

open Extensions
open AlmostPerfect

module type WeightType =
  sig
    type t
    val compare : t -> t -> int
    val zero : t
    val add : t -> t -> t
    val sub : t -> t -> t
    (* sample function should produce a value between
       0 inclusive and the provided value exclusive *)
    val sample : t -> t
  end

module IntWeight = struct
  include Int
  let sample = Random.int
end

module FloatWeight = struct
  include Float
  let sample = Random.float
end

(* sample, remove, update, update_opt, replace are effectful *)

module type U =
  sig
    type weight
    type !+'a t
    val singleton : weight -> 'a -> 'a t
    val of_list : (weight * 'a) list -> 'a t option
    val of_nonempty : (weight * 'a) nonempty -> 'a t
    val sample : 'a t -> 'a
    val remove : 'a t -> (weight * 'a) * 'a t option
    val add : weight -> 'a -> 'a t -> 'a t
    val add_seq : (weight * 'a) Seq.t -> 'a t -> 'a t
    val add_list : (weight * 'a) list -> 'a t -> 'a t
    val update :
      (weight -> 'a -> weight * 'a) -> 'a t ->
      (weight * 'a) * (weight * 'a) * 'a t
    val update_opt :
      (weight -> 'a -> (weight * 'a) option) -> 'a t ->
      (weight * 'a) * (weight * 'a) option * 'a t option
    val replace : weight -> 'a -> 'a t -> (weight * 'a) * 'a t
    val size : 'a t -> int
    val weight : 'a t -> weight
  end

module Make(Weight : WeightType) = struct

  type weight = Weight.t

  let (+) = Weight.add
  let (-) = Weight.sub

  type 'a wtree =
      WLeaf of {w: weight; a: 'a}
    | WNode of {w: weight; l: 'a wtree; r: 'a wtree}

  type 'a t = {size: int; tree: 'a wtree}

  let size urn = urn.size

  let weight_tree t =
    match t with
    | WLeaf {w; _} -> w
    | WNode {w; _} -> w

  let weight {tree; _} = weight_tree tree

  let singleton w a = {size=1; tree=WLeaf {w; a}}

  let sampler f urn = f urn (Weight.sample (weight urn))

  let sample_index {tree=tree0; _} i =
    let rec sample_tree tree i =
      match tree with
      | WLeaf {a; _} -> a
      | WNode {l; r; _} ->
         let wl = weight_tree l in
         if i < wl
         then sample_tree l i
         else sample_tree r (i - wl)
    in sample_tree tree0 i

  let sample urn = sampler sample_index urn

  let update_index upd {size; tree=tree0} i =
    let rec update_tree tree i =
      match tree with
      | WLeaf {w; a} ->
         let (w', a') = upd w a in
         ((w, a), (w', a'), WLeaf {w=w'; a=a'})
      | WNode {w; l; r} ->
         let wl = weight_tree l in
         if i < wl
         then let (old, nw, l') = update_tree l i in
              (old, nw, WNode {w=w - fst old + fst nw; l=l'; r})
         else let (old, nw, r') = update_tree r (i - wl) in
              (old, nw, WNode {w=w - fst old + fst nw; l; r=r'})
    in let (old, nw, tree') = update_tree tree0 i in
       (old, nw, {size; tree=tree'})

  let update upd urn = sampler (update_index upd) urn

  let replace_index w' a' {size; tree=tree0} i =
    let rec replace_tree tree i =
      match tree with
      | WLeaf {w; a} ->
         ((w, a), WLeaf {w=w'; a=a'})
      | WNode {w; l; r} ->
         let wl = weight_tree l in
         if i < wl
         then let (old, l') = replace_tree l i in
              (old, WNode {w=w - fst old + w'; l=l'; r})
         else let (old, r') = replace_tree r (i - wl) in
              (old, WNode {w=w - fst old + w'; l; r=r'})
    in let (old, tree') = replace_tree tree0 i in
       (old, {size; tree=tree'})

  let replace w' a' urn = sampler (replace_index w' a') urn

  let add w' a' {size; tree=tree0} =
    let[@tail_mod_cons] rec go path tree =
      match tree with
      | WLeaf {w; a} ->
         WNode {w=w+w'; l=WLeaf {w; a}; r=WLeaf {w=w'; a=a'}}
      | WNode {w; l; r} ->
         let path' = Int.shift_right path 1 in
         if Int.test_bit path 0
         then WNode {w=w+w'; l; r=go path' r}
         else WNode {w=w+w'; l=go path' l; r}
    in {size=Int.succ size; tree=go size tree0}

  let unadd {size; tree=tree0} =
    let rec go path tree =
      match tree with
      | WLeaf {w; a} -> ((w, a), Weight.zero, None)
      | WNode {w; l; r} ->
         let path' = Int.shift_right path 1 in
         if Int.test_bit path 0
         then let ((w', a'), lb, r_opt') = go path' r in
              ((w', a'), lb + weight_tree l,
               Some (match r_opt' with
                     | None -> l
                     | Some r' -> WNode {w=w-w'; l; r=r'}))
         else let ((w', a'), lb, l_opt') = go path' l in
              ((w', a'), lb,
               Some (match l_opt' with
                     | None -> r
                     | Some l' -> WNode {w=w-w'; l=l'; r}))
    in let ((w', a'), lb, tree_opt) = go (Int.pred size) tree0 in
       ((w', a'), lb,
        Option.map (fun tree -> {size=Int.pred size; tree}) tree_opt)

  let remove_index urn i = 
    let ((w', a'), lb, urn_opt') = unadd urn in
    match urn_opt' with
    | None -> ((w', a'), None)
    | Some urn' ->
       if i < lb
       then let (old, urn'') = replace_index w' a' urn' i in
            (old, Some urn'')
       else if i < lb + w'
       then ((w', a'), Some urn')
       else let (old, urn'') = replace_index w' a' urn' (i - w') in
            (old, Some urn'')

  let remove urn = sampler remove_index urn

  (* TODO: can this be done without removing from the tree when
           upd returns Some? *)
  let update_opt_index upd urn i =
    let ((w, a), urn_opt') = remove_index urn i in
    match upd w a with
    | None -> ((w, a), None, urn_opt')
    | Some (w', a') ->
       ((w, a), Some (w', a'),
        match urn_opt' with
        | None -> Some (singleton w' a')
        | Some urn' -> Some (add w' a' urn'))

  let update_opt upd urn = sampler (update_opt_index upd) urn

  let of_nonempty was =
    let size = NonEmpty.length was in
    {size;
     tree = almost_perfect
              (fun l r -> WNode {w=weight_tree l + weight_tree r; l; r})
              (fun (w, a) -> WLeaf {w; a})
              size
              was}

  let of_list was = Option.map of_nonempty (NonEmpty.of_list was)

  let add_list was urn =
    List.fold_left (fun acc (w, a) -> add w a acc) urn was

  let add_seq was urn =
    Seq.fold_left (fun acc (w, a) -> add w a acc) urn was

  (*let add_seq = Fun.flip (Seq.fold_left (Fun.flip (Fun.uncurry add)))*)

end
