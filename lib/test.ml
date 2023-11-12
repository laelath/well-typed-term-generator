open Extensions

module type GenType = sig
  type (!+'exp, !+'ty) exp
  type (!+'exp, !+'ty) ctx
  type !+'ty ty

  val exp_map : 'exp1 'exp2 'ty1 'ty2.
    ('exp1 -> 'exp2) -> ('ty1 -> 'ty2) ->
    ('exp1, 'ty1) exp -> ('exp2, 'ty2) exp

  val ctx_map : 'exp1 'exp2 'ty1 'ty2 'a.
    ('exp1 -> 'exp2) -> ('ty1 -> 'ty2) ->
    ('exp1, 'ty1) ctx -> ('exp2, 'ty2) ctx

  val ctx_plug : 'exp 'ty.
    ('exp, 'ty) ctx -> 'exp ->
    ('exp, 'ty) exp

  val exp_unplug : 'exp 'ty.
    ('exp, 'ty) exp -> ('exp * ('exp, 'ty) ctx) list

  val ty_fold : 'ty 'a.
    ('ty -> 'a -> 'a) -> 'ty ty -> 'a -> 'a

  val ty_eq : 'ty 'a.
    ('ty -> 'ty -> 'a -> 'a option) ->
    'ty ty -> 'ty ty -> 'a option
end

module Make(G : GenType) = struct

  type 'a mlist_node =
    | Mt | Elem of { value: 'a; mutable next: 'a mlist_node }
  type 'a mlist = 'a mlist_node ref

  let mcons x ml = ref (Elem {value = x; next = !ml})

  (* helper function *)
  let exp_map_exp f = G.exp_map f Fun.id
  let ctx_map_exp f = G.ctx_map f Fun.id

  type exp_node =
    | Cut
    | E of (ctx, ty) G.exp
    | LP of linkvar * ctx
    | LN of linkvar * ctx
  and exp = {mutable exp_node: exp_node; mutable ctx: ctx}
  and ctx_node =
    | CCut
    | Top
    | C of (ctx, ty) G.ctx * exp
    | CLP of linkvar * exp
    | CLN of linkvar * exp
  and ctx = {mutable ctx_node: ctx_node; mutable hole: exp}
  and ty_node =
    | Unif of ty
    | T of ty G.ty
    | L of linkvar
  and ty = ty_node UnionFind.elem
  and linkvar = {
    mutable link_ty : ty G.ty;
    mutable link_ends_pos : exp list;
    mutable link_ends_neg : exp list;
  }

  (* exp.ctx contains the expressions context *)
  (* exp fields of ctx_node contain the /implementing/ expression *)
  (* ctx.hole contains the exp of the ctx's hole *)
  (* exp.ctx.hole should be a cycle *)
  (* ctx.hole.ctx should be a cycle *)

  let make_exp e_node c_node =
    let ctx = {ctx_node=c_node; hole=Obj.magic ()} in
    let e = {exp_node=e_node; ctx=ctx} in
    ctx.hole <- e;
    e

  let link_add_pos lvar e =
    assert (match e.exp_node with | LP _ -> true | _ -> false);
    lvar.link_ends_pos <- e :: lvar.link_ends_pos

  let link_add_neg lvar e =
    assert (match e.exp_node with | LN _ -> true | _ -> false);
    lvar.link_ends_neg <- e :: lvar.link_ends_neg

  type exp_cutting =
    | Boundary of exp
    | CutE of (exp_cutting, ty) G.exp
    | CutLP of linkvar * exp_cutting
    | CutLN of linkvar * exp_cutting

  let cut (e : exp) =
    match e.exp_node with
    | Cut -> None | LP (_, _) | LN (_, _) -> None
    | E e_g ->
      e.exp_node <- Cut;
      Some (exp_map_exp (fun ctx -> ctx.ctx_node <- CCut; ctx.hole) e_g)

  (* returns and ctx with ec as its hole and ctx_node = CCut *)
  let rec build ec =
    match ec with
    | Boundary e ->
      if e.ctx.ctx_node <> CCut
      then failwith "duplicated expression at boundary"
      else e.ctx
    | CutE ec_g ->
      let e_g = exp_map_exp build ec_g in
      let e = make_exp (E e_g) CCut in
      let children = G.exp_unplug e_g in
      List.iter (fun (child, ctx) -> child.ctx_node <- C (ctx, e)) children;
      e.ctx
    | CutLP (lvar, ec') ->
      let ctx = build ec' in
      let e = make_exp (LP (lvar, ctx)) CCut in
      ctx.ctx_node <- CLP (lvar, e);
      link_add_pos lvar e;
      e.ctx
    | CutLN (lvar, ec') ->
      let ctx = build ec' in
      let e = make_exp (LN (lvar, ctx)) CCut in
      ctx.ctx_node <- CLN (lvar, e);
      link_add_neg lvar e;
      e.ctx

  (* potentially discards the context's hole exp *)
  let paste ctx ec =
    assert (ctx.hole.exp_node = Cut);
    match ec with
    | Boundary e ->
      (* discards e's ctx and ctx's hole *)
      assert (e.ctx.ctx_node = CCut);
      e.ctx <- ctx;
      ctx.hole <- e
    | CutE ec_g ->
      let e_g = exp_map_exp build ec_g in
      ctx.hole.exp_node <- E e_g;
      let children = G.exp_unplug e_g in
      List.iter (fun (child, ctx_g) -> child.ctx_node <- C (ctx_g, ctx.hole))
                children
    | CutLP (lvar, ec') ->
      let ctx' = build ec' in
      ctx.hole.exp_node <- LP (lvar, ctx');
      ctx'.ctx_node <- CLP (lvar, ctx.hole);
      link_add_pos lvar ctx.hole
    | CutLN (lvar, ec') ->
      let ctx' = build ec' in
      ctx.hole.exp_node <- LN (lvar, ctx');
      ctx'.ctx_node <- CLN (lvar, ctx.hole);
      link_add_neg lvar ctx.hole



  type ctx_cutting =
    | CBoundary of ctx
    | CutC of (exp_cutting, ty) G.ctx * ctx_cutting
    | CutCLP of linkvar * ctx_cutting
    | CutCLN of linkvar * ctx_cutting

  let ctx_cut ctx =
    match ctx.ctx_node with
    | CCut | CLP _ | CLN _ -> None
    | Top -> None
    | C (ctx_g, e) ->
      ctx.ctx_node <- CCut;
      e.exp_node <- Cut;
      let ctx_g' =
        ctx_map_exp (fun ctx -> ctx.ctx_node <- CCut; ctx.hole) ctx_g in
      Some (e.ctx, ctx_g')

  (* returns an exp with cc as its context with exp_node = Cut *)
  let rec ctx_build cc =
    match cc with
    | CBoundary ctx ->
      if ctx.hole.exp_node <> Cut
      then failwith "duplicated context at boundary (how?)"
      else ctx.hole
    | CutC (ec_ctx_g, cc') ->
      let e = ctx_build cc' in
      let ctx_g = ctx_map_exp build ec_ctx_g in
      let e' = make_exp Cut CCut in
      let e_g = G.ctx_plug ctx_g e'.ctx in
      e.exp_node <- E e_g;
      let children = G.exp_unplug e_g in
      (* update of the children should include e' *)
      List.iter (fun (child, c_ctx_g) -> child.ctx_node <- C (c_ctx_g, e))
                children;
      e'
    | CutCLP (lvar, cc') ->
      let e = ctx_build cc' in
      let e' = make_exp Cut (CLP (lvar, e)) in
      e.exp_node <- LP (lvar, e'.ctx);
      link_add_pos lvar e;
      e'
    | CutCLN (lvar, cc') ->
      let e = ctx_build cc' in
      let e' = make_exp Cut (CLN (lvar, e)) in
      e.exp_node <- LN (lvar, e'.ctx);
      link_add_neg lvar e;
      e'

  (* potentially discards e's ctx *)
  let ctx_paste e cc =
    assert (e.ctx.ctx_node = CCut);
    match cc with
    (* discards e's ctx and ctx's hole *)
    | CBoundary ctx ->
      assert (ctx.hole.exp_node = Cut);
      ctx.hole <- e;
      e.ctx <- ctx
    | CutC (ec_ctx_g, cc') ->
      let e' = ctx_build cc' in
      let ctx_g = ctx_map_exp build ec_ctx_g in
      let e_g = G.ctx_plug ctx_g e.ctx in
      e'.exp_node <- E e_g;
      let children = G.exp_unplug e_g in
      List.iter (fun (child, c_ctx_g) -> child.ctx_node <- C (c_ctx_g, e'))
                children
    | CutCLP (lvar, cc') ->
      let e' = ctx_build cc' in
      e.ctx.ctx_node <- CLP (lvar, e');
      e'.exp_node <- LP (lvar, e.ctx);
      link_add_pos lvar e'
    | CutCLN (lvar, cc') ->
      let e' = ctx_build cc' in
      e.ctx.ctx_node <- CLN (lvar, e');
      e'.exp_node <- LN (lvar, e.ctx);
      link_add_neg lvar e'



  (* public functions for creating subexpressions *)
  let make_cut_exp e = CutE e
  let make_cut_link_pos lvar ec = CutLP (lvar, ec)
  let make_cut_link_neg lvar ec = CutLN (lvar, ec)



  let make_ty : ty_node -> ty = UnionFind.make
  let make_unif () =
    (* The Obj.magical recursive knot *)
    let ty = make_ty (Unif (UnionFind.make (Obj.magic ()))) in
    UnionFind.set ty (Unif ty);
    ty

  let make_linkvar ty = {
      link_ty = ty;
      link_ends_pos = [];
      link_ends_neg = [];
    }

  let close_link lvar =
    List.iter (fun e ->
                 match e.exp_node with
                 | LP (lvar', ctx_lp) when (lvar == lvar') ->
                   ctx_lp.hole.ctx <- e.ctx;
                   e.ctx.hole <- ctx_lp.hole
                 | _ -> failwith "linkvar bad link")
              lvar.link_ends_pos;
    List.iter (fun e ->
                 match e.exp_node with
                 | LN (lvar', ctx_ln) when (lvar == lvar') ->
                   ctx_ln.hole.ctx <- e.ctx;
                   e.ctx.hole <- ctx_ln.hole
                 | _ -> failwith "linkvar bad link")
              lvar.link_ends_neg

  (* f is an action that should change the links type to ty_g *)
  (* cuts each LP/LN out, actions can capture the link to reuse it *)
  (* f_pos can't access the ctx by way of types/can't reach a ctx
     through publicly viewable functions *)
  (* f_neg needs to be blocked from looking downwards *)
  (* TODO: how to deal with conflicts when inspecting upwards *)
  let modify_link lvar ty_g f_pos f_neg =
    lvar.link_ty <- ty_g;
    let pos_ends = lvar.link_ends_pos in
    let neg_ends = lvar.link_ends_neg in
    lvar.link_ends_pos <- [];
    lvar.link_ends_neg <- [];
    List.iter (fun e ->
                 match e.exp_node with
                 | LP (lvar', ctx_lp) when (lvar == lvar') ->
                   e.exp_node <- Cut;
                   ctx_lp.ctx_node <- CCut;
                   let ec = f_pos ctx_lp.hole in
                   paste e.ctx ec;
                 | _ -> failwith "linkvar bad link")
              pos_ends;
    List.iter (fun e ->
                 match e.exp_node with
                 | LN (lvar', ctx_ln) when (lvar == lvar') ->
                   e.exp_node <- Cut;
                   ctx_ln.ctx_node <- CCut;
                   let cc = f_neg e.ctx in
                   ctx_paste ctx_ln.hole cc;
                   e.exp_node <- LN (lvar, ctx_ln)
                 | _ -> failwith "linkvar bad link")
              neg_ends

  (* TODO: does extra computation after finding one, could ask the interface to
           provide a short-circuiting option fold *)
  let rec ty_contains_linkvar lvar ty =
    let f ty = 
      G.ty_fold (fun ty' b -> b || ty_contains_linkvar lvar ty')
                ty false in
    match UnionFind.get ty with
    | Unif _ -> false
    | T ty_g -> f ty_g
    | L lvar' -> lvar == lvar' || f lvar.link_ty


  exception UnificationError

  let rec unify ty1_0 ty2_0 =

    (* returns true if ty_node contains ty' *)
    let rec contains_ty ty' ty_n =
      let f ty_g =
        G.ty_fold (fun ty'' b -> b || ty' == ty'' ||
                     contains_ty ty' (UnionFind.get ty''))
                  ty_g false in
      match ty_n with
      | Unif _ -> false
      | T ty_g -> f ty_g
      | L lvar -> f lvar.link_ty in

  let unify_node ty_n1 ty_n2 =
    match ty_n1, ty_n2 with
    | Unif ty, ty_n | ty_n, Unif ty ->
      if contains_ty ty ty_n
      then raise UnificationError
      else ty_n
    | T ty_g1, T ty_g2 ->
      begin
        match (G.ty_eq (fun ty1 ty2 () -> Some (unify ty1 ty2))
                       ty_g1 ty_g2) with
        | Some () -> ty_n1
        | None -> raise UnificationError
      end
    | L lvar1, L lvar2 ->
      if lvar1 != lvar2
      then raise UnificationError
      else ty_n1
    | _, _ -> raise UnificationError in

  ignore (UnionFind.merge unify_node ty1_0 ty2_0)

  (* feels kinda wasteful that the mapping is just thrown away,
     but I suspect that the benefits of fully unifying the types
     might outweigh it? *)
  (* TODO: could merge unification variable free types here
           for faster repeat checking, kinda hacky though *)
  let can_unify ty1_0 ty2_0 =

    let lookup ty mp0 =
      let ty_rep = UnionFind.find ty in
      let rec lp mp =
        match mp with
        | [] -> None
        | (ty_rep', ty') :: mp' ->
          if ty_rep == ty_rep'
          then Some (ty', mp')
          else lp mp' in
      lp mp0 in

    let mp_add ty ty' mp = (UnionFind.find ty, ty') :: mp in

    (* returns true if ty_node contains ty' with substitution mp*)
    let rec contains_ty mp ty' ty_n =
      let f ty_g =
        G.ty_fold (fun ty'' b -> b || ty' == ty'' ||
                     contains_ty mp ty' (UnionFind.get ty''))
                  ty_g false in
      match ty_n with
      | T ty_g -> f ty_g
      | L lvar -> f lvar.link_ty
      | Unif ty ->
        match lookup ty mp with
        | None -> false
        | Some (ty'', mp') ->
          ty' == ty'' || contains_ty mp' ty' (UnionFind.get ty'') in

    let rec lp mp ty1 ty2 =
      if UnionFind.eq ty1 ty2 then Some mp else
      match UnionFind.get ty1, UnionFind.get ty2 with
      | Unif _, ty_n2 ->
        begin
          match lookup ty1 mp with
          | Some (ty1', _) -> lp mp ty1' ty2
          | None ->
            if contains_ty mp ty1 ty_n2
            then None
            else Some (mp_add ty1 ty2 mp)
        end
      | ty_n1, Unif _ ->
        begin
          match lookup ty2 mp with
          | Some (ty2', _) -> lp mp ty2' ty1
          | None ->
            if contains_ty mp ty2 ty_n1
            then None
            else Some (mp_add ty2 ty1 mp)
        end
      | L lvar1, L lvar2 ->
        if lvar1 != lvar2
        then raise UnificationError
        else Some mp
      | T ty_g1, T ty_g2 ->
        G.ty_eq (fun ty1 ty2 mp' -> lp mp' ty1 ty2) ty_g1 ty_g2
      | _, _ -> None in

    match lp [] ty1_0 ty2_0 with
    | None -> false
    | Some _ -> true

end


type 'ty var = (string * 'ty)

type ('exp, 'ty) exp =
  | Hole of 'ty
  | Ref of 'ty var
  | ExtRef of string * 'ty
  | Lambda of 'ty var list * 'exp
  | Call of 'exp * 'exp list

let exp_map fe ft exp =
  match exp with
  | Ref (x, ty) -> Ref (x, ft ty)
  | Hole ty -> Hole (ft ty)
  | ExtRef (x, ty) -> ExtRef (x, (ft ty))
  | Lambda (xs, e) ->
    Lambda (List.map (fun (x, ty) -> (x, ft ty)) xs, fe e)
  | Call (ef, es) -> Call (fe ef, List.map fe es)

type ('exp, 'ty) ctx =
  | CtxLambda of 'ty var list
  | CtxCallF of 'exp list
  | CtxCallArg of 'exp * 'exp list * 'exp list

let ctx_map fe ft ctx =
  match ctx with
  | CtxLambda xs -> CtxLambda (List.map (fun (x, ty) -> (x, ft ty)) xs)
  | CtxCallF es -> CtxCallF (List.map fe es)
  | CtxCallArg (ef, es1, es2) ->
    CtxCallArg (fe ef, List.map fe es1, List.map fe es2)

let ctx_plug c e =
  match c with
  | CtxLambda xs -> Lambda (xs, e)
  | CtxCallF es -> Call (e, es)
  | CtxCallArg (ef, es1, es2) ->
    Call (ef, List.fold_left (Fun.flip List.cons) (e :: es2) es1)

let exp_unplug e =
  match e with
  | Hole _ | Ref _ | ExtRef _ -> []
  | Lambda (xs, e_body) -> [(e_body, CtxLambda xs)]
  | Call (e_f, e_args) ->
    (e_f, CtxCallF e_args) ::
    (List.zippers e_args |>
     List.map (fun (es1, e, es2) -> (e, CtxCallArg (e_f, es1, es2))))

type 'ty ty =
  | TyInt
  | TyBool
  | TyList of 'ty
  | TyFun of 'ty list * 'ty

let ty_fold f ty a =
  match ty with
  | TyInt | TyBool -> a
  | TyList ty' -> f ty' a
  | TyFun (ty_args, ty_body) ->
    List.fold_left (Fun.flip f) a ty_args |> f ty_body

let ty_eq f ty1 ty2 a =
  match ty1, ty2 with
  | TyInt, TyInt | TyBool, TyBool -> Some a
  | TyList ty1', TyList ty2' ->
    f ty1' ty2' a
  | TyFun (ty_args1, ty_body1), TyFun (ty_args2, ty_body2) ->
    let g a t1 t2 = f t1 t2 a in
    if List.length ty_args1 <> List.length ty_args2 then None else
    List.fold_left_opt2 g a ty_args1 ty_args2
    |> Option.fold ~none:None ~some:(f ty_body1 ty_body2)
  | _, _ -> None

(* type checking has to be written in a module that has access creating
   expression manipulator types *)

