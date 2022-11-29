(*
module DataTy = Key.Make (struct let x="d" end)

module DataCon = Key.Make (struct let x="c" end)

module DataTyVar = Key.Make (struct let x="a" end)


(* we need a couple maps

   datatype -> constructor list
   (list -> cons, nil)

   unify : datatype * type -> substitution
   'a list, int list -> 'a |-> int

   constructor * substitution -> type list
   (cons, 'a |-> int  -> int, int list
 *)


let list = DataTy.make()
let cons = DataCon.make()
let nil = DataCon.make()

let bool = DataTy.make()
let t = DataCon.make()
let f = DataCon.make()



type datatype_registry = {

    datatype : list DataTy.t;

    ty_to_constrs : DataTy.t -> DataCon.t list;

    (* second argument is the substitution *)
    unify_and_instantiate_constr : DataCon.t -> (Type.ty_label list) -> Type.ty_label list

  }

let unify_and_instantiate_constr_list dcon subst =
  if DataCon.same dcon cons
  then let a = List.nth subst 1 in
       [a, Type.TyNdData list a]
  else ...


let unify_and_instantiate_constr datacon subst =
  

let datatype_registry =
  let ty_to_constrs = DataTy.Tbl.create 100 in
  let constr_to_tys = DataCon.Tbl.create 100 in


  {
    ty_to_constrs=DataTy.Tbl.find ty_to_constrs;

    unify=unify;

    instantiate_constr=instantiate_constr
  }


 *)
