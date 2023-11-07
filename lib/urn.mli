open Extensions

module type WeightType =
  sig
    type t
    val compare : t -> t -> int
    val zero : t
    val add : t -> t -> t
    val sub : t -> t -> t
    val sample : t -> t
  end

module IntWeight : WeightType with type t = int
module FloatWeight : WeightType with type t = float

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

module Make(Weight : WeightType) : U with type weight = Weight.t
