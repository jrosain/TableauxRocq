(* Module interfacing usual string to Rocq strings *)
module RocqStr : sig
  type t = char list

  val from_string : string -> t
  val to_string : t -> string
end
