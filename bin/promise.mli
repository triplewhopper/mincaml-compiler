type 'a state = Pending | Resolved of 'a(*| Rejected of exn *)
type 'a t
type 'a resolver

val pp: (Format.formatter -> 'a -> unit) -> Format.formatter  -> 'a t -> unit
val make : unit -> 'a t * 'a resolver
val return : 'a -> 'a t
val state : 'a t -> 'a state
val resolve : 'a resolver -> 'a -> unit
(* val reject : 'a resolver -> exn -> unit *)
