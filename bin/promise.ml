type 'a state = Pending | Resolved of 'a [@@deriving show]
type 'a promise = 'a state ref

let pp_promise poly_a fmt p = pp_state poly_a fmt !p
type 'a resolver = 'a promise
type 'a t = 'a promise [@@deriving show]

(** [write_once p s] changes the state of [p] to be [s]. If [p] and
  [s] are both pending, that has no effect. Raises: [Invalid_arg] if
  the state of [p] is not pending. *)
let write_once p s =
  if !p = Pending then p := s else invalid_arg "cannot write twice"

let make () =
  let p = ref Pending in
  (p, p)

let return x = ref (Resolved x)
let state p = !p
let resolve r x = write_once r (Resolved x)

(* let reject r x = write_once r (Rejected x) *)
