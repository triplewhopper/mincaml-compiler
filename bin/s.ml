(** customized version of Set *)

module S =
  Set.Make
    (struct
      type t = Id.t
      let compare = Id.compare
    end)
include S

let of_list l = List.fold_left (fun s e -> add e s) empty l
