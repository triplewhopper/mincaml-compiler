open KNormal

type dag_node = {
  name: Id.t;
  children: dag_node list[@printer fun fmt lst-> fprintf fmt "[%a]" (Id.pp_t_list ~pp_sep:", ") (List.map (fun n -> n.name) lst)];
  mutable synonyms: Id.t list;
  kn: KNormal.t[@printer pp_kn];
  dep_arr: Id.t list;
  mutable killed: bool;
}[@@deriving show]
let is_synonymous_with name dag = if dag.killed then false else Id.equal name dag.name || List.find_opt (Id.equal name) dag.synonyms |> Option.is_some
let is_synonymous_with_opt name dag = if is_synonymous_with name dag then Some dag else None
let mkDag ?(dep_arr=[]) kn name ~children_names dags = 
  match kn.value with
  | Let _ -> assert false | LetRec _ -> assert false | LetTuple _ -> assert false
  | _ -> ();
  let children = List.filter_map (fun name -> List.find_opt (is_synonymous_with name) dags) children_names in
  {name;children;synonyms=[];kn;dep_arr;killed=false}
let kill dags arr = List.iter (fun dag -> if List.find_opt (Id.equal arr) dag.dep_arr |> Option.is_some then dag.killed <- true) dags
let find_dep_arr dags arrs names = 
  List.concat_map (fun name -> 
    try let dag = List.find (fun dag -> (not dag.killed) && Id.equal name dag.name) dags in dag.dep_arr
    with Not_found -> if List.exists (Id.equal name) arrs then [name] else []) names
let predicate kn1 dag = 
  if dag.killed then false else
    let has_child name = List.find_opt (fun child -> 
      Id.equal name child.name || List.find_opt (Id.equal name) child.synonyms |> Option.is_some) dag.children |> Option.is_some in
    match kn1.value, dag.kn.value with
    | Neg(x1), Neg (x2) -> assert (List.length dag.children <= 1); Id.equal x1 x2 || has_child x1
    | Add(x1,y1), Add (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | Sub(x1,y1), Sub (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | FNeg(x1), FNeg (x2) -> assert (List.length dag.children <= 1); Id.equal x1 x2 || has_child x1
    | FAdd(x1,y1), FAdd (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | FSub(x1,y1), FSub (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | FMul(x1,y1), FMul (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | FDiv(x1,y1), FDiv (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | Get(x1,y1), Get (x2,y2) -> assert (List.length dag.children <= 2); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1)
    | Put(x1,y1,z1), Put (x2,y2,z2) -> assert (List.length dag.children <= 3); (Id.equal x1 x2 || has_child x1) && (Id.equal y1 y2 || has_child y1) && (Id.equal z1 z2 || has_child z1)
    | Tuple(xs1), Tuple(xs2) -> assert (List.length dag.children <= List.length xs2); List.for_all2 (fun x1 x2 -> Id.equal x1 x2 || has_child x1) xs1 xs2
    (* | ExtArray(x1), ExtArray (x2) -> assert (List.length dag.children <= 1); Id.equal x1 x2 || has_child x1 *)
    | ExtArray _, _ | _, ExtArray _ -> assert false 
    | Unit, _ | _, Unit -> assert false
    | Int _, _ | _, Int _ -> assert false
    | Float _, _ | _, Float _ -> assert false
    | IfEq _, _ | _, IfEq _ -> assert false
    | IfLE _, _ | _, IfLE _ -> assert false
    | Let _, _ | _, Let _ -> assert false
    | LetRec _, _ | _, LetRec _ -> assert false
    | LetTuple _, _ | _, LetTuple _ -> assert false
    | App _, _ | _, App _ -> assert false
    | ExtFunApp _, _ | _, ExtFunApp _ -> assert false
    | _, _ -> false


(** 共通部分式削除 *)
let rec f dags arrs kn = 
  let return value = if equal_exp value kn.value then kn else { kn with value;prev=PrevLeft(kn)} in
  let makeFather value p = { value; tokens=NList.empty; prev=Father p } in
  let try_substitute dags x t rhs e2 = 
    let prev = List.find (predicate rhs) dags in
    assert (not (Id.equal x prev.name));
    prev.synonyms <- x::prev.synonyms;
    let p, r = Promise.make () in
    let kn' = return (Let((x, t), makeFather (Var(prev.name)) p, f dags arrs e2)) in
    Promise.resolve r kn';
    Format.eprintf "Eliminating %a =@;<1 2>@[%a@]@;<1 0>with@;<1 4>@[%a@]@." Id.pp x KNormal.pp_kn rhs Id.pp prev.name;
    kn' in
  match kn.value with 
  | IfEq(x, y, e1, e2) -> IfEq(x, y, f [] arrs e1, f [] arrs e2) |> return
  | IfLE(x, y, e1, e2) -> IfLE(x, y, f [] arrs e1, f [] arrs e2) |> return
  | Let((x, t), ({value=Neg(y1)|FNeg(y1);_}as rhs), e2) ->
      (try try_substitute dags x t rhs e2
      with Not_found -> 
        let dep_arr = find_dep_arr dags arrs [y1] in
        Let((x, t), rhs, f ((mkDag rhs x ~dep_arr ~children_names:[y1] dags)::dags) arrs e2) |> return)

  | Let((x, t), ({value=Var(y1);_} as rhs), e2) ->
      (try try_substitute dags x t rhs e2 with Not_found -> 
        let dep_arr = find_dep_arr dags arrs [y1] in
        Let((x, t), rhs, f ((mkDag rhs x ~dep_arr ~children_names:[y1] dags)::dags) arrs e2) |> return)

  | Let((x, t), ({value=ExtArray(_);_} as rhs), e2) ->
      Let((x, t), rhs, f dags (x::arrs) e2) |> return

  | Let((x, t), ({value=Add(y1,y2)|Sub(y1,y2)|FAdd(y1,y2)|FSub(y1,y2)|FMul(y1,y2)|FDiv(y1,y2);_} as rhs), e2) -> (* letの場合 (caml2html: elim_let) *)
      (try try_substitute dags x t rhs e2 with Not_found -> 
        let dep_arr = find_dep_arr dags arrs [y1;y2] in
        Let((x, t), rhs, f ((mkDag rhs x ~dep_arr ~children_names:[y1;y2] dags)::dags) arrs e2) |> return)

  | Let((x, t), ({value=Tuple(ys);_} as rhs), e2) ->
      (try try_substitute dags x t rhs e2 with Not_found -> 
        let dep_arr = find_dep_arr dags arrs ys in
        Let((x, t), rhs, f ((mkDag rhs x ~dep_arr ~children_names:ys dags)::dags) arrs e2) |> return)

  | Let((x, t), ({value=(Get(y1, y2));_} as rhs), e2) -> (* letの場合 (caml2html: elim_let) *)
      (try try_substitute dags x t rhs e2 with Not_found -> 
        let dep_arr = find_dep_arr dags arrs [y1;y2] in
        if false then (
          Format.eprintf "dep_arr of %a = %a: [%a]@." Id.pp x pp_kn rhs (Id.pp_t_list ~pp_sep:", ") dep_arr;
          Format.eprintf "arrs: [%a]@." (Id.pp_t_list ~pp_sep:", ") arrs;
          Format.eprintf "dags: @[[";
          Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_text fmt ", ") 
          (fun fmt dag -> Format.fprintf fmt "%a" pp_dag_node dag) 
          Format.err_formatter dags;
          Format.eprintf "]@]@.";
        );
        let e2' = f ((mkDag rhs x ~dep_arr ~children_names:[y1;y2] dags)::dags) arrs e2 in Let((x, t), rhs, e2') |> return)

  | Let((x, t), ({value=Put(y1, _, _);_} as rhs), e2) -> (* letの場合 (caml2html: elim_let) *)
      (try
        let dep_arr = find_dep_arr dags arrs [y1] in
        if false then (
          Format.eprintf "dep_arr of %a = %a: [%a]@." Id.pp x pp_kn rhs (Id.pp_t_list ~pp_sep:", ") dep_arr;
          Format.eprintf "arrs: [%a]@." (Id.pp_t_list ~pp_sep:", ") arrs;
          Format.eprintf "dags: @[[";
          Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_text fmt ", ") 
          (fun fmt dag -> Format.fprintf fmt "%a" pp_dag_node dag) 
          Format.err_formatter dags;
          Format.eprintf "]@]@.";
        );
        List.iter (kill dags) dep_arr;
        try_substitute dags x t rhs e2
      with Not_found -> let e2' = f dags arrs e2 in Let((x, t), rhs, e2') |> return)
  | Let((x, t), ({value=ExtFunApp(fn, _);_} as rhs), e2) when let fn = Id.toString fn in 
    String.starts_with fn ~prefix:"create_" && String.ends_with fn ~suffix:"_array" ->
      Let((x, t), rhs, f dags (x::arrs) e2) |> return
  | Let((x, t), ({value=App _|ExtFunApp _;_} as rhs), e2) -> 
      let e2' = f [] arrs e2 in
      Let((x, t), rhs, e2') |> return
  | Let(_, {value=Let _;_}, _) -> assert false
  | Let(_, {value=LetRec _;_}, _) -> assert false
  | Let(_, {value=LetTuple _;_}, _) -> assert false
  | Let((x, t), e1, e2) ->
      let e1' = f [] arrs e1 in
      let e2' = f dags arrs e2 in
      Let((x, t), e1', e2') |> return
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recの場合 (caml2html: elim_letrec) *)
    let e2' = f dags arrs e2 in
    LetRec({ name = (x, t); args = yts; body = f [] arrs e1 }, e2') |> return
  | LetTuple(xts, y, e) ->
      let e' = f dags arrs e in
      LetTuple(xts, y, e') |> return
  | e -> kn

let f e = f [] [] e