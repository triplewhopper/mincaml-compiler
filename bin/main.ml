let limit = ref 1000
let _ = Printexc.record_backtrace true

let rec iter n filename kn =
  (** 最適化処理をくりかえす (caml2html: main_iter) *)
  (* Format.eprintf "iteration %d@..." n; *)
  if n = 0 then (Format.eprintf "iteration %d... nothing to do@." n;kn)
  else
    let kn' = kn in 

    let kn' = Assoc.f kn' in
    Action.onANormalized filename kn';
    Action.onBeforeCSE (filename ^ "-" ^ string_of_int n)  kn';
    let kn' = Cse.f kn' in
    let kn' = Beta.f kn' in
    Action.onAfterCSE (filename ^ "-" ^ string_of_int n) kn';
    (* let kn' = Inline.f kn' in
    let kn' = ConstFold.f kn' in
    let kn' = Elim.f kn' in *)
    Format.eprintf "iteration %d... done@." n;
    if KNormal.shallowEq kn kn' then kn else iter (n - 1) filename kn'

let lexbuf ~filename outchan l : unit =
  (** バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.resetCounter ();
  Typing.extenv := M.empty;
  assert (String.ends_with filename ~suffix:".ml" = false);
  Lexing.set_filename l (filename ^ ".ml");
  match Parser.toplevel Lexer.token l with
  | None -> ()
  | Some parsetree ->
      Action.onParsed filename parsetree;
      let knormal = parsetree |> Typing.f |> KNormal.f in
      Action.onKNormalized filename knormal;
      let knormal = knormal |> Alpha.f in 
      Action.onAlphaConverted filename knormal;
      knormal |> iter !limit filename |> Closure.f |> Virtual.f |> Simm.f
      |> RegAlloc.f |> Emit.f outchan

let lexbuf_string outchan l : unit =
  (** バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.resetCounter ();
  Typing.extenv := M.empty;
  Lexing.set_filename l "//toplevel//";
  match Parser.toplevel Lexer.token l with
  | None -> ()
  | Some parsetree ->
      parsetree |> Typing.f |> KNormal.f |> Alpha.f |> iter !limit "<stdin>"|> Closure.f
      |> Virtual.f |> Simm.f |> RegAlloc.f |> Emit.f outchan

(** 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)
let string s = lexbuf_string stdout (Lexing.from_string s)

let file f = (** ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  let buf = Lexing.from_channel inchan in
  try
    lexbuf outchan buf ~filename:f;
    close_in inchan;
    close_out outchan
  with
  | Parser.Error ->
      close_in inchan;
      close_out outchan;
      let pos0 = Lexing.lexeme_start_p buf and pos1 = Lexing.lexeme_end_p buf in
      Format.eprintf "@[File \"%s\",@ %s,@ characters@ %d-%d@]@." pos0.pos_fname
        (if pos0.pos_lnum = pos1.pos_lnum then
           Format.sprintf "@[line@ %d@]" pos0.pos_lnum
         else Format.sprintf "@[lines@ %d-%d@]" pos0.pos_lnum pos1.pos_lnum)
        (pos0.pos_cnum - pos0.pos_bol + 1)
        (pos1.pos_cnum - pos1.pos_bol + 1);
      Format.eprintf "@[Syntax error@]@.";
      exit 1
  | Typing.Error (Typing.Known { ast; got; expected }) ->
      close_in inchan;
      close_out outchan;
      Format.eprintf "ast:@ %a@." Syntax.pp_ast ast;
      let front = NList.front ast.tokens |> Option.get
      and back = NList.back ast.tokens |> Option.get in
      Format.eprintf "@[File \"%s.ml\",@ %s,@ characters@ %d-%d@]@." f
        (if front.start.pos_lnum = back.stop.pos_lnum then
           Format.sprintf "@[lines@ %d@]" front.start.pos_lnum
         else
           Format.sprintf "@[lines@ %d-%d@]" front.start.pos_lnum
             back.stop.pos_lnum)
        (front.start.pos_cnum - front.start.pos_bol + 1)
        (back.stop.pos_cnum - back.stop.pos_bol + 1);
      Format.eprintf "@[%a@]@." Syntax.pp_ast ast;
      Format.eprintf "@[TypeError: expected %a, but got %a@]@." Type.pp expected
        Type.pp got;
      exit 1
  | Typing.Error (Unknown ast) as e ->
      close_in inchan;
      close_out outchan;
      let front = NList.front ast.tokens |> Option.get
      and back = NList.back ast.tokens |> Option.get in
      Format.eprintf "@[File \"%s.ml\",@ %s,@ characters@ %d-%d@]@." f
        (if front.start.pos_lnum = back.stop.pos_lnum then
           Format.sprintf "@[lines@ %d@]" front.start.pos_lnum
         else
           Format.sprintf "@[lines@ %d-%d@]" front.start.pos_lnum
             back.stop.pos_lnum)
        (front.start.pos_cnum - front.start.pos_bol + 1)
        (back.stop.pos_cnum - back.stop.pos_bol + 1);
      Format.eprintf "@[%a@]@." Syntax.pp_ast ast;
      Format.eprintf "@[TypeError: unknown type@]@.";
      exit 1
  | e ->
      close_in inchan;
      close_out outchan;
      raise e

let () = (** ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [
      ( "-inline",
        Arg.Int (fun i -> Inline.threshold := i),
        "maximum size of functions inlined" );
      ( "-iter",
        Arg.Int (fun i -> limit := i),
        "maximum number of optimizations iterated" );
    ]
    (fun s -> files := !files @ [ s ])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n"
    ^ Printf.sprintf
        "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..."
        Sys.argv.(0));
  List.iter (fun f -> ignore (file f)) !files
