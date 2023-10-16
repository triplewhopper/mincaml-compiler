let limit = ref 1000
let _ = Printexc.record_backtrace true

let rec iter n e =
  (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e
  else
    let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
    if e = e' then e else iter (n - 1) e'

let lexbuf ~onParsed ~onKNormalized ~filename outchan l : unit =
  (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  assert (String.ends_with filename ~suffix:".ml" = false);
  Lexing.set_filename l (filename ^ ".ml");
  match Parser.toplevel Lexer.token l with
  | None -> ()
  | Some parsetree ->
      onParsed filename parsetree;
      let knormal = parsetree |> Typing.f |> KNormal.f in
      onKNormalized filename knormal;
      knormal |> Alpha.f |> iter !limit |> Closure.f |> Virtual.f |> Simm.f
      |> RegAlloc.f |> Emit.f outchan

let lexbuf_string outchan l : unit =
  (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  Lexing.set_filename l "//toplevel//";
  match Parser.toplevel Lexer.token l with
  | None -> ()
  | Some parsetree ->
      parsetree |> Typing.f |> KNormal.f |> Alpha.f |> iter !limit |> Closure.f
      |> Virtual.f |> Simm.f |> RegAlloc.f |> Emit.f outchan

let onParsed f (tree : Syntax.ast) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".parsed") in
    let ff = Format.formatter_of_out_channel oc in
    Format.fprintf ff "@[%a@]@." Syntax.pp_ast tree;
    close_out oc

let onKNormalized f (tree : KNormal.t) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".knormalized") in
    let ff = Format.formatter_of_out_channel oc in
    Format.fprintf ff "@[%a@]@." KNormal.pp tree;
    close_out oc

let string s = lexbuf_string stdout (Lexing.from_string s)

(* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f =
  (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  let buf = Lexing.from_channel inchan in
  try
    lexbuf outchan buf ~onParsed ~onKNormalized ~filename:f;
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
      Format.eprintf "@[File \"%s\",@ %s,@ characters@ %d-%d@]@." f
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
      Format.eprintf "@[File \"%s\",@ %s,@ characters@ %d-%d@]@." f
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
  | Failure e ->
      close_in inchan;
      close_out outchan;
      failwith e
  | e ->
      close_in inchan;
      close_out outchan;
      raise e

let () =
  (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
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
