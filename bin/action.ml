let onParsed f (tree : Syntax.ast) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".parsed") in
    let ff = Format.formatter_of_out_channel oc in Format.set_geometry ~max_indent:190 ~margin:200;
    Format.fprintf ff "@[%a@]@." Syntax.pp_ast tree;
    close_out oc

let onKNormalized f (tree : KNormal.t) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".knormalized") in
    let ff = Format.formatter_of_out_channel oc in Format.set_geometry ~max_indent:190 ~margin:200;
    Format.fprintf ff "@[%a@]@." KNormal.pp_kn tree;
    close_out oc

let onAlphaConverted f (tree : KNormal.t) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".alpha") in
    let ff = Format.formatter_of_out_channel oc in Format.set_geometry ~max_indent:190 ~margin:200;
    Format.fprintf ff "@[%a@]@." KNormal.pp_kn tree;
    close_out oc

let onANormalized f (tree : KNormal.t) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".A-normalized") in
    let ff = Format.formatter_of_out_channel oc in Format.set_geometry ~max_indent:190 ~margin:200;
    Format.fprintf ff "@[%a@]@." KNormal.pp_kn tree;
    close_out oc

let onBeforeCSE f (tree : KNormal.t) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".before_CSE") in
    let ff = Format.formatter_of_out_channel oc in Format.set_geometry ~max_indent:190 ~margin:200;
    Format.fprintf ff "@[%a@]@." KNormal.pp_kn tree;
    close_out oc

let onAfterCSE f (tree : KNormal.t) =
  if f = "" then ()
  else
    let oc = open_out (f ^ ".after_CSE") in
    let ff = Format.formatter_of_out_channel oc in Format.set_geometry ~max_indent:190 ~margin:200;
    Format.fprintf ff "@[%a@]@." KNormal.pp_kn tree;
    close_out oc
