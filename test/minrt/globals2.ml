(*open MiniMLRuntime;;*)
(**************** グローバル変数の宣言 ****************)

(* オブジェクトの個数 *)
let n_objects = Array.make 1 0


(* オブジェクトのデータを入れるベクトル（最大60個）*)
let objects =
  let dummy = Array.make 0 0.0 in
  Array.make 60 (0, 0, 0, 0, dummy, dummy, false, dummy, dummy, dummy, dummy)


(* Screen の中心座標 *)
let screen = Array.make 3 0.0

(* 視点の座標 *)
let viewpoint = Array.make 3 0.0

(* 光源方向ベクトル (単位ベクトル) *)
let light = Array.make 3 0.0

(* 鏡面ハイライト強度 (標準=255) *)
let beam = Array.make 1 255.0

(* AND ネットワークを保持 *)
let and_net = Array.make 50 (Array.make 1 (-1))

(* OR ネットワークを保持 *)
let or_net = Array.make 1 (Array.make 1 (and_net.(0)))


(* 以下、交差判定ルーチンの返り値格納用 *)
(* solver の交点 の t の値 *)
let solver_dist = Array.make 1 0.0

(* 交点の直方体表面での方向 *)
let intsec_rectside = Array.make 1 0

(* 発見した交点の最小の t *)
let tmin = Array.make 1 (1000000000.0)

(* 交点の座標 *)
let intersection_point = Array.make 3 0.0

(* 衝突したオブジェクト番号 *)
let intersected_object_id = Array.make 1 0

(* 法線ベクトル *)
let nvector = Array.make 3 0.0

(* 交点の色 *)
let texture_color = Array.make 3 0.0


(* 計算中の間接受光強度を保持 *)
let diffuse_ray = Array.make 3 0.0

(* スクリーン上の点の明るさ *)
let rgb = Array.make 3 0.0


(* 画像サイズ *)
let image_size = Array.make 2 0

(* 画像の中心 = 画像サイズの半分 *)
let image_center = Array.make 2 0

(* 3次元上のピクセル間隔 *)
let scan_pitch = Array.make 1 0.0


(* judge_intersectionに与える光線始点 *)
let startp = Array.make 3 0.0

(* judge_intersection_fastに与える光線始点 *)
let startp_fast = Array.make 3 0.0


(* 画面上のx,y,z軸の3次元空間上の方向 *)
let screenx_dir = Array.make 3 0.0

let screeny_dir = Array.make 3 0.0

let screenz_dir = Array.make 3 0.0


(* 直接光追跡で使う光方向ベクトル *)
let ptrace_dirvec  = Array.make 3 0.0


(* 間接光サンプリングに使う方向ベクトル *)
let dirvecs =
  let dummyf = Array.make 0 0.0 in
  let dummyff = Array.make 0 dummyf in
  let dummy_vs = Array.make 0 (dummyf, dummyff) in
  Array.make 5 dummy_vs


(* 光源光の前処理済み方向ベクトル *)
let light_dirvec =
  let dummyf2 = Array.make 0 0.0 in
  let v3 = Array.make 3 0.0 in
  let consts = Array.make 60 dummyf2 in
  (v3, consts)


(* 鏡平面の反射情報 *)
let reflections =
  let dummyf3 = Array.make 0 0.0 in
  let dummyff3 = Array.make 0 dummyf3 in
  let dummydv = (dummyf3, dummyff3) in
  Array.make 180 (0, dummydv, 0.0)


(* reflectionsの有効な要素数 *)
let n_reflections = Array.make 1 0

