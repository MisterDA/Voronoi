(* https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html
 * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Graphics.html
 * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Array.html *)

open Graphics;;

type seed = {c : color option; x : int; y : int}
type voronoi = {dim: int * int; seeds : seed array}

let euclidean (x1, y1) (x2, y2) = int_of_float ((float)(x1 - x2) ** 2. +. (float)(y1 - y2) ** 2.);;
let taxicab (x1, y1) (x2, y2) = abs (x1 - x2) + abs (y1 - y2);;
let taxicab2 (x1, y1) (x2, y2) = max (abs (x1 - x2)) (abs (y1 - y2));;
let fn a b = int_of_float (sqrt ((float)(euclidean a b))) + taxicab a b;;
let fn2 a b = taxicab a b + taxicab2 a b;;
let distance = taxicab;;

let regions_voronoi dist v =
  let width, height = v.dim in
  let matrix = Array.make_matrix width height (-1) in
  for x = 0 to width - 1 do
    for y = 0 to height - 1 do
      let d = ref max_int in
      for s = 0 to Array.length v.seeds - 1 do
        let d' = dist (x, y) (v.seeds.(s).x, v.seeds.(s).y) in
        if d' < !d then
          begin
            d := d';
            matrix.(x).(y) <- s
          end
      done
    done
  done;
  matrix;;

let draw_voronoi v m =
  let width, height = v.dim in
  for x = 0 to width - 1 do
    for y = 0 to height - 1 do
      let s = m.(x).(y) in
      if y > 0 && s <> m.(x).(y - 1) ||
         x < width - 1 && s <> m.(x + 1).(y) ||
         y < height - 1 && s <> m.(x).(y + 1) ||
         x > 0 && s <> m.(x - 1).(y) then
        set_color black
      else
        begin
          match v.seeds.(m.(x).(y)).c with
          | None -> set_color white
          | Some c -> set_color c
        end;
      plot x y
     done
  done;;

let adjacences_voronoi v m =
  let n = Array.length v.seeds in
  let b = Array.make_matrix n n false in
  let width, height = v.dim in
  for x = 0 to width - 1 do
    for y = 0 to height - 1 do
      let h = m.(x).(y) in
      b.(h).(h) <- true;
      if y > 0 && h <> m.(x).(y - 1) then
        b.(h).(m.(x).(y - 1)) <- true;
      if x < width - 1 && h <> m.(x + 1).(y) then
        b.(h).(m.(x + 1).(y)) <- true;
      if y < height - 1 && h <> m.(x).(y + 1) then
        b.(h).(m.(x).(y + 1)) <- true;
      if x > 0 && h <> m.(x - 1).(y) then
        b.(h).(m.(x - 1).(y)) <- true;
    done
  done;
  b;;

module Variables = struct
  type t = {i : int; c : color}
  let compare s1 s2 =
    if s1.i > s2.i then 1
    else if s1.i = s2.i then
      if s1.c > s2.c then 1 else if s1.c = s2.c then 0 else -1
    else -1
end;;

module Sat = Sat_solver.Make(Variables);;

let make_color_array v =
  let cl = Array.make (Array.length v.seeds) None in
  for i = 0 to Array.length v.seeds - 1 do
    cl.(i) <- v.seeds.(i).c
  done;
  cl;;

let produce_constraints cl b =
  let colors = [| red; blue; green; yellow |] in

  let exists fnc =
    for i = 0 to Array.length b - 1 do
      let disj = ref [] in
      for c = 0 to Array.length colors - 1 do
        disj := (true, {Variables.i = i; c = colors.(c)}) :: !disj
      done;
      fnc := !disj :: !fnc
    done;
    fnc
  in

  let unique fnc =
    for i = 0 to Array.length b - 1 do
      for c = 0 to Array.length colors - 1 do
        for c' = c + 1 to Array.length colors - 1 do
          fnc := [(false, {Variables.i = i; c = colors.(c)}); (false, {Variables.i = i; c = colors.(c')})] :: !fnc
        done
      done
    done;
    fnc
  in

  let adjacence fnc =
    for i = 0 to Array.length b - 1 do
      for j = 0 to Array.length b - 1 do
        if i <> j && b.(i).(j) then
          for c = 0 to Array.length colors - 1 do
            fnc := [(false, {Variables.i = i; c = colors.(c)}); (false, {Variables.i = j; c = colors.(c)})] :: !fnc
          done
      done
    done;
    fnc
  in

  !(exists (unique (adjacence (ref []))));;

let v4 =  {
  dim = 800,800;
  seeds = [|
    {c = None; x=100; y=75};
    {c = None; x=125; y=225};
    {c = Some red; x=25; y=255};
    {c = None; x=60; y=305};
    {c = Some blue; x=50; y=400};
    {c = Some green; x=100; y=550};
    {c = Some green; x=150; y=25};
    {c = Some red; x=200; y=55};
    {c = None; x=200; y=200};
    {c = None; x=250; y=300};
    {c = None; x=300; y=450};
    {c = None; x=350; y=10};
    {c = None; x=357; y=75};
    {c = Some yellow; x=450; y=80};
    {c = Some blue; x=400; y=150};
    {c = None; x=550; y=350};
    {c = None; x=400; y=450};
    {c = None; x=400; y=500};
    {c = Some red; x=500; y=75};
    {c = Some green; x=600; y=100};
    {c = Some red; x=700; y=75};
    {c = None; x=578; y=175};
    {c = None; x=750; y=205};
    {c = None; x=520; y=345};
    {c = None; x=678; y=420};
    {c = None; x=600; y=480};
    {c = Some blue; x=650; y=480};
    {c = None; x=750; y=500};
    {c = None; x=600; y=550};
    {c = Some red; x=700; y=550};
  |]
}

let v = v4;;

let () =
  let cell_width, cell_height = fst v.dim / 5, 50 in
  open_graph (" " ^ string_of_int (fst v.dim) ^ "x" ^ string_of_int (snd v.dim + cell_height));
  clear_graph ();
  auto_synchronize false;

  let colors = [| white; red; green; blue; yellow |] in
  for i = 0 to Array.length colors - 1 do
    set_color colors.(i);
    fill_rect (i * cell_width) (snd v.dim) cell_width cell_height
  done;
  set_color black;
  fill_rect 0 (snd v.dim) (fst v.dim) 1;

  let m = regions_voronoi distance v in
  let b = adjacences_voronoi v m in
  let cl = make_color_array v in
  let c = ref white in

  draw_voronoi v m;
  synchronize ();
  while true do
    let e = wait_next_event[Button_down] in
    let x, y = e.mouse_x, e.mouse_y in

    if y > snd v.dim + 1 then
      c := point_color x y
    else if y < snd v.dim then
      let i = m.(x).(y) in
      if cl.(i) = None then
        begin
          v.seeds.(i) <- {c = Some !c; x = v.seeds.(i).x; y = v.seeds.(i).y};
          draw_voronoi v m;
          synchronize ()
        end
  done;
  close_graph ();;