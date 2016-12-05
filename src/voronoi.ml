(* https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html
 * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Graphics.html
 * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Array.html *)

open Graphics;;
open Examples;;

let v = v4;;

let euclidean (x1, y1) (x2, y2) =
  int_of_float ((float)(x1 - x2) ** 2. +. (float)(y1 - y2) ** 2.);;
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
          fnc := [(false, {Variables.i = i; c = colors.(c)});
                  (false, {Variables.i = i; c = colors.(c')})] :: !fnc
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
            fnc := [(false, {Variables.i = i; c = colors.(c)});
                    (false, {Variables.i = j; c = colors.(c)})] :: !fnc
          done
      done
    done;
    fnc
  in

  let pre_colored fnc =
    for i = 0 to Array.length b - 1 do
      match cl.(i) with
      | None -> ()
      | Some(c) -> fnc := [(true, {Variables.i = i; c = c})] :: !fnc
    done;
    fnc
  in

  !(pre_colored (exists (unique (adjacence (ref [])))));;

let rec color_from_valuation v vl =
  match vl with
  | [] -> ()
  | (b, l) :: t ->
    let s = v.seeds.(l.Variables.i) in
    if b then
      v.seeds.(l.Variables.i) <- {c = Some l.Variables.c; x = s.x; y = s.y};
    color_from_valuation v t;;

let print_bool b = print_string (if b then "true" else "false");;

let print_valuation v =
  let print_color c =
    print_string (
      if c = white then "white" else
      if c = red then "red" else
      if c = blue then "blue" else
      if c = yellow then "yellow" else
      if c = green then "green" else "") in

  match v with
  | Some v ->
    begin
      let rec aux v =
        match v with
        | [] -> ()
        | h :: t ->
          begin
            print_string "(";
            print_bool (fst h); print_string ", {";
            print_int (snd h).Variables.i; print_string ", ";
            print_color (snd h).Variables.c; print_string "}); ";
            print_newline ();
            aux t
          end in
      aux v
    end
  | None -> ();;

let rec print_fnc fnc =
  match fnc with
  | [] -> ()
  | h::t -> print_valuation (Some h); print_fnc t;;

exception No_value;;
let get = function None -> raise No_value | Some(a) -> a;;

let main () =
  let cell_width, cell_height = fst v.dim / 5, 50 in
  open_graph (" " ^ string_of_int (fst v.dim) ^ "x" ^
              string_of_int (snd v.dim + cell_height));
  clear_graph ();
  auto_synchronize false;

  let colors = [| white; red; green; blue; yellow |] in
  for i = 0 to Array.length colors - 1 do
    set_color colors.(i);
    fill_rect (i * cell_width) (snd v.dim) cell_width cell_height
  done;
  set_color black;
  fill_rect 0 (snd v.dim) (fst v.dim) 1;

  let count_pre_colored cl =
    let x = ref 0 in
    for i = 0 to Array.length cl - 1 do
      if cl.(i) <> None then x := !x + 1
    done;
    !x in

  let m = regions_voronoi distance v in
  let b = adjacences_voronoi v m in
  let cl = make_color_array v in
  let fnc = produce_constraints cl b in
  let c = ref white in
  let z = ref 0 in
  let go_on = ref true in


  color_from_valuation v (get (Sat.solve (fnc)));

  draw_voronoi v m;
  synchronize ();
  while !go_on do
    let e = wait_next_event[Button_down; Key_pressed] in
    let x, y = e.mouse_x, e.mouse_y in

    if e.keypressed && e.key = Char.chr 27 then
      go_on := false
    else if e.button then begin
      if y > snd v.dim + 1 then
        c := point_color x y
      else if y < snd v.dim then begin
        let i = m.(x).(y) in
        if cl.(i) = None then begin
          if !c <> white && v.seeds.(i).c = None then
            z := !z + 1
          else if !c = white && v.seeds.(i).c <> None && !z > 0 then
            z := !z - 1;
          v.seeds.(i) <- {c = if !c = white then None else Some !c;
                          x = v.seeds.(i).x; y = v.seeds.(i).y};
          draw_voronoi v m;
          synchronize ()
        end
      end;

      if !z = Array.length cl - count_pre_colored cl then begin
        let fnc' = ref fnc in
        for i = 0 to Array.length cl - 1 do
          if cl.(i) = None then
            fnc' := [(true, {Variables.i = i; c = get v.seeds.(i).c})] :: !fnc'
        done;
        print_valuation (Sat.solve (!fnc'));
        if Sat.solve (!fnc') <> None then print_string "GAGNE"; print_newline ()
      end
    end
  done;
  close_graph ();;

main ();;
