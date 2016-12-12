open Graphics;;
open Examples;;

let euclidean (x1, y1) (x2, y2) =
  int_of_float ((float)(x1 - x2) ** 2. +. (float)(y1 - y2) ** 2.);;
let taxicab (x1, y1) (x2, y2) = abs (x1 - x2) + abs (y1 - y2);;
let taxicab2 (x1, y1) (x2, y2) = max (abs (x1 - x2)) (abs (y1 - y2));;
let fn a b = int_of_float (sqrt ((float)(euclidean a b))) + taxicab a b;;
let fn2 a b = taxicab a b + taxicab2 a b;;

let distances = [| euclidean; taxicab; taxicab2; fn; fn2 |];;

let regions_voronoi dist v =
  let width, height = v.dim in
  let matrix = Array.make_matrix width height (-1) in
  for x = 0 to width - 1 do
    for y = 0 to height - 1 do
      let d = ref max_int in
      for s = 0 to Array.length v.seeds - 1 do
        let d' = dist (x, y) (v.seeds.(s).x, v.seeds.(s).y) in
        if d' < !d then begin
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
      else begin
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

let reset_voronoi cl v =
  for i = 0 to Array.length cl - 1 do
    if cl.(i) = None then
      v.seeds.(i) <- {c = None; x = v.seeds.(i).x; y = v.seeds.(i).y}
  done;;

let draw_graph v b =
  set_color black;
  for i = 0 to Array.length b - 1 do
    for j = 0 to Array.length b - 1 do
      if b.(i).(j) then begin
        moveto v.seeds.(i).x v.seeds.(i).y;
        lineto v.seeds.(j).x v.seeds.(j).y
      end
    done
  done;;

exception No_value;;
let get = function None -> raise No_value | Some(a) -> a;;

let print_bool b = print_string (if b then "true" else "false");;

let print_valuation v =
  let print_color c =
    print_string (
      if c = white then "white" else
      if c = red then "red" else
      if c = blue then "blue" else
      if c = yellow then "yellow" else
      if c = green then "green" else "")
  in
  match v with
  | Some v -> begin
      let rec aux v =
        match v with
        | [] -> ()
        | h :: t -> begin
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

type button = {y : int; txt : string};;

let play v =
  let button_width, button_height, button_x = 150, 30, fst v.dim + 5 in
  let cell_width, cell_height = fst v.dim / 5, 50 in
  open_graph (" " ^ string_of_int (fst v.dim + button_width + 8) ^ "x" ^
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
  fill_rect (fst v.dim) 0 1 (snd v.dim + cell_height);

  let count_pre_colored cl =
    let x = ref 0 in
    for i = 0 to Array.length cl - 1 do
      if cl.(i) <> None then x := !x + 1
    done;
    !x in

  (* Buttons bravo/reset/solve/quit/dist *)
  let bkgd_color, btn_color = rgb 77 114 121, rgb 8 52 60 in

  let solve_btn = {y = (snd v.dim) / 2 - button_height / 2; txt = "Solution"} in
  let reset_btn = {y = solve_btn.y + button_height + 5; txt = "Nettoyer"} in
  let quit_btn = {y = solve_btn.y - button_height - 5; txt = "Quitter"} in
  let bravo_btn = {y = reset_btn.y + button_height + 5; txt = "Bravo !"} in
  let dist_btn = {y = quit_btn.y - button_height - 5; txt = "Distance : "} in

  let has_clicked b e =
    e.mouse_x >= button_x && e.mouse_x < button_x + button_width &&
    e.mouse_y >= b.y && e.mouse_y < b.y + button_height
  in

  set_color bkgd_color;
  fill_rect (fst v.dim + 1) 0 (button_width + 10) (snd v.dim + cell_height);
  let erase_btn b c =
    set_color c;
    fill_rect button_x b.y button_width button_height;
  in
  let draw_btn b c r =
    erase_btn b c;
    set_color black;
    if r then draw_rect button_x b.y button_width button_height;
    moveto (button_x + button_width / 2 - (fst (text_size b.txt)) / 2)
           (b.y + button_height / 2 - (snd (text_size b.txt)) / 2);
    draw_string b.txt
  in
  draw_btn solve_btn btn_color true;
  draw_btn reset_btn btn_color true;
  draw_btn quit_btn btn_color true;

  let distance = ref 0 in
  let m = ref (regions_voronoi distances.(!distance) v) in
  let b = ref (adjacences_voronoi v !m) in
  let cl = make_color_array v in
  let fnc = ref (produce_constraints cl !b) in
  let c = ref white in
  let z = ref 0 in
  let go_on = ref true in
  let graph_drawn = ref false in

  let draw_current_color () =
    let x, y, r = (fst v.dim) + button_width / 2 + 4,
                  (snd v.dim) + cell_height / 2,
                  cell_height / 2 - 5 in
    set_color !c;
    fill_circle x y r;
    set_color black;
    draw_circle x y r
  in

  let draw_distance () =
    let txt = dist_btn.txt ^ string_of_int (!distance + 1) ^ "/"
              ^ string_of_int (Array.length distances) in
    erase_btn dist_btn bkgd_color;
    set_color black;
    moveto (button_x + button_width / 2 - (fst (text_size txt)) / 2)
           (dist_btn.y + button_height / 2 - (snd (text_size txt)) / 2);
    draw_string txt
  in

  let erase_bravo () = erase_btn bravo_btn bkgd_color in

  draw_distance ();
  draw_current_color ();
  draw_voronoi v !m;
  synchronize ();
  while !go_on do
    let e = wait_next_event[Button_down; Key_pressed] in
    let x, y = e.mouse_x, e.mouse_y in

    if e.keypressed then begin
      if e.key = Char.chr 27 then
        go_on := false
      else if compare e.key '1' >= 0 &&
              compare e.key (char_of_int (int_of_char '0' + Array.length distances)) <= 0 then begin
        distance := int_of_char e.key - int_of_char '0' - 1;
        m := regions_voronoi distances.(!distance) v;
        b := adjacences_voronoi v !m;
        fnc := produce_constraints cl !b;
        if !graph_drawn then (draw_graph v !b; synchronize ());
        reset_voronoi cl v;
        erase_bravo ();
        draw_distance ();
        draw_voronoi v !m;
        z := 0;
        synchronize ()
      end
      else if e.key = 'g' then begin
        graph_drawn := if !graph_drawn then false else true;
        if !graph_drawn then draw_graph v !b else draw_voronoi v !m;
        synchronize ()
      end
(*
      else if compare e.key 'a' >= 0 &&
              compare e.key (char_of_int (int_of_char 'a' + List.length voronois)) <= 0 then begin
        i := int_of_char
              end
*)
    end
    else if e.button then begin
      if has_clicked solve_btn e then begin
        let fnc' = ref !fnc in
        for i = 0 to Array.length v.seeds - 1 do
          if v.seeds.(i).c <> None then
            fnc' := [(true, {Variables.i = i; c = get v.seeds.(i).c})] :: !fnc'
        done;
        let valuation = Sat.solve (!fnc') in
        if valuation <> None then begin
          color_from_valuation v (get valuation);
          z := Array.length cl - count_pre_colored cl
        end;
        draw_voronoi v !m;
        synchronize ()
      end
      else if has_clicked reset_btn e then begin
        reset_voronoi cl v;
        z := 0;
        draw_voronoi v !m;
        erase_bravo ();
        synchronize ()
      end
      else if has_clicked quit_btn e then
        go_on := false
      else if x < fst v.dim && y > snd v.dim + 1 then begin
        c := point_color x y;
        draw_current_color ();
        synchronize ()
      end
      else if x < fst v.dim && y < snd v.dim then begin
        let i = !m.(x).(y) in
        if cl.(i) = None then begin
          if !c <> white && v.seeds.(i).c = None then
            z := !z + 1
          else if !c = white && v.seeds.(i).c <> None && !z > 0 then
            z := !z - 1;
          v.seeds.(i) <- {c = if !c = white then None else Some !c;
                          x = v.seeds.(i).x; y = v.seeds.(i).y};
          draw_voronoi v !m;

          if !z = Array.length cl - count_pre_colored cl then begin
            let fnc' = ref !fnc in
            for i = 0 to Array.length cl - 1 do
              if cl.(i) = None then
                fnc' := [(true, {Variables.i = i; c = get v.seeds.(i).c})] :: !fnc'
            done;
            if Sat.solve (!fnc') <> None then begin
              draw_btn bravo_btn bkgd_color false
            end
          end;
          synchronize ()
        end
      end
    end;
    if !graph_drawn then (draw_graph v !b; synchronize ())
  done;
  close_graph ();;

let main () =
  let rec aux l =
    match l with
    | [] -> ()
    | v :: t -> play v; aux t
  in
  aux voronois;;

main ();;
