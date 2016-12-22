open Graphics;;
open Voronoi;;
open Examples;;

exception No_value;;
let get = function None -> raise No_value | Some(a) -> a;;

let set_color c =
  if c = white then
    set_color (rgb 246 247 189)
  else if c = red then
    set_color (rgb 191 77 40)
  else if c = yellow then
    set_color (rgb 230 172 39)
  else if c = blue then
    set_color (rgb 128 188 163)
  else if c = green then
    set_color (rgb 101 86 67)
  else
    set_color c;;

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
      Array.iteri (fun i s ->
          let d' = dist (x, y) (s.x, s.y) in
          if d' < !d then begin
            d := d';
            matrix.(x).(y) <- i
          end
        ) v.seeds
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
        Graphics.set_color white
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
  Array.iteri (fun i s -> cl.(i) <- s.c) v.seeds;
  cl;;

let count_pre_colored cl =
  let count = ref 0 in
  Array.iter (fun c -> if c <> None then count := !count + 1) cl;
  !count;;

let get_colors cl =
  let colors = ref (Array.make 0 0) in
  Array.iter (fun c ->
      if c <> None then
        let c = get c in
        let ok = ref true in
        Array.iter (fun c' -> if c = c' then ok := false) !colors;
        if !ok then colors := Array.append !colors [| c |]
    ) cl;
  !colors
;;

let produce_constraints cl b =
  let colors = get_colors cl in

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

type cell = {x : int; y : int; w : int; h : int; c : color};;
type button = {x : int; y : int; w : int; h : int; txt : string};;
type game_state = Play | Previous | Next | Quit;;

let play v has_prev has_next =
  (* Window setup *)
  let voronoi_width, voronoi_height = v.dim in
  let margin_right, margin_top = 150, 50 in
  resize_window (voronoi_width + margin_right) (voronoi_height + margin_top);

  (* Voronoï *)
  let distance = ref 0 in
  let m = ref (regions_voronoi distances.(!distance) v) in
  let b = ref (adjacences_voronoi v !m) in
  let cl = make_color_array v in
  let ncl = count_pre_colored cl in
  let fnc = ref (produce_constraints cl !b) in
  let c = ref white in
  let z = ref 0 in
  let graph_drawn = ref false in
  let state = ref Play in
  draw_voronoi v !m;

  (* Color cells *)
  let colors = get_colors cl in
  let cell_width = voronoi_width / (Array.length colors + 1) in
  set_color white;
  fill_rect 0 voronoi_height cell_width margin_top;
  Array.iteri (fun i c ->
      set_color c;
      fill_rect ((i+1) * cell_width) voronoi_height cell_width margin_top
    ) colors;
  Graphics.set_color black;
  moveto 0 voronoi_height;
  lineto voronoi_width voronoi_height;

  (* Draw right background *)
  let bkgd_color = rgb 197 188 142 in
  Graphics.set_color bkgd_color;
  fill_rect voronoi_width 0 margin_right (voronoi_height + margin_top);
  Graphics.set_color black;
  moveto voronoi_width 0;
  lineto voronoi_width (voronoi_height + margin_top);

  (* Buttons *)
  let btn_color = rgb 105 103 88 in
  let btn_margin_x, btn_margin_y = 10, 6 in
  let btn_width, btn_height = margin_right - btn_margin_x, 25 in
  let btn_x = voronoi_width + btn_margin_x / 2 in

  (* bravo/reset/solve/{prev,next}/quit/dist *)
  let solve_btn = {x = btn_x; y = voronoi_height / 2 - btn_margin_y / 2;
                   w = btn_width; h = btn_height;
                   txt = "Solution"} in
  let reset_btn = {x = btn_x; y = solve_btn.y + btn_height + btn_margin_y / 2;
                   w = btn_width; h = btn_height;
                   txt = "Nettoyer"} in
  let bravo_btn = {x = btn_x; y = reset_btn.y + btn_height + btn_margin_y / 2;
                   w = btn_width; h = btn_height;
                   txt = "Bravo !"} in
  let prev_btn = {x = btn_x; y = solve_btn.y - btn_height - btn_margin_y / 2;
                  w = btn_width / 2 - btn_margin_x / 4; h = btn_height;
                  txt = "<--"} in
  let next_btn = {x = btn_x + btn_width / 2 + btn_margin_x / 4;
                  y = solve_btn.y - btn_height - btn_margin_y / 2;
                  w = btn_width / 2 - btn_margin_x / 4; h = btn_height;
                  txt = "-->"} in
  let quit_btn = {x = btn_x; y = prev_btn.y - btn_height - btn_margin_y / 2;
                  w = btn_width; h = btn_height;
                  txt = "Quitter"} in
  let dist_btn = {x = btn_x; y = quit_btn.y - btn_height - btn_margin_y / 2;
                  w = btn_width; h = btn_height;
                  txt = "Distance : "} in

  let erase_btn btn =
    Graphics.set_color bkgd_color;
    fill_rect btn.x btn.y btn.w btn.h
  in
  let draw_btn_txt btn txt =
    let txt = if txt = "" then btn.txt else btn.txt ^ txt in
    let txtw, txth = text_size txt in
    moveto (btn.x + btn.w / 2 - txtw / 2) (btn.y + btn.h / 2 - txth / 2);
    Graphics.set_color black;
    draw_string txt;
  in
  let draw_btn btn =
    erase_btn btn;
    Graphics.set_color btn_color;
    fill_rect btn.x btn.y btn.w btn.h;
    Graphics.set_color black;
    draw_rect btn.x btn.y btn.w btn.h;
    draw_btn_txt btn ""
  in
  let draw_dist_btn () =
    erase_btn dist_btn;
    draw_btn_txt dist_btn (string_of_int (!distance + 1) ^ "/" ^
                           string_of_int (Array.length distances))
  in
  let draw_bravo_btn () =
    erase_btn bravo_btn;
    draw_btn_txt bravo_btn "";
  in

  let has_clicked btn e =
    e.mouse_x >= btn.x && e.mouse_x < btn.x + btn.w &&
    e.mouse_y >= btn.y && e.mouse_y < btn.y + btn.h
  in

  draw_btn solve_btn;
  draw_btn reset_btn;
  draw_btn prev_btn;
  draw_btn next_btn;
  draw_btn quit_btn;
  draw_dist_btn ();

  (* Color circle *)
  let draw_color_circle () =
    let x, y, r = voronoi_width + margin_right / 2,
                  voronoi_height + margin_top / 2,
                  margin_top / 2 - btn_margin_y in
    set_color !c;
    fill_circle x y r;
    Graphics.set_color black;
    draw_circle x y r
  in
  draw_color_circle ();


  synchronize ();
  while !state = Play do
    let e = wait_next_event[Button_down; Key_pressed] in
    let x, y = e.mouse_x, e.mouse_y in

    if e.keypressed then begin
      if e.key = Char.chr 27 then
        state := Quit
      else if compare e.key '1' >= 0 &&
              compare e.key (char_of_int (int_of_char '0' + Array.length distances)) <= 0 then begin
        distance := int_of_char e.key - int_of_char '0' - 1;
        m := regions_voronoi distances.(!distance) v;
        b := adjacences_voronoi v !m;
        fnc := produce_constraints cl !b;
        if !graph_drawn then (draw_graph v !b; synchronize ());
        reset_voronoi cl v;
        erase_btn bravo_btn;
        draw_dist_btn ();
        draw_voronoi v !m;
        z := 0;
        synchronize ()
      end
      else if e.key = 'g' then begin
        graph_drawn := if !graph_drawn then false else true;
        if !graph_drawn then draw_graph v !b else draw_voronoi v !m;
        synchronize ()
      end
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
          z := Array.length cl - ncl
        end;
        draw_voronoi v !m;
        synchronize ()
      end
      else if has_clicked reset_btn e then begin
        reset_voronoi cl v;
        z := 0;
        draw_voronoi v !m;
        erase_btn bravo_btn;
        synchronize ()
      end
      else if has_clicked quit_btn e then
        state := Quit
      else if has_next && has_clicked next_btn e then
        state := Next
      else if has_prev && has_clicked prev_btn e then
        state := Previous
      else if x < fst v.dim && y > snd v.dim + 1 then begin
        c := point_color x y;
        draw_color_circle ();
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

          if !z = Array.length cl - ncl then begin
            let fnc' = ref !fnc in
            for i = 0 to Array.length cl - 1 do
              if cl.(i) = None then
                fnc' := [(true, {Variables.i = i; c = get v.seeds.(i).c})] :: !fnc'
            done;
            if Sat.solve (!fnc') <> None then begin
              draw_bravo_btn ();
            end
          end;
          synchronize ()
        end
      end
    end;
    if !graph_drawn then (draw_graph v !b; synchronize ())
  done;
  !state;;


let main () =
  open_graph (" 1x1");
  clear_graph ();
  auto_synchronize false;

  let rec walk_voronois prev next current =
    let state = play current (prev <> []) (next <> []) in
    match state with
    | Quit -> ()
    | Previous -> begin
      match prev with
      | [] -> ()
      | h :: t -> walk_voronois t (current :: next) h
      end
    | Next -> begin
      match next with
      | [] -> ()
      | h :: t -> walk_voronois (current :: prev) t h
      end
    | _ -> ()
  in
  let hd = List.hd voronois in
  walk_voronois [] (List.tl voronois) hd;
  close_graph ();;

main ();;
