(** Module principal du projet *)

open Graphics;;
open Voronoi;;
open Examples;;

exception No_value;;
let get = function None -> raise No_value | Some(a) -> a;;

(** Type alias pour les fonctions de distance *)
type distance = (int * int) -> (int * int) -> int;;

let euclidean : distance = fun (x1, y1) (x2, y2) ->
  int_of_float ((float)(x1 - x2) ** 2. +. (float)(y1 - y2) ** 2.);;
let taxicab : distance = fun (x1, y1) (x2, y2) ->
  abs (x1 - x2) + abs (y1 - y2);;
let taxicab2 : distance = fun (x1, y1) (x2, y2) ->
  max (abs (x1 - x2)) (abs (y1 - y2));;
let fn : distance = fun a b ->
  int_of_float (sqrt ((float)(euclidean a b))) + taxicab a b;;
let fn2 : distance = fun a b -> taxicab a b + taxicab2 a b;;

let distances = [| euclidean; taxicab; taxicab2; fn; fn2 |];;
let ndistances = Array.length distances;;

(** Détermine les différentes régions du graphe à partir d'une fonction de
    distance *)
let regions_voronoi (dist : distance) v =
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
          end)
        v.seeds
    done
  done;
  matrix;;

(** Dessine le graphe avec la délimitation des différentes régions, tenant
    compte de la pré-coloration *)
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

(** Définit la matrice d'adjacence des régions du voronoi : deux régions sont
    adjacentes si elles ont une délimitation commune *)
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

(** Dresse un tableau contenant la couleur et le germe des régions d'un voronoi *)
let make_color_array v = Array.map (fun s -> s.c) v.seeds;;

(** Renvoie le nombre de régions pré-coloriées à partir d'un tableau du type de
    la fonction précédente *)
let count_pre_colored cl =
  let count = ref 0 in
  Array.iter (fun c -> if c <> None then incr count) cl;
  !count;;

(** Renvoie un tableau contenant les différentes couleurs présentes dans la
    pré-coloration du voronoi *)
let get_colors cl =
  let colors = ref (Array.make 0 0) in
  Array.iter (fun c ->
      if c <> None then
        let c = get c in
        let ok = ref true in
        Array.iter (fun c' -> if c = c' then ok := false) !colors;
        if !ok then colors := Array.append !colors [| c |])
    cl;
  !colors
;;

(** Produit la FNC avec les conditions d'existence, d'unicité et d'adjacence des
    régions du voronoi *)
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

  (* La valuation correspondant à la pré-coloration *)
  let pre_colored fnc =
    for i = 0 to Array.length b - 1 do
      match cl.(i) with
      | None -> ()
      | Some(c) -> fnc := [(true, {Variables.i = i; c = c})] :: !fnc
    done;
    fnc
  in

  !(pre_colored (exists (unique (adjacence (ref [])))));;

(** Permet d'obtenir une coloration satisfaisante à partir d'une valuation bien
    définie *)
let rec color_from_valuation v vl =
  match vl with
  | [] -> ()
  | (b, l) :: t ->
    let s = v.seeds.(l.Variables.i) in
    if b then
      v.seeds.(l.Variables.i) <- {c = Some l.Variables.c; x = s.x; y = s.y};
    color_from_valuation v t;;

(** Permet de rafraîchir le graphe à son état d'origine *)
let reset_voronoi cl v =
  Array.iteri (fun i c ->
      if c = None then
        v.seeds.(i) <- {c = None; x = v.seeds.(i).x; y = v.seeds.(i).y})
    cl;;

(** Dessine le graphe *)
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


(** Affiche la valeur d'un booléen *)
let print_bool b = print_string (if b then "true" else "false");;

(** Affiche la valuation, c'est-à-dire une liste d'éléments de la forme
    (booléen, {n° région, couleur}) *)
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

(** Affiche la FNC qui est un ensemble de valuations *)
let rec print_fnc fnc =
  match fnc with
  | [] -> ()
  | h::t -> print_valuation (Some h); print_fnc t;;


type button = {x : int; y : int; w : int; h : int; txt : string};;
type game_state = Play | Previous | Next | Quit;;

(** Fonction de jeu *)
let play v has_prev has_next =
  (* Configuration de la fenêtre de jeu *)
  let voronoi_width, voronoi_height = v.dim in
  let margin_right, margin_top = 150, 50 in
  resize_window (voronoi_width + margin_right) (voronoi_height + margin_top);

  (* Instructions relatives au voronoi *)
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

  (* Coloration des régions *)
  let colors = get_colors cl in
  let cell_width = voronoi_width / (Array.length colors + 1) in
  set_color white;
  fill_rect 0 voronoi_height cell_width margin_top;
  Array.iteri (fun i c ->
      set_color c;
      fill_rect ((i+1) * cell_width) voronoi_height cell_width margin_top)
    colors;
  set_color black;
  moveto 0 voronoi_height;
  lineto voronoi_width voronoi_height;

  (* Arrière-plan droit *)
  let bkgd_color = rgb 197 188 142 in
  set_color bkgd_color;
  fill_rect voronoi_width 0 margin_right (voronoi_height + margin_top);
  set_color black;
  moveto voronoi_width 0;
  lineto voronoi_width (voronoi_height + margin_top);

  (* Boutons *)
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
    set_color bkgd_color;
    fill_rect btn.x btn.y btn.w btn.h
  in

  let draw_btn_txt btn txt =
    let txt = if txt = "" then btn.txt else btn.txt ^ txt in
    let txtw, txth = text_size txt in
    moveto (btn.x + btn.w / 2 - txtw / 2) (btn.y + btn.h / 2 - txth / 2);
    set_color black;
    draw_string txt;
  in

  let draw_btn btn =
    erase_btn btn;
    set_color btn_color;
    fill_rect btn.x btn.y btn.w btn.h;
    set_color black;
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
  if has_prev then draw_btn prev_btn;
  if has_next then draw_btn next_btn;
  draw_btn quit_btn;
  draw_dist_btn ();

  (* Cercle avec la couleur du point courant *)
  let draw_color_circle () =
    let x, y, r = voronoi_width + margin_right / 2,
                  voronoi_height + margin_top / 2,
                  margin_top / 2 - btn_margin_y in
    set_color !c;
    fill_circle x y r;
    set_color black;
    draw_circle x y r
  in
  draw_color_circle ();


  (* Boucle de jeu *)
  while !state = Play do
    synchronize ();
    let e = wait_next_event[Button_down; Key_pressed] in
    let x, y = e.mouse_x, e.mouse_y in

    if e.keypressed then begin
      if e.key = Char.chr 27 then
        state := Quit
      else if !distance <> int_of_char e.key - int_of_char '0' - 1 &&
              compare e.key '1' >= 0 &&
              compare e.key (char_of_int (int_of_char '0' + ndistances)) <= 0
      then begin
        reset_voronoi cl v;
        distance := int_of_char e.key - int_of_char '0' - 1;
        m := regions_voronoi distances.(!distance) v;
        b := adjacences_voronoi v !m;
        fnc := produce_constraints cl !b;
        z := 0;
        erase_btn bravo_btn;
        draw_dist_btn ();
        draw_voronoi v !m;
        if !graph_drawn then draw_graph v !b
      end
      else if e.key = 'g' then begin
        graph_drawn := not !graph_drawn;
        if !graph_drawn then draw_graph v !b else draw_voronoi v !m
      end
    end
    else if e.button then begin
      if has_clicked solve_btn e then begin
        let fnc' = ref !fnc in
        Array.iteri (fun i s ->
             if s.c <> None then
              fnc' := [(true, {Variables.i = i; c = get s.c})] :: !fnc')
          v.seeds;
        match Sat.solve (!fnc') with
        | Some valuation ->
          color_from_valuation v valuation;
          z := Array.length cl - ncl;
          draw_voronoi v !m
        | None -> ()
      end
      else if has_clicked reset_btn e then begin
        reset_voronoi cl v;
        z := 0;
        draw_voronoi v !m;
        erase_btn bravo_btn
      end
      else if has_clicked quit_btn e then
        state := Quit
      else if has_next && has_clicked next_btn e then begin
        reset_voronoi cl v;
        state := Next
      end
      else if has_prev && has_clicked prev_btn e then begin
        reset_voronoi cl v;
        state := Previous
      end
      else if x < fst v.dim && y > snd v.dim + 1 then begin
        c := point_color x y;
        draw_color_circle ()
      end
      else if x < fst v.dim && y < snd v.dim then begin
        let i = !m.(x).(y) in
        if cl.(i) = None then begin
          if !c <> white && v.seeds.(i).c = None then incr z else
          if !c = white && v.seeds.(i).c <> None && !z > 0 then decr z;
          v.seeds.(i) <- {c = if !c = white then None else Some !c;
                          x = v.seeds.(i).x; y = v.seeds.(i).y};
          draw_voronoi v !m;

          if !z = Array.length cl - ncl then begin
            let fnc' = ref !fnc in
            Array.iteri (fun i s ->
                if cl.(i) = None then
                  fnc' := [(true, {Variables.i = i; c = get s.c})] :: !fnc')
              v.seeds;
            if Sat.solve (!fnc') <> None then draw_bravo_btn ()
            else erase_btn bravo_btn
          end else erase_btn bravo_btn
        end
      end
    end
  done;
  !state;;

(** Fonction principale *)
let main () =
  open_graph (" 1x1");
  clear_graph ();
  auto_synchronize false;

  (* Permet de choisir le graphe à colorer *)
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
