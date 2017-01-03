# Voronoï

Antonin Décimo & Anya Zibulski

```sh
make    # make a native code executable
./project.native
```

Pour ajouter de nouveaux exemples, remplacer le fichier `src/examples.ml` et
ajouter une liste contenant tous les `voronoi` comme suivant :

```ocaml
(* src/examples.ml *)
let v1 = { ... };;
let v2 = { ... };;
let v3 = { ... };;
let v4 = { ... };;

let voronois = [v1; v2; v3; v4];;
```
