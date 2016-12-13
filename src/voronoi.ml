open Graphics;;

type seed = {c : color option; x : int; y : int};;
type voronoi = {dim: int * int; seeds : seed array};;
