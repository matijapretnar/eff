open CoreUtils

module SkelEff = SkelEffSyntax
module Multicore = MulticoreSyntax

(* Abstractions *)
let rec of_abstraction (p, c) = (of_pattern p, of_computation c)

and of_abstraction2 (p1, p2, c) =
  (of_pattern p1, of_pattern p2, of_computation c)

(* Patterns *)
and of_pattern = function
  | SkelEff.PEVar v -> Multicore.PVar v
  | SkelEff.PEAs (p, v) -> Multicore.PAs (of_pattern p, v)
  | SkelEff.PETuple ps -> Multicore.PTuple (List.map of_pattern ps)
  | SkelEff.PERecord ass -> Multicore.PRecord (Assoc.map of_pattern assoc)
  | SkelEff.PEVariant (l, p) -> (
    match p with
    | None -> Multicore.PVariant (l, None)
    | Some p -> Multicore.PVariant (l, Some (of_pattern p))
    )
  | SkelEff.PEConst c -> Multicore.PConst c
  | SkelEff.PENonbinding -> Multicore.PNonbinding
