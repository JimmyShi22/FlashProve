-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PtGet.lean: place j of a sumcheck's point.

It imports the library alone (Cb/Ld/LdPscVars.lean).

A sumcheck's point (`PPt l`, Cb/Ld/LdPsc.lean) is a nested tuple with one element for each variable
of the list l, in the order of the rounds.
Main names:
  `ppGet l γ j`   place j of the point γ; 0 from the length of l on.
  `hFnOf_get`     for k variables of one format and one further variable: the library's reader
                  `hFnOf` behind `hInit` reads place j of the point.
Both restate texts of a file that is not in this library.
Limits: nothing on which challenge stands at a place.

-/
import Cb.Ld.LdPscVars

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop Hiop Prob Cb

variable {E : Type} [Field E]

/-- Place j of a point. -/
def ppGet : (l : List (PFmt E)) → PPt l → ℕ → E
  | [], _, _ => 0
  | _ :: _, γ, 0 => γ.1
  | _ :: l, γ, j + 1 => ppGet l γ.2 j

/-- `hFnOf` behind `hInit` reads place j of the point. -/
theorem hFnOf_get (f g : PFmt E) (e : PDat E g) : ∀ (k : ℕ) (d : PDats (List.replicate k f))
    (γ : PPt (List.replicate k f ++ [g])) (j : Fin k),
    hFnOf f k d (hInit (List.replicate k f) d g e
      (pH (List.replicate k f ++ [g]) (PDats.snoc (List.replicate k f) d g e) γ)) j =
      ppGet (List.replicate k f ++ [g]) γ j
  | 0, _, _, j => j.elim0
  | k + 1, d, γ, j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact hFnOf_get f g e k d.2 γ.2 i

end Lk6

#print axioms Lk6.hFnOf_get
