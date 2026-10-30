-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Order/TwList.lean.
The challenges of a sumcheck as a list.

A sumcheck's out-statement holds its challenges in the field pt, a nested pair (`PPt l`,
Cb/Ld/LdPsc.lean) that follows the list l of formats.
Main names:
  `ppList`: pt as a list, in the order of the rounds; `ppList_length`. Where the sumcheck has a
    further variable behind its cube's variables (the library's dummy, `pDummy`), its format is the
    list's last (that its challenge is the last member: `hLast_list`, Cb/Pv/Lookup/Alg/TwGen.lean).
  `hFnOf_list`, `hFnMix_list`: the two readers of a cube's variables (hFnOf behind hInit; hFnMix,
    Cb/Pv/Lookup/Blocks/EndM.lean) read place j of the list.
  `ppList_pG`: one step of ppList on the challenges of a transcript's rounds (`pG`).
Not claimed: that the field pt of a verifier's out-statement holds the transcript's challenges.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Blocks.EndM

set_option autoImplicit false

namespace Cb.Tw
open Iop Hiop Prob

section
variable {E : Type}

/-- the field pt of a sumcheck's out-statement, as the list of its challenges in the order of the
rounds -/
def ppList : (l : List (PFmt E)) → PPt l → List E
  | [], _ => []
  | _ :: l, γ => γ.1 :: ppList l γ.2

theorem ppList_length : ∀ (l : List (PFmt E)) (γ : PPt l), (ppList l γ).length = l.length
  | [], _ => rfl
  | _ :: l, γ => congrArg (· + 1) (ppList_length l γ.2)

variable [Field E]

theorem ppList_pG (f : PFmt E) (l : List (PFmt E)) (ρ : Rho (pRounds (f :: l))) :
    ppList (f :: l) (pG (f :: l) ρ) = f.val ρ.1 :: ppList l (pG l ρ.2) := rfl

/-- the library's reader of a cube's variables, after the further variable is cut off, reads place j
of the list -/
theorem hFnOf_list (f g : PFmt E) (e : PDat E g) : ∀ (k : ℕ) (d : PDats (List.replicate k f))
    (γ : PPt (List.replicate k f ++ [g])) (j : Fin k),
    hFnOf f k d (hInit (List.replicate k f) d g e
      (pH (List.replicate k f ++ [g]) (PDats.snoc (List.replicate k f) d g e) γ)) j =
      (ppList (List.replicate k f ++ [g]) γ).getD j 0
  | 0, _, _, j => j.elim0
  | k + 1, d, γ, j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact hFnOf_list f g e k d.2 γ.2 i

/-- the like for a cube with a degree for each variable (no further variable) -/
theorem hFnMix_list [Fintype E] : ∀ (k : ℕ) (dg : Fin k → ℕ) (d : PDats (pfMix E k dg)) (γ : PPt
    (pfMix E k dg)) (j : Fin k),
    hFnMix E k dg d (pH (pfMix E k dg) d γ) j = (ppList (pfMix E k dg) γ).getD j 0
  | 0, _, _, _, j => j.elim0
  | k + 1, dg, d, γ, j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact hFnMix_list k (fun i => dg i.succ) d.2 γ.2 i

end
end Cb.Tw
