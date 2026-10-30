-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/MatNames.lean: the names under which the honest side of the
sub-protocol "the output head's own rounds" (K6) reads the head's matrices (`headMatNames`,
Honest/K6/Wit.lean) are the names of the public part's own list. Two lemmas. No goal is stated.

WHAT IT IS NOT. NAMES ALONE: nothing on what stands under a name. CONDITIONAL: the second lemma on a
return of the verifier's own function `publicOf` and on public numbers Nw with the public part's
shape, layout and border (h1, h2, h3): that any public files give such a return is not shown here.
The first has no premise. No scope, no thread, no run.

  `matsH_names`     the names of the plan's list of the head's matrices hang on neither of its two
                    identifiers
  `headMatNames_public`   **headMatNames Nw = X.H.tl.mats.map (·.name)**

Why. Whoever ties the honest side's reader of the cells to a reader by the plan's names wants this
step. The library has it inside a proof, under the public core (the step "em" of `entryH`,
Johnson/Goal/Meaning/HidPlanFit.lean); here it is had from `publicOf`'s return alone. Called:
`publicH_of_public` (Johnson/Road/HeadMade.lean), `planH2_label` (Johnson/Road/HeadSeg.lean).
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Road.HeadMade
import Johnson.Road.HeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Model.Verify (publicOf Public borderOf)

/-- The names of the plan's list of the head's matrices hang on neither of its two identifiers. -/
theorem matsH_names (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (g s g' s' : Nat) :
    (OnBytes.Model.Head.matsH h L b g s).map (·.name) =
      (OnBytes.Model.Head.matsH h L b g' s').map (·.name) := by
  unfold OnBytes.Model.Head.matsH
  simp [List.map_map, Function.comp_def]

/-- **THE NAMES UNDER WHICH THE HONEST SIDE READS THE HEAD's MATRICES ARE THE NAMES OF THE PUBLIC
PART's OWN LIST**: from the return of the verifier's own function alone. Nw: public numbers with the
public part's shape, layout and border. -/
theorem headMatNames_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (Nw : HeadWhere) (h1 : Nw.shape = X.hS) (h2 : Nw.lay = X.HLy)
    (h3 : Nw.border = borderOf X.y) : headMatNames Nw = X.H.tl.mats.map (·.name) := by
  obtain ⟨H0, hH, e⟩ := (OnBytes.Road.Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := OnBytes.Road.Hd.planH2_label hH
  have em : X.H.tl.mats = OnBytes.Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr)
      stream.aId := by
    rw [e]
    exact hm
  unfold headMatNames
  rw [h1, h2, h3, em]
  exact matsH_names _ _ _ _ _ _ _

#print axioms matsH_names
#print axioms headMatNames_public

end ProofFile.Honest.K6
