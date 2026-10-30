--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Says3.lean: what group 7 and two claims of group 14 of the layers' own rounds say,
by the library's theorems on the second token sumcheck and the batched sumcheck.

Johnson/Road/Rows/LayerEnds34.lean and LayerEnds3S.lean name, in a public record Pub34, the
statements on both sides of these two sumchecks, and prove what each comes to on cells. Here two of
these theorems are laid at K4's own lists (OnBytes/Desc/First/K4/Claims.lean).

  `terms_says` (group 7): on true reads, if every form of K4's group 7 is worth 0, each hidden end
      value of the second token sumcheck is the true contraction (the library's EndsL3).
  `back_says` (group 14, its second and third claim): if every form of K4's list `back` is worth 0,
      and the merge and the product layers have shown what they are there to show (the library's
      Merged and Gated), the two factors of the batched sumcheck's summand, on the hidden end
      values, are the extensions of the two long vectors at the end point (the library's MapsL4).

Limits. Implications in one world: no draw, no soundness. The record Pub34 is a premise with many
public fields; BY ITS OWN FILE's HEAD NONE EXISTS AT THE SMALL EXAMPLE (its field hfl fails there),
and nothing here builds one at the full size. Merged and Gated are premises. That the record's
letters are K4's (three equations; one on the token sumcheck) is asked as premises. No theorem on a
run of `verify-on-bytes` is called.
-/
import Johnson.Road.K4.ListsTie2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own)

variable {K : Type} [Field K]

/-- Group 7. -/
theorem terms_says (X : Rows.Pub34 K) {H : Heard} (hT : H.tT = some X.tT)
    (hp : X.p.v.y.h.p3 = true) (Wo : World K) (Mm : Mats K) (hh : ℕ → ℕ → K) {l : List Aff}
    (hRd : X.ReadsTrue Wo Mm) (h : Desc.First.K4.termsForms X.p.v H = some l)
    (hz : ∀ f ∈ l, f.value X.ρ Wo = 0) : X.EndsL3 Wo Mm hh :=
  Rows.l3EndShown X Wo Mm hh l hRd (termsForms_termsL hT hp h) hz

/-- Group 14, the second and the third claim. -/
theorem back_says (X : Rows.Pub34 K) {o : Own} {rowM : Aff} (hA : X.sA0 = o.K.sA0)
    (hB : X.sB0 = o.K.sB0) (hf : X.fin = o.K.fin) (Wo : World K) (M : Wm K) (hh : ℕ → ℕ → K)
    (hz : ∀ f ∈ Desc.First.K4.back o rowM, f.value X.ρ Wo = 0) (hM : X.Merged Wo M)
    (hG : X.Gated Wo hh) : X.MapsL4 Wo M hh := by
  refine Rows.l4EndOut X Wo M hh (fun f hf' => hz f ?_) hM hG
  unfold Rows.Pub34.sideClaims at hf'
  rw [hA, hB, hf] at hf'
  unfold Desc.First.K4.back
  rcases List.mem_cons.mp hf' with rfl | hf'
  · simp
  · rcases List.mem_cons.mp hf' with rfl | hf'
    · simp
    · cases hf'

#print axioms terms_says
#print axioms back_says

end OnBytes.Road.K4
