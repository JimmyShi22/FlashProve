-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/ViewNumbers.lean: the kind "lookup" (K3): the key levels v and the table's
levels d of a lookup's shape at the library's written calls (`callsW`,
Johnson/AtFull/Desc/Lots/K3Written.lean), as a written table of five pairs; and so, under the
library's six statements at a site's link, the site's three numbers, written. One definition; closed
facts by evaluation in Lean's kernel, on written data alone; two theorems.

What is defined and shown.
  `vdW`: the written table, by the sort of the link (0, 2: layers; 1: attention; 3: the output head)
  and the sort of the lookup. `vd_written`: at the four sorts of link and both sorts of lookup
  `shapeOwn` returns at the written calls and the cap 28, and its shape's pair (v, d) is the
  table's. By Lean's kernel. `vd_bent`: a negative test: with the table's v raised by one the
  comparison fails at each of the eight. `sortOf_lt`: a link's sort is below 4. `site_numbers`:
  under `SixAt Z.p.X s.link`: s.p.first, s.shape.v and s.shape.d are `firstW` and the table's two
  numbers at the site's link and sort.

Hypotheses that remain. In `site_numbers`: `hs`, `h6`, as in SiteOfView.lean. The others have none.


Limits. `vdW` has catch-all arms: at a first argument from 4 on it says (27, 11) and (30, 19), and
nothing is claimed there. The closed facts have been checked by Lean's own kernel alone. Numbers on
public data.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.SiteOfView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc.First.Look (shapeOwn)
open Johnson.AtFull.Lots.K3 (sortOf callsW firstW)
open Johnson.AtFull.K3X (SixAt)

/-- The key levels and the table's levels at a sort of link (0, 2: layers; 1: attention; 3: the
head) and a sort of lookup (true: on the digits), written. -/
def vdW : Nat → Bool → Nat × Nat
  | 1, true => (26, 11)
  | _, true => (27, 11)
  | 1, false => (29, 18)
  | 3, false => (31, 19)
  | _, false => (30, 19)

/-- At the written calls `shapeOwn` returns, and its shape's two numbers are the table's. -/
theorem vd_written : (List.range 4).all (fun σ => [false, true].all fun d =>
    (shapeOwn (callsW σ d) 28).map (fun h => (h.v, h.d)) == some (vdW σ d)) = true := by
  decide +kernel

/-- BENT: with each written number of key levels raised by one the comparison fails, at every sort.
-/
theorem vd_bent : (List.range 4).any (fun σ => [false, true].any fun d =>
    (shapeOwn (callsW σ d) 28).map (fun h => (h.v, h.d)) ==
      some ((vdW σ d).1 + 1, (vdW σ d).2)) = false := by
  decide +kernel

/-- A link's sort is below 4. -/
theorem sortOf_lt (i : Nat) : sortOf i < 4 := by
  unfold Johnson.AtFull.Lots.K3.sortOf
  split_ifs <;> omega

/-- **So, under the six statements at the site's link: the three numbers, written.** -/
theorem site_numbers (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (h6 : SixAt Z.p.X s.link) :
    s.p.first = firstW (sortOf s.link) s.digits ∧ s.shape.v = (vdW (sortOf s.link) s.digits).1 ∧
      s.shape.d = (vdW (sortOf s.link) s.digits).2 := by
  obtain ⟨h1, h2⟩ := site_of_view Z s hs h6
  have hw := List.all_eq_true.1
    (List.all_eq_true.1 vd_written (sortOf s.link) (List.mem_range.2 (sortOf_lt _))) s.digits
    (by cases s.digits <;> simp)
  have hw' := beq_iff_eq.1 hw
  rw [h2] at hw'
  have e := Option.some.inj hw'
  exact ⟨h1, congrArg Prod.fst e, congrArg Prod.snd e⟩

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.vd_written
#print axioms AtFullSide.Honest.K3.vd_bent
#print axioms AtFullSide.Honest.K3.sortOf_lt
#print axioms AtFullSide.Honest.K3.site_numbers
