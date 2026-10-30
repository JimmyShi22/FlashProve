-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K13LotRows.lean: THE ROWS OF K13's THREE LOTS AT THE FULL SIZE: closed
facts by Lean's kernel AGAINST THE WRITTEN TABLE ITSELF (cutFirstFull, rows 355 · 356 · 357, by
sameRow), each with negative tests stated "= false"; then the rows under hypotheses by field.
  m3_written · m3_rejects     82 roots in front · the plan's test passes · 18 columns · row 355
  skM4Full · m4_written · m4_rejects   the lot returns a sub-protocol; its skeleton is the one
                              written out; the own group is 31; row 356
  m5_written                  there is a last round but one, it owes no row; row 357; two negatives
  **lot_row · lot4_row · lotEnd_row**   lotSk G L = ‹plain data›
  weaker_of_written           lot_row's hk and lot4_row's hg from FirstWritten's equations
  lots_steady                 ProofFile.Sk.steady_none applies to all three
THE HYPOTHESES, BY FIELD: hc : Z.cuts = cutWritten · he : Z.D.1.map (·.entry) = esWritten (as in
Johnson/AtFull/K4Sent/LotSkel.lean) · hk : Z.first.lin.kCol = 18 · hr : Z.first.pendingRows = 13 ·
hcd · hl : codes and lin are proofSizedFull's · hg : K1.ownGroup Z.first = 31.
THEY ARE TO BE PAID WITHOUT THE ENTRY TESTS' COMPARISONS (the first comparison's accept; cutIs):
these rows serve to show those; a proof that takes one of them as a premise would close a circle
that Lean does not see.
Skel.row HOLDS SIX FIELDS: it drops planOk, claims and after. "The row is the written one" says
nothing of the test on the plan: that is stated beside, in the skeleton's own field (true).
Limits. That the front's value has hc … hg is not shown here. The name column is set to the spot's
by hand ("M:3" · "M:4" · "seal:5"): that the seated sub-protocol bears it is not shown here.
Nothing on soundness.
The recursion limit is raised (maxRecDepth 1000000) at the kernel's facts, for elaboration.

-/
import Johnson.AtFull.Desc.Lots.K13LotSk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.LotRows
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (Cut)
open VerifiableInference.PlanWritten (cutFirstFull sameRow proofSizedFull)
open ProofFile (Pub Lot Ground)
open ProofFile.Sk (Skel skel LotSk lotSk toldFrom)
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.G

/-! ## The closed facts, by Lean's kernel, against the written table itself -/

set_option maxRecDepth 1000000 in
/-- **K13.lot at the written values.** -/
theorem m3_written : sentM3 cutWritten esWritten = 82 ∧ okM3 cutWritten 13 = true ∧
    proofSizedFull.batch.shape.kCol = 18 ∧
    (cutFirstFull[355]?).any (sameRow { skM3 18 82 true with name := "M:3" }.row) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **Negative tests**: one root fewer · one column fewer · no step of the name · one row in
the pile · the row in front. -/
theorem m3_rejects :
    (cutFirstFull[355]?).any (sameRow { skM3 18 81 true with name := "M:3" }.row) = false ∧
    (cutFirstFull[355]?).any (sameRow { skM3 17 82 true with name := "M:3" }.row) = false ∧
    okM3 [] 13 = false ∧ okM3 cutWritten 1 = false ∧
    (cutFirstFull[354]?).any (sameRow { skM3 18 82 true with name := "M:3" }.row) = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The skeleton of W's commitment at the full size, written out: one round tells one tree, of two
tenants; the first joins the request's own group, 31. -/
def skM4Full : Skel :=
  { name := "W's commitment, the own group and (Eval)", place := ⟨1, none, 4, .K1⟩, nRounds := 2
    nOracles := 2
    told := [(0, [⟨22, 12, [⟨3, 3, 3, true, [31]⟩, ⟨0, 6, 1, false, []⟩]⟩])], before := []
    planOk := true, claims := [], after := [] }

set_option maxRecDepth 1000000 in
/-- **K13.lot4 at the written values**: the lot returns a block, its test on the plan passes, and
its row is the written one. -/
theorem m4_written :
    skM4 proofSizedFull.codes proofSizedFull.batch.shape 31 = some skM4Full ∧
    proofSizedFull.request.link.length + proofSizedFull.request.last.length = 31 ∧
    (cutFirstFull[356]?).any (sameRow { skM4Full with name := "M:4" }.row) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **Negative tests**: another own group · the row in front. -/
theorem m4_rejects :
    (skM4 proofSizedFull.codes proofSizedFull.batch.shape 32 == some skM4Full) = false ∧
    (cutFirstFull[355]?).any (sameRow { skM4Full with name := "M:4" }.row) = false :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **K13.lotEnd at the written values**: there is a last round but one (so the yes is not the idle
one of an empty list), and it owes no row; with two negative tests: a last round but one that owes a
row · the row in front. -/
theorem m5_written : okM5 esWritten = true ∧ (esWritten.dropLast.getLast?).isSome = true ∧
    (cutFirstFull[357]?).any (sameRow { skM5 true with name := "seal:5" }.row) = true ∧
    okM5 [{ name := "a", rows := 1 }, { name := "b" }] = false ∧
    (cutFirstFull[356]?).any (sameRow { skM5 true with name := "seal:5" }.row) = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The rows, under hypotheses by field -/

/-- **K13.lot.** Of lin the number of columns alone is asked. -/
theorem lot_row {Z : Pub} (G : Ground) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) (hk : Z.first.lin.kCol = 18)
    (hr : Z.first.pendingRows = 13) :
    lotSk G (lot Z) = plainSk "K13: the members' batching" [skM3 18 82 true] := by
  rw [lot_sk, hc, he, hk, hr, m3_written.1, m3_written.2.1]

/-- **K13.lot4.** Of the shape the own group's number alone is asked. -/
theorem lot4_row {Z : Pub} (G : Ground) (hcd : Z.first.codes = proofSizedFull.codes)
    (hl : Z.first.lin = proofSizedFull.batch.shape) (hg : K1.ownGroup Z.first = 31) :
    lotSk G (lot4 Z) =
      plainSk "K1 and K13: W's commitment, the request's own group and the row (Eval)"
        [skM4Full] := by
  rw [lot4_sk, hcd, hl, hg, m4_written.1]
  rfl

/-- The two weaker premises, from the equations on the first chain's parameters as FirstWritten
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) states them. -/
theorem weaker_of_written {Z : Pub} (hl : Z.first.lin = proofSizedFull.batch.shape)
    (hs : Z.first.shape = proofSizedFull.request) :
    Z.first.lin.kCol = 18 ∧ K1.ownGroup Z.first = 31 := by
  refine ⟨by rw [hl]; exact m3_written.2.2.1, ?_⟩
  unfold K1.ownGroup
  rw [hs]
  exact m4_written.2.1

/-- **K13.lotEnd.** -/
theorem lotEnd_row {Z : Pub} (G : Ground) (he : Z.D.1.map (·.entry) = esWritten) :
    lotSk G (lotEnd Z) = plainSk "the end of the first chain" [skM5 true] := by
  rw [lotEnd_sk, he, m5_written.1]

/-- The three lots supply no batching: ProofFile.Sk.steady_none applies. -/
theorem lots_steady (Z : Pub) (G : Ground) :
    ProofFile.Sk.Steady G (lot Z) ∧ ProofFile.Sk.Steady G (lot4 Z) ∧ ProofFile.Sk.Steady G (lotEnd Z) :=
  ⟨ProofFile.Sk.steady_none G _ fun _ => rfl, ProofFile.Sk.steady_none G _ fun _ => rfl,
    ProofFile.Sk.steady_none G _ fun _ => rfl⟩

end VerifiableInference.Desc.K13.LotRows

#print axioms VerifiableInference.Desc.K13.LotRows.m3_written
#print axioms VerifiableInference.Desc.K13.LotRows.m3_rejects
#print axioms VerifiableInference.Desc.K13.LotRows.m4_written
#print axioms VerifiableInference.Desc.K13.LotRows.m4_rejects
#print axioms VerifiableInference.Desc.K13.LotRows.m5_written
#print axioms VerifiableInference.Desc.K13.LotRows.lot_row
#print axioms VerifiableInference.Desc.K13.LotRows.lot4_row
#print axioms VerifiableInference.Desc.K13.LotRows.lotEnd_row
#print axioms VerifiableInference.Desc.K13.LotRows.weaker_of_written
#print axioms VerifiableInference.Desc.K13.LotRows.lots_steady
