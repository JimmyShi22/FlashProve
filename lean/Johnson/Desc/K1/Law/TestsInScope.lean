-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TestsInScope.lean: two of the tests
with code that hpub_point (HpubPointwise.lean) takes as premises ACCEPT at the full size's
written shape, at ANY table's numbers: so these two premises fall to three equations on letters.
  `cntAt shape l t`   how many messages of link l the shape has at moment t
  `own_size`, `dS_own_size`   the data's list "own" of a segment has `cntAt shape l 0` entries, by
                   the make of `sentDataOf` (First/FillSent.lean)
  `sent_size`      a later moment's place sends `cntAt q.shape l t` messages, by the make of
                   `parLater` (K1/Places.lean)
  `secondAt_full`  [kernel] `secondAtB` at `shapeFull`, at these two counts, at the 25 links
  `hAt_scope`      **hpub_point's hAt**
  `findReads_full`   [kernel] in the written list of places, the first place of link l at piece
                   4 + the segment's shift is the place number 14 l + k1Ix l false + 2
  `hOwn1_scope`    **hpub_point's hOwn1** (`own1B`, HpubAtPlus13.lean)
  `scopeTests_fail`   [kernel] both kernel facts' tests can fail
PREMISES: hD : Dm.shape = shapeFull · hs : G.first.shape = shapeFull (k01_fifty's own hs) · hlk :
Dm.links = linksFull. CAN THEY BE MET? hD, hlk: `MgData` and `PubData0` (Sound/MgAll.lean,
First/PubAll.lean) have no field that is a proof, and no other field's type names
`shape` or `links`: the two are free. No `Dm` is written out here. hs: it is k01_fifty's own
premise; whether `ProofFile.Ground` lets `first.shape` be set freely has not been read for this file.
The recursion limit is raised in this file (maxRecDepth 1000000), as in FormsAtFifty.lean:
for the elaboration of the kernel's evaluations alone.
What is not claimed. That the release's own files give that shape. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HpubPointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf shift)
open VerifiableInference.Desc.First.FillSent (SentData sentDataOf secondNos base1At TreeLook)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ)
open VerifiableInference.Desc.ReqLit (shapeFull)
open IM (k1Ix)

/-- How many messages of link l the shape has at moment t. -/
def cntAt (shape : Params.ReqShape) (l t : ℕ) : ℕ :=
  (((shape.link[l]?.map (·.messages)).getD []).filter fun x => x.moment == t).length

theorem own_size (shape : Params.ReqShape) (base : ℕ → ℕ) (trees : ℕ → List TreeLook) (m : ℕ) :
    ((sentDataOf shape base trees).own m).size = cntAt shape m 0 := by
  simp [sentDataOf, cntAt]

theorem sent_size (q : Params.First) (gp : _root_.Desc.Plain.GPar) (l piece t : ℕ) :
    (parLater q gp l piece t).sent.size = cntAt q.shape l t := by
  simp [Par.sent, parLater, noticesAt, ReqFrame.notices, ReqFrame.atMoment, cntAt]

theorem secondAt_full : ((List.range 25).all fun l =>
    secondAtB shapeFull l (cntAt shapeFull l 0) (cntAt shapeFull l 1)) = true := by
  decide +kernel

theorem findReads_full : ((List.range 25).all fun l =>
    decide (((flatPlacesOf linksFull true).find? fun p =>
        p.link == some l && p.piece == 4 + ((linksFull[l]?).map shift).getD 0) =
      (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?)) = true := by
  decide +kernel

/-- **The tests can fail**: with no room for the second sending's messages; and the place one
further on is another. -/
theorem scopeTests_fail :
    secondAtB shapeFull 3 (cntAt shapeFull 3 0) 0 = false ∧
    decide (((flatPlacesOf linksFull true).find? fun p =>
        p.link == some 3 && p.piece == 4 + ((linksFull[3]?).map shift).getD 0) =
      (flatPlacesOf linksFull true)[14 * 3 + k1Ix 3 false + 3]?) = false := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV)

theorem dS_own_size (l : ℕ) : (Dm.pubD.dS.own l).size = cntAt Dm.shape l 0 :=
  own_size Dm.shape _ _ l

/-- **hpub_point's hAt**, in scope. -/
theorem hAt_scope (hD : Dm.shape = shapeFull) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hs : G.first.shape = shapeFull) : ∀ l, l < 25 →
    secondAtB Dm.shape l (Dm.pubD.dS.own l).size (parL Z G l false).sent.size = true := by
  intro l hl
  have e : (parL Z G l false).sent.size = cntAt G.first.shape l 1 :=
    sent_size G.first (gpOf Z) l (k1Ix l false + 1) 1
  rw [dS_own_size, e, hD, hs]
  exact List.all_eq_true.1 secondAt_full l (List.mem_range.2 hl)

/-- **hpub_point's hOwn1**, in scope, at any table's numbers. -/
theorem hOwn1_scope (hD : Dm.shape = shapeFull) (hlk : Dm.links = linksFull) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (hs : G.first.shape = shapeFull) :
    own1B Dm.shape Dm.N Dm.links Z G = true := by
  unfold own1B
  rw [List.all_eq_true]
  intro l hl
  have hl' := List.mem_range.1 hl
  have e : (parL Z G l false).sent.size = cntAt G.first.shape l 1 :=
    sent_size G.first (gpOf Z) l (k1Ix l false + 1) 1
  have hf := of_decide_eq_true (List.all_eq_true.1 findReads_full l hl)
  rw [beq_iff_eq, hlk]
  unfold secondNos base1At idsOf
  rw [hf, e, hD, hs]
  all_goals rfl

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.secondAt_full
#print axioms VerifiableInference.Desc.K1.findReads_full
#print axioms VerifiableInference.Desc.K1.scopeTests_fail
#print axioms VerifiableInference.Desc.K1.hAt_scope
#print axioms VerifiableInference.Desc.K1.hOwn1_scope
