-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/Ent4Rows.lean: THE SMALLNESS TEST: THE ENTRIES OF VIRTUAL ROWS AT WHICH THE
LIBRARY VALUES THE FIRST FOUR CLAIMS OF THE RUN "K8.equations" OFF WHAT IS FIXED IN FRONT OF THE
BATCHING's DRAW (`LinkJoin.ent4`, Johnson/Desc/First/Link/Law/FullFour.lean) MEET THE LIBRARY's LAW
OF THE ROWS (`Fo.RowsLaw`, OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean) AT THE LEDGER IN WHICH THE
ROUTINE THAT LAYS THE WEIGHTS HAS RUN ON THE SNAPSHOT's OWN LEDGER: by unfolding. NO STATE BEHIND
THE DRAW IS NAMED. Lemmas on the library's own definitions; none of its goals.

  **`rowsLaw_ent4`**   (π q.1).1 = some tlb → q.2 = some v → tlb.heard = some g → at every reading
                   of the slots: RowsLaw Reading.gl (coefAll tlb g v.F) ⟨slot, ent4 π q y⟩ (entUnit
                   q y)
  `virt_bz_ent4`   so the three virtual rows of the array of planes are the combinations that the
                   library's `Fo.virt_bz` names, of the data's cells
  `virt_piece_ent4`   and each piece's virtual row, by `Fo.virt_piece`
Limits. At the data of the test AS WHAT IS FIXED SHOWS THEM (the fourteen written fields blanked).
The premises of the two corollaries on the snapshot's ledger (`Fo.CoefOK`; the pieces' rows lie
within the array) are the library's promise in front of the draw: not paid here. Nothing on what the
cells are.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.Link.Law.FullFour
import OnBytes.Tie.Pv.Lookup.Ends.FoRowsLaw
import OnBytes.Tie.Pv.Lookup.Ends.FoTailLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open VerifiableInference.Desc.K9L (Pub9 Bound GE8)
open VerifiableInference.Desc.LinkJoin (ent4 n4 w4)
open VerifiableInference.Desc.EntryUnit (entBy entUnit)
open _root_.Fo FoNums

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **The entries meet the law of the rows at the snapshot's own ledger, the weights laid.** -/
theorem rowsLaw_ent4 (q : α × Option Pub9) (y : Bound GE8) {tlb : HTailF2} {v : Pub9}
    {g : Forest.Heard} (h1 : (π q.1).1 = some tlb) (h2 : q.2 = some v) (hg : tlb.heard = some g)
    (slot : Nat → GE8) :
    RowsLaw Reading.gl (coefAll tlb g v.F) ⟨slot, ent4 π q y⟩ (entUnit q y) := by
  intro t e i _
  show entBy Reading.gl n4 (w4 π) q y t e i = _
  unfold entBy
  have hn : n4 q t = ((coefAll tlb g v.F).trees.getD t {}).R := by
    rw [((frame_all tlb g v.F).2 t).1]
    simp [n4, h2]
  rw [hn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : w4 π q t e j = (rowAt (coefAll tlb g v.F) t e).coef.getD j zeroE := by
    simp [w4, h1, h2, hg]
  rw [hw]

/-- So the three virtual rows of the array of planes. -/
theorem virt_bz_ent4 (q : α × Option Pub9) (y : Bound GE8) {tlb : HTailF2} {v : Pub9}
    {g : Forest.Heard} (h1 : (π q.1).1 = some tlb) (h2 : q.2 = some v) (hg : tlb.heard = some g)
    (T : CoefOK tlb v.F) (n : Nat) :
    VirtRow (ent4 π q y) tlb.ix.BZ 0
        (fun r => (eqTabK ((rdL Reading.gl g.zb0).take 5)).getD r 0)
        (entUnit q y tlb.ix.BZ) 32 n ∧
      VirtRow (ent4 π q y) tlb.ix.BZ 1
        (fun r => (eqTabK ((rdL Reading.gl g.zb1).take 5)).getD r 0)
        (entUnit q y tlb.ix.BZ) 32 n ∧
      VirtRow (ent4 π q y) tlb.ix.BZ 2 (fun _ => 1) (entUnit q y tlb.ix.BZ) 32 n :=
  virt_bz Reading.gl tlb g v.F T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR ⟨fun _ => 0, ent4 π q y⟩
    (entUnit q y) (rowsLaw_ent4 π q y h1 h2 hg fun _ => 0) _ _ rfl rfl n

/-- And each piece's virtual row. -/
theorem virt_piece_ent4 (q : α × Option Pub9) (y : Bound GE8) {tlb : HTailF2} {v : Pub9}
    {g : Forest.Heard} (h1 : (π q.1).1 = some tlb) (h2 : q.2 = some v) (hg : tlb.heard = some g)
    (T : CoefOK tlb v.F) (a : Nat × Piece) (ha : a ∈ allPieces tlb)
    (hR : a.2.r0 + a.2.Rp ≤ (v.F.trees.getD a.2.tree {}).R) (i : Nat) :
    ent4 π q y a.2.tree a.2.row i = ∑ r ∈ Finset.range a.2.Rp,
      (eqTabK (exL (rdL Reading.gl (g.zk.getD a.1 #[]))
        ((tlb.zOf a.1).call.n - a.2.b) ((tlb.zOf a.1).call.n - a.2.b + a.2.a))).getD r 0 *
          entUnit q y a.2.tree (a.2.r0 + r) i :=
  virt_piece Reading.gl tlb g v.F T a ha hR ⟨fun _ => 0, ent4 π q y⟩ (entUnit q y)
    (rowsLaw_ent4 π q y h1 h2 hg fun _ => 0) i

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.rowsLaw_ent4
#print axioms VerifiableInference.Desc.First.K8.Honest.virt_bz_ent4
#print axioms VerifiableInference.Desc.First.K8.Honest.virt_piece_ent4
