-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/HeadMatsLabels.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE HONEST SIDE's READING OF THE HEAD's MATRIX NUMBER a (`headMats`, Honest/K6/Wit.lean) IS THE CELL
THAT THE FORMAT's PACKING READS (`packedCells`, Johnson/HonestTrace/Packed.lean): the witness's
reader at segment 24 and the label of the matrix with the number a in the list of `Sz.ref`. Under
the hypothesis h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) and hG. No definition; two theorems.

  `k6_noAt_of_matAt`    under h: a number in Sz.ref's list of the head is the number at the public
                        files' own numbers of parts
  `k6_headMats_label`   the sentence above, at every reader C

By. `headMatNames_public` (Honest/K6/Cells/MatNames.lean); `k6_seg_at_head`
(Honest/K6/Law/GuestsOfTheTrace.lean); `ground_of_blank` (Honest/K6/Law/DebtsLess.lean); the
library's `planName_head_in_scope` (Johnson/Goal/HonestTrace/FullInScope.lean), `parts_at`,
`partsFit_in_scope`, `matAt_eq_some_iff`. The lines on names are those of `headCell_is_trace`
(Honest/K6/Cells/OfServed.lean), typed anew here: that file stands over a file that lies in no seal.

What it is not.
  * Names and numbers alone: nothing on a cell's value; C is a letter.
  * It says nothing of a borrowed matrix's OWNER: at the stream (number NHf + 3) both sides read the
    reader at segment 24 under the head's own name for it; the array that is sent is the owner's.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Cells.MatNames
import Johnson.Desc.ProofFile.Honest.K6.Law.GuestsOfTheTrace
import Johnson.Desc.ProofFile.Honest.K6.Law.DebtsLess
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.HonestTrace.Packed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.Model.Verify (borderOf)
open OnBytes.HonestTrace (Sz Seg MatName noAt planMats parts_at partsFit_in_scope
  matAt_eq_some_iff planName_head_in_scope)
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS At.X)
open ProofFile.Honest.K6 (headMats headMatNames headWhereOf headMatNames_public)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- CONDITIONAL: the hypothesis h. A number in Sz.ref's list of the head's segment is the name's
number at the public files' own numbers of parts. -/
theorem k6_noAt_of_matAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {a : ℕ} {μ : MatName}
    (hμ : Sz.ref.matAt 24 a = some (.head, μ)) : noAt (At.X Zp) .head μ = some a := by
  obtain ⟨-, -, hmu⟩ := (matAt_eq_some_iff Sz.ref 24 a .head μ).1 hμ
  have e : Sz.ref.mu .head μ = MatName.no? 3 1 1 4 .head μ := if_pos trivial
  exact ((parts_at (partsFit_in_scope h.scope h.reads h.pubOne) (k := Seg.no 12 .head)
    (σ := .head) (Seg.ofNo_no (G := 12) (σ := .head) trivial)).2.1 μ).trans (e.symm.trans hmu)

/-- CONDITIONAL: h; hG. **THE HONEST SIDE READS THE VERY CELL THAT THE PACKING READS**, at every
reader C. -/
theorem k6_headMats_label (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {a : ℕ} {μ : MatName}
    (hμ : Sz.ref.matAt 24 a = some (.head, μ)) (C : ProofFile.Honest.Cells) (rr c : ℕ) :
    headMats (headWhereOf Zp G) C a rr c = C.cell 24 μ.label rr c := by
  have hP := h.pubOne
  have hGW : G.W = At.X Zp := ground_of_blank hG
  have h1 : (headWhereOf Zp G).shape = (At.X Zp).hS := by
    show G.W.hS = _
    rw [hGW]
  have h2 : (headWhereOf Zp G).lay = (At.X Zp).HLy := by
    show G.W.HLy = _
    rw [hGW]
  have h3 : (headWhereOf Zp G).border = borderOf (At.X Zp).y := by
    show borderOf G.W.y = _
    rw [hGW]
  have ep : planMats (At.X Zp) 24 = (At.X Zp).H.tl.mats := by simp [planMats]
  have en : (headMatNames (headWhereOf Zp G)).getD a "" =
      ((planMats (At.X Zp) 24).getD a {}).name := by
    rw [headMatNames_public hP (headWhereOf Zp G) h1 h2 h3, ep]
    by_cases hs' : a < (At.X Zp).H.tl.mats.size
    · simp [Array.getD, hs']
    · simp [Array.getD, hs']
  show C.cell (headWhereOf Zp G).seg ((headMatNames (headWhereOf Zp G)).getD a "") rr c = _
  rw [k6_seg_at_head h hG, en,
    planName_head_in_scope h.scope h.reads hP (k6_noAt_of_matAt h hμ)]

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_noAt_of_matAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_headMats_label
