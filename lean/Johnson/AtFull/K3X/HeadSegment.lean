-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/HeadSegment.lean: the six statements that the two lookups of the output head's
link ask of the public data (SixAt X 24, Johnson/AtFull/K3X/SixAt.lean) hold at every public part
whose head's parts are the full size's. A join: calls alone.

  **seg24**: X has profile 4 and twelve groups; its head's shape is the written one (Cond.hFull);
    its head's layout is one that Head.layout returns there (LaidW,
    Johnson/AtFull/Head/LayoutAtFull.lean); its head's plan is the written plan HW with the rows'
    weights trimmed; the weights' matrix has 2^18 columns ⊢ SixAt X 24.
  The theorem on the public part's maker at the library's written copy of the full-size public files
  (publicOfO_zFull_of_rest, Johnson/AtFull/Public/Join.lean) names the parts of its value so that
  the first five premises follow by short steps; that join is not made here. The last premise is
  paid at the makers in Johnson/AtFull/K3X/HeadLk.lean.
  callsHead_written, pubHead_written: the written calls and counts of the head's lookup stand under
    two names, here and in the file on the head's row (Johnson/AtFull/ProofRows/K3HeadRow.lean):
    they are one value, by definition.
  **head_two**: at a layout that Head.layout returns at the full size: its six calls, their tables
    taken out, are callsHead, and its nine counts of padding keys are pubHead: the two equations
    that the proof file's entry test on the head's lookup is paid from.
Who pays what. The nine counts: laid_pub (a closed form and two kernel facts). The host's count:
laidHead_W (a law over the same closed form). The calls, the plan's numbers, the names: three closed
facts proved by evaluation in Lean's kernel (Johnson/AtFull/K3X/HeadKernel.lean).

Limits. The full size, at the stored free numbers alone: at the library's second written set of
public files (VerifierAndGoals.zGap), whose acceptance policy is another, the head's shape is not Cond.hFull:
seg24's third premise fails there. The premises are premises here. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.K3X.HeadLaidAtFull
import Johnson.AtFull.K3X.HeadKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open _root_.AtFull.Head (LaidW HW withLaid_true laid_pub pubNine)

/-- **The six at the output head's link, at the full size's head.** -/
theorem seg24 {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) (hS : X.hS = Cond.hFull)
    (hL : LaidW (.ok X.HLy)) (hH : X.H = { HW with Fp := HW.Fp.trimL })
    (hk : X.layers.wsLay.lk = 18) : SixAt X 24 := by
  obtain ⟨A, eA, c0⟩ := withLaid_true headCalls_W _ hL
  obtain ⟨B, eB, p0⟩ := laid_pub hL
  obtain ⟨C, eC, q0⟩ := laidHead_W hL
  rw [← Except.ok.inj eA] at c0
  rw [← Except.ok.inj eB] at p0
  rw [← Except.ok.inj eC] at q0
  refine six_head h4 hN names_head_W (by rw [hS]; rfl) (by rw [hS]; rfl) c0
    (p0.trans pubNine_written) (by rw [hS]; exact q0.trans (congrArg some pubNine_written)) hk ?_
  rw [hH]
  exact headTail_HW

/-- The written calls of the head's lookup stand under two names. -/
theorem callsHead_written : Lots.K3.callsW 3 false = ProofRows.K3.callsHead := rfl

/-- And so do the nine counts. -/
theorem pubHead_written : pubNine = ProofRows.K3.pubHead := rfl

/-- **The head's calls and counts at what the head's layout returns.** -/
theorem head_two {X : Verify.Public} (hL : LaidW (.ok X.HLy)) :
    X.HLy.cl.map ProofRows.K3.strip = ProofRows.K3.callsHead ∧
      X.HLy.fs.pub = ProofRows.K3.pubHead := by
  obtain ⟨A, eA, c0⟩ := withLaid_true headCalls_W _ hL
  obtain ⟨B, eB, p0⟩ := laid_pub hL
  rw [← Except.ok.inj eA] at c0
  rw [← Except.ok.inj eB] at p0
  exact ⟨(Array.toList_inj.1 (sameList_eq c0)).trans callsHead_written, p0.trans pubHead_written⟩

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.seg24
#print axioms Johnson.AtFull.K3X.callsHead_written
#print axioms Johnson.AtFull.K3X.pubHead_written
#print axioms Johnson.AtFull.K3X.head_two
