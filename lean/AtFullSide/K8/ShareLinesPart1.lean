-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/ShareLinesPart1.lean: the three fields of AtPublicFiles.TheFalls.ShareLines that the smallness test owes:
front, ledger and marksK8, in the fields' own words, from the bounds of AtFullSide/K8/SharesBound.lean and
AtFullSide/K8/SharesLedger.lean.

  small_of                   a positive denominator and a numerator that is small enough pass the test
  front_line, ledger_line, marks_line  the three fields

Limits. Under the library's head, at the blank ground. A stated number bounds no chance here. Nothing is
claimed on completeness, soundness or hiding.
-/
import E2E.TheFallsSum
import AtFullSide.K8.SharesLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open VerifiableInference.Desc (Chain KindName)
open AtPublicFiles.TheFalls (shareSmall markSmall ShareLines)
open ProofFile.Honest (Odds)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {G₀ : ProofFile.Ground}

theorem small_of {o : Odds} (h : 0 < o.den ∧ o.num * 2 ^ 109 ≤ o.den) : shareSmall o = true := by
  unfold shareSmall
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩

/-- The numbers stand at 2 ^ 124, which gives the test at 2 ^ 109. -/
theorem small_of_124 {o : Odds} (h : 0 < o.den ∧ o.num * 2 ^ 124 ≤ o.den) : shareSmall o = true :=
  small_of ⟨h.1, Nat.le_trans (Nat.mul_le_mul_left _ (by norm_num)) h.2⟩

/-- **The field front.** -/
theorem front_line (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) : ∀ l, l < 25 →
    shareSmall (ProofFile.Honest.K8.frontFallShare (ProofFile.Honest.K8.k8ColsAt G₀ l)
      (ProofFile.Honest.K8.k8TauAt G₀ l)) = true :=
  fun _ hl => small_of_124 (front_bound h hG hl)

/-- **The field ledger.** -/
theorem ledger_line (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) : ∀ l, l < 25 →
    shareSmall (P1K8.k8ShareAt Zp G₀ l) = true :=
  fun _ hl => small_of_124 (ledger_bound h hG hl)

/-- **The field marksK8.** -/
theorem marks_line (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    (P1K8.part1Marks Zp G₀).all markSmall = true :=
  List.all_eq_true.2 fun mk hm => by
    obtain ⟨a, b, c, d⟩ := marks_bound h hG mk hm
    unfold markSmall
    rw [if_neg (not_or.2 ⟨a, b⟩)]
    exact small_of ⟨c, d⟩

/-- **The structure's own fields**: a move of the structure's text turns this line red: the five other
fields are handed in, and the constructor takes these three. -/
theorem lines_of_others (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀)
    (quiet : ∀ l, l < 25 → ∀ u, VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u →
      shareSmall ((ProofFile.Honest.K9.batFallShare u.2.2.filled (u.2.1 - 1) ProofFile.Honest.K9.sizeOfE).plus
        (AtPublicFiles.TheFalls.noneNotGood l)) = true)
    (m3 : (ProofFile.Honest.K3.Good.k3Marks Zp G₀).all markSmall = true)
    (m4 : (ProofFile.Honest.K4.k4MarksWide Zp G₀).all markSmall = true)
    (m5 : (ProofFile.Honest.K5.k5Marks Zp G₀).all markSmall = true)
    (m6 : (ProofFile.Honest.K6.part4Marks Zp G₀).all markSmall = true) :
    ShareLines Zp G₀ :=
  ⟨front_line h hG, ledger_line h hG, quiet, marks_line h hG, m3, m4, m5, m6⟩

end AtFullSide.K8

#print axioms AtFullSide.K8.front_line
#print axioms AtFullSide.K8.ledger_line
#print axioms AtFullSide.K8.marks_line
