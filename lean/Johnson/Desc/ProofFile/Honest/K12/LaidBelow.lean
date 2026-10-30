-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/LaidBelow.lean: a member's rows read its stretch below the
message's count alone. memOfSending (JobShared.lean) hands laid the stretch from 0 on, and a stretch
gives what its maker gives beyond its count: this file shows that no row reads there. The sister of
rowsR_csAt (AtProof/JobW.lean) for laid (Honest/K14/Sendings.lean).

  tabE_congr_laid     a table reads its function below its two sizes alone
  ite_same_off       a small lemma on two branches
  rows_below     a plain message's rows, at two readers of coins that agree below dueOf, are one
  mem_rows_below so at a member made by memOfSending, at a plain message, where no vector is handed
                 in or one is: at two stretches that agree below the count

Limits.
- Plain messages alone: every member of jobAtU and jobAtOmega that is laid is one: jobOmega's sort
  is plain at every number, jobU's at number 0 by its text; read, not stated here. The fresh table's
  rows are not treated.
- Of the extension field's values: the rows read no other.
- It says which values a row reads, not whose they are: that is the lending.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E Codes OracleShape)
open ProofFile.Honest.K14 (SendJob MsgSort dueOf laid)

/-- A table reads its function below its two sizes alone. -/
theorem tabE_congr_laid (r n : ℕ) (f g : ℕ → ℕ → E) (h : ∀ i < r, ∀ j < n, f i j = g i j) :
    tabE r n f = tabE r n g := by
  unfold tabE
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  rw [h i (List.mem_range.1 hi) j (List.mem_range.1 hj)]

/-- Two branches that agree where the test is true. -/
theorem ite_same_off (c : Bool) (a a' b : E) (h : c = true → a = a') :
    (if c = true then a else b) = (if c = true then a' else b) := by
  cases c with
  | false => rfl
  | true => exact h rfl

/-- **A plain message's rows, at two readers of coins that agree below its count, are one.** -/
theorem rows_below (codes : Codes) (s : OracleShape) (v cs cs' : ℕ → E) (hi : Bool)
    (h : ∀ i < dueOf codes s (.plain hi), cs i = cs' i) :
    rowsOfLaid codes s (laid codes s v cs (.plain hi)) =
      rowsOfLaid codes s (laid codes s v cs' (.plain hi)) := by
  have hd : ∀ i, i < s.mainRows * (codes.base.getD s.code default).r +
      (if s.maskRows == 0 then s.answers else 0) +
      s.maskRows * (codes.mask.getD s.maskCode default).ell +
      s.maskRows * (codes.mask.getD s.maskCode default).r → cs i = cs' i := h
  have hM : tabE s.mainRows (codes.base.getD s.code default).ell
      (laid codes s v cs (.plain hi)).main =
      tabE s.mainRows (codes.base.getD s.code default).ell
        (laid codes s v cs' (.plain hi)).main := by
    refine tabE_congr_laid _ _ _ _ fun r _ j hj => ?_
    simp only [laid]
    refine ite_same_off _ _ _ _ fun hc => ?_
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h0, -⟩, hle⟩, -⟩ := hc
    refine hd _ ?_
    have e0 : (if s.maskRows == 0 then s.answers else 0) = s.answers := by simp [h0]
    rw [e0, h0, Nat.zero_mul, Nat.zero_mul]
    omega
  have hR : tabE s.mainRows (codes.base.getD s.code default).r
      (laid codes s v cs (.plain hi)).mainTail =
      tabE s.mainRows (codes.base.getD s.code default).r
        (laid codes s v cs' (.plain hi)).mainTail := by
    refine tabE_congr_laid _ _ _ _ fun r hr t ht => ?_
    simp only [laid]
    refine hd _ ?_
    have h1 := Nat.mul_le_mul_right (codes.base.getD s.code default).r (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at h1
    omega
  have hW : tabE s.maskRows (codes.mask.getD s.maskCode default).ell
      (laid codes s v cs (.plain hi)).mask =
      tabE s.maskRows (codes.mask.getD s.maskCode default).ell
        (laid codes s v cs' (.plain hi)).mask := by
    refine tabE_congr_laid _ _ _ _ fun r hr j hj => ?_
    simp only [laid]
    refine hd _ ?_
    have h1 := Nat.mul_le_mul_right s.maskRows (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul, Nat.mul_comm (codes.mask.getD s.maskCode default).ell] at h1
    omega
  have hS : tabE s.maskRows (codes.mask.getD s.maskCode default).r
      (laid codes s v cs (.plain hi)).maskTail =
      tabE s.maskRows (codes.mask.getD s.maskCode default).r
        (laid codes s v cs' (.plain hi)).maskTail := by
    refine tabE_congr_laid _ _ _ _ fun r hr t ht => ?_
    simp only [laid]
    refine hd _ ?_
    have h1 := Nat.mul_le_mul_right (codes.mask.getD s.maskCode default).r (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at h1
    omega
  simp only [rowsOfLaid, hM, hR, hW, hS]

/-- **A member's rows read its stretch below the message's count alone**, at a plain message:
whatever stands beyond the count, and whatever a stretch's maker gives there, no row reads it. -/
theorem mem_rows_below {W X : Type} (J : SendJob) (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ)
    (ask : W → ProofFile.Honest.K14.Ask) (v? : Option (W → Front X → ℕ → E)) (hi : Bool)
    (hs : J.sort k = .plain hi) (w : W) (fr : Front X) (c c' : Stretch)
    (h : ∀ i < dueOf J.Q.codes (J.Q.sent.getD k default).shape (J.sort k), c.e i = c'.e i) :
    (memOfSending J at_ k fs ask v?).rows w fr c =
      (memOfSending J at_ k fs ask v?).rows w fr c' := by
  simp only [memOfSending]
  rw [hs]
  refine rows_below _ _ _ _ _ hi fun i hi' => ?_
  show E.ofTriple (OnBytes.Slice.ofE (c.e i)) = E.ofTriple (OnBytes.Slice.ofE (c'.e i))
  rw [h i (by rw [hs]; exact hi')]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tabE_congr_laid
#print axioms ProofFile.Honest.K12.Light.ite_same_off
#print axioms ProofFile.Honest.K12.Light.rows_below
#print axioms ProofFile.Honest.K12.Light.mem_rows_below
