-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/QuietLine.lean: the stated share of the batching test's fall is small at each of the
25 segments. The share is the number of filled slots times one less than the number of claims, over
the size of the field. Both numbers are bounded by crude bounds, so no value of the public record
is evaluated.

  planG_used     a layers' plan has fewer than 2 ^ 30 slots: planG refuses more
  plan_nMsg      an attention plan has fewer than 2 ^ 30 slots: plan refuses more
  tests_cases    what testsWhere returns at each of the 25 segments
  quiet_sizes    under the library's head: fewer than 2 ^ 30 filled slots, at most 2 ^ 25 claims
  quiet_num      the share's numerator times 2 ^ 124 is at most the size of the field
  quiet_line     **the test on the share at each of the 25 segments**

Limits. Under the library's head. A stated number bounds no chance here. Nothing is claimed on
completeness, soundness or hiding.
-/
import E2E.TheFallsSum
import Johnson.P1K8R.RowsAskedOfHead
import Johnson.P1K8R.K9RowsByLink
import Johnson.Road.FormsKeysPlan
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Desc.First.Batch.TestsAtS
import Johnson.Desc.ProofFile.Honest.K9.Fall
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open OnBytes OnBytes.Model
open OnBytes.Road (ok_of_bind ok_of_refuse)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K9Asks (rowsFitB_iff claimsAt)
open ProofFile.Honest (Odds)
open P5J (AtMgA TS)

/-- **A layers' plan has fewer than 2 ^ 30 slots.** -/
theorem planG_used {P : Layer.Pub} {g : Nat} {O : Option Layer.HPlan2} {hp : Layer.HPlan2}
    (h : Layer.planG P g O = .ok hp) : hp.used < 2 ^ 30 := by
  unfold Layer.planG at h
  obtain ⟨b, -, h⟩ := ok_of_bind h
  obtain ⟨t1, -, h⟩ := ok_of_bind h
  obtain ⟨a, -, h⟩ := ok_of_bind h
  obtain ⟨Tp, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_refuse h
  cases O with
  | none =>
    obtain ⟨-, h⟩ := ok_of_refuse h
    obtain ⟨hm, h⟩ := ok_of_refuse h
    have e := (Except.ok.inj h).symm
    subst e
    exact Nat.lt_of_not_le (of_decide_eq_false hm)
  | some O =>
    cases hb2 : O.tl.ix.TX.back? with
    | none =>
      simp only [hb2] at h
      have h' : (Except.error "internal-g-owner-shape" : Except String Layer.HPlan2) = .ok hp := h
      cases h'
    | some t =>
      simp only [hb2] at h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨t3, -, h⟩ := ok_of_bind h
      obtain ⟨pe, -, h⟩ := ok_of_bind h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨hm, h⟩ := ok_of_refuse h
      have e := (Except.ok.inj h).symm
      subst e
      exact Nat.lt_of_not_le (of_decide_eq_false hm)

/-- **An attention plan has fewer than 2 ^ 30 slots.** -/
theorem plan_nMsg {settings : Settings} {i : Attention.In} {cf : Attention.Cfg}
    {P : Attention.Plan} (h : Attention.plan settings i cf = .ok P) : P.nMsg < 2 ^ 30 := by
  unfold Attention.plan at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h; done)
    | (cases h; rename_i hm _ _ _; exact Nat.lt_of_not_le hm)

/-- **What testsWhere returns**, at a public record with attention and twelve groups: the head at
24, a layers' plan at an even number and an attention plan at an odd one. -/
theorem tests_cases {X : Verify.Public} (hp4 : X.p4 = true) (hN : X.NGr = 12) {l : Nat}
    (hl : l < 25) {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hu : VerifiableInference.Desc.K9.testsWhere X l 0 = some u) :
    (l = 24 ∧ u.2.1 = X.H.nLin ∧ u.2.2.filled = X.H.nMsg) ∨
      (∃ hp, l = 2 * (l / 2) ∧ l / 2 < 12 ∧ X.G[l / 2]? = some hp ∧ u.2.1 = hp.nLin ∧
        u.2.2.filled = hp.used) ∨
      (∃ a, l = 2 * (l / 2) + 1 ∧ l / 2 < 12 ∧ X.A[l / 2]? = some a ∧ u.2.1 = a.nLin ∧
        u.2.2.filled = a.nMsg) := by
  unfold VerifiableInference.Desc.K9.testsWhere at hu
  simp only [hp4, hN, if_true] at hu
  by_cases e : l = 24
  · have e1 : (l == 2 * 12) = true := by
      rw [beq_iff_eq]
      omega
    rw [if_pos e1] at hu
    obtain rfl := Option.some.inj hu
    exact Or.inl ⟨e, rfl, rfl⟩
  · have e1 : ¬ (l == 2 * 12) = true := by
      rw [beq_iff_eq]
      omega
    rw [if_neg e1] at hu
    by_cases e2 : l % 2 = 0
    · have e3 : (l % 2 == 0) = true := by
        rw [beq_iff_eq]
        exact e2
      rw [if_pos e3] at hu
      obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 hu
      exact Or.inr (Or.inl ⟨hp, by omega, by omega, hg, rfl, rfl⟩)
    · have e3 : ¬ (l % 2 == 0) = true := by
        rw [beq_iff_eq]
        exact e2
      rw [if_neg e3] at hu
      obtain ⟨a, hg, rfl⟩ := Option.map_eq_some_iff.1 hu
      exact Or.inr (Or.inr ⟨a, by omega, by omega, hg, rfl, rfl⟩)

theorem rows_small (l : Nat) : P1K8.rowsAtLink l ≤ 2 ^ 25 := by
  unfold P1K8.rowsAtLink
  split_ifs <;> norm_num

theorem size_big : 2 ^ 179 ≤ ProofFile.Honest.K9.sizeOfE := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head: fewer than 2 ^ 30 filled slots and at most 2 ^ 25 claims.** The claims are
among the rows of the round that batches them, whose number is written. -/
theorem quiet_sizes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u) :
    u.2.2.filled < 2 ^ 30 ∧ u.2.1 ≤ 2 ^ 25 := by
  have pub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have S := _root_.Meaning.scope_plans h.scope h.reads pub
  have h4 : Zp.p.X.p4 = true := S.1
  have hN : Zp.p.X.NGr = 12 := S.2.1
  obtain ⟨Xl, -, hy⟩ := P1K8.rowsAsked_of_head Z D r Zp Np cF h.toAtMg l hl
  obtain ⟨n, ps, p, c1, -, ep, hle⟩ := (rowsFitB_iff Zp l Xl).1 hy
  obtain ⟨p', ep', er⟩ := P1K8.k9Rows_at_head OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg l hl
  obtain rfl : p = p' := Option.some.inj (ep.symm.trans ep')
  have hn : n ≤ 2 ^ 25 :=
    ((Nat.le_add_right _ _).trans hle).trans (er.le.trans (rows_small l))
  rcases tests_cases h4 hN hl hu with ⟨e, e1, e2⟩ | ⟨hp, e, hg, hG, e1, e2⟩ | ⟨a, e, hg, hA, e1, e2⟩
  · subst e
    have c2 : claimsAt Zp.p.X 24 = some Zp.p.X.H.nLin := rfl
    obtain rfl : n = Zp.p.X.H.nLin := Option.some.inj (c1.symm.trans c2)
    have w : Zp.p.X.H.nMsg = 3570 :=
      (VerifiableInference.Desc.Kinds.Head.Law.InScope.plan_in_scope h.scope h.reads pub).ns
    rw [e1, e2, w]
    exact ⟨by norm_num, hn⟩
  · have c2 : claimsAt Zp.p.X l = some hp.nLin := by
      unfold claimsAt
      rw [if_neg (by omega), if_pos (by omega), hG]
      rfl
    obtain rfl : n = hp.nLin := Option.some.inj (c1.symm.trans c2)
    rw [e1, e2]
    exact ⟨planG_used (Fo.Pub.public_G pub _ hp hG), hn⟩
  · have c2 : claimsAt Zp.p.X l = some a.nLin := by
      unfold claimsAt
      rw [if_neg (by omega), if_neg (by omega), hA]
      rfl
    obtain rfl : n = a.nLin := Option.some.inj (c1.symm.trans c2)
    obtain ⟨_, _, _, a0, _, _, _, hpl, ea, _, _⟩ := Fo.Pub.public_A pub _ a hA
    have e3 : a.nMsg = a0.nMsg := by
      have e4 := congrArg Attention.Plan.nMsg ea
      exact e4
    rw [e1, e2, e3]
    exact ⟨plan_nMsg hpl, hn⟩

/-- **The share's numerator times 2 ^ 124 is at most the size of the field.** -/
theorem quiet_num (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u) :
    u.2.2.filled * (u.2.1 - 1) * 2 ^ 124 ≤ ProofFile.Honest.K9.sizeOfE := by
  obtain ⟨hf, ht⟩ := quiet_sizes h hl hu
  have h1 : u.2.2.filled * (u.2.1 - 1) ≤ 2 ^ 30 * 2 ^ 25 :=
    Nat.mul_le_mul hf.le ((Nat.sub_le _ _).trans ht)
  refine (Nat.mul_le_mul_right _ h1).trans (le_trans ?_ size_big)
  norm_num

/-- **The test on the share of the batching test's fall, at each of the 25 segments.** -/
theorem quiet_line (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ l, l < 25 → ∀ u, VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u →
      AtPublicFiles.TheFalls.shareSmall ((ProofFile.Honest.K9.batFallShare u.2.2.filled (u.2.1 - 1)
                  ProofFile.Honest.K9.sizeOfE).plus (AtPublicFiles.TheFalls.noneNotGood l)) = true := by
  intro l hl u hu
  have hn := quiet_num h hl hu
  have hp : 0 < ProofFile.Honest.K9.sizeOfE := lt_of_lt_of_le (by norm_num) size_big
  have hn' : u.2.2.filled * (u.2.1 - 1) * 2 ^ 109 ≤ ProofFile.Honest.K9.sizeOfE :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by norm_num))).trans hn
  simp only [AtPublicFiles.TheFalls.shareSmall, Odds.plus, ProofFile.Honest.K9.batFallShare,
    AtPublicFiles.TheFalls.noneNotGood, Bool.and_eq_true, decide_eq_true_eq, Nat.mul_one, Nat.zero_mul,
    Nat.add_zero]
  exact ⟨hp, hn'⟩

end AtFullSide.K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K8.quiet_sizes
#print axioms AtFullSide.K8.quiet_num
#print axioms AtFullSide.K8.quiet_line
