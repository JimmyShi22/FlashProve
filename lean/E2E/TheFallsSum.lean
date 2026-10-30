-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheFallsSum.lean: THE FALLS' NUMBER LIES WITHIN ITS ROOM, FROM ONE TEST ON THE RECORDS. Each of
the 251 records, falls and marks, is asked one inequality of natural numbers on its stated share. That
test reads public data alone. Where it holds, the sum of all records at the kit is at most 2⁻¹⁰⁰.

  tiny                   2⁻¹⁰⁸, what a record may cost
  shareSmall, markSmall  the test on one record
  sharesSmall            the test on all records
  ShareLines, sharesSmall_of_lines   the test, kind by kind; the kinds' lines give it
  atKit_le, markPrice_le what the test gives for one record
  sum_map_le             a sum of small things
  number_le              the number is at most the count of records times tiny
  fallsWithinRoom        at the term: under the head, from the test on all records, the number lies
                         within the room

Limits. The test is a premise here. It is not evaluated at any public files. That a record's stated
number bounds its event is no part of this file. This file proves nothing about completeness,
soundness or zero knowledge.
-/
import E2E.TheFallsSeated

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.TheFalls
open ProofFile.Honest
open VerifiableInference.Desc (Chain KindName)
open P5J (AtMgA TS)

/-- What a record may cost. -/
def tiny : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 108

/-- **The test on a stated share.** -/
def shareSmall (o : Odds) : Bool := decide (0 < o.den) && decide (o.num * 2 ^ 109 ≤ o.den)

/-- A stricter test than shareSmall, for a finer bound. -/
def fallSmall (o : Odds) : Bool := decide (0 < o.den) && decide (o.num * 2 ^ 124 ≤ o.den)

/-- The stricter test gives the plainer one. -/
theorem shareSmall_of_fallSmall {o : Odds} (h : fallSmall o = true) : shareSmall o = true := by
  unfold fallSmall at h
  unfold shareSmall
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, le_trans (Nat.mul_le_mul_left _ ?_) h.2⟩
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- The size of the field, as the marks of the lookups and of the output head are priced. -/
def fieldSize : Nat := Fmt.Fld.two.p ^ 3

/-- **The test on a mark.** -/
def markSmall (mk : Mark) : Bool :=
  if mk.place.kind = KindName.K3 ∨ mk.place.kind = KindName.K6 then
    shareSmall ⟨mk.share.num, fieldSize⟩
  else shareSmall mk.share

theorem kap_pow_le {n : ℕ} (h : n * 2 ≤ 2 ^ 128) : Iop.kapSl 128 ^ n ≤ 2 := by
  have e := Iop.kapSl_pow_le (sl := 128) (n := n) (e := 0) (by simpa using h)
  simpa [one_add_one_eq_two] using e

/-- **A share of at most 2⁻⁽ᵉ⁺¹⁾ costs at most 2⁻ᵉ**, at a factor of at most 2. -/
theorem atKit_le_pow {κ : ℝ≥0∞} (hκ : κ ≤ 2) {o : Odds} {e : ℕ} (h₀ : 0 < o.den)
    (h₁ : o.num * 2 ^ (e + 1) ≤ o.den) : atKit κ o ≤ (2 : ℝ≥0∞)⁻¹ ^ e := by
  have hD : (o.num : ℝ≥0∞) * 2 ^ (e + 1) ≤ (o.den : ℝ≥0∞) := by exact_mod_cast h₁
  have hD₀ : (o.den : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.1 h₀)
  unfold atKit
  rw [← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le]
  calc (o.num : ℝ≥0∞) * (κ / (o.den : ℝ≥0∞)) * 2 ^ e
      = ((o.num : ℝ≥0∞) * 2 ^ e * κ) / (o.den : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        ring
    _ ≤ ((o.num : ℝ≥0∞) * 2 ^ e * 2) / (o.den : ℝ≥0∞) :=
        ENNReal.div_le_div_right (mul_le_mul_left' hκ _) _
    _ = ((o.num : ℝ≥0∞) * 2 ^ (e + 1)) / (o.den : ℝ≥0∞) := by
        rw [mul_assoc, ← pow_succ]
    _ ≤ (o.den : ℝ≥0∞) / (o.den : ℝ≥0∞) := ENNReal.div_le_div_right hD _
    _ = 1 := ENNReal.div_self hD₀ (ENNReal.natCast_ne_top _)

/-- **A record that passes costs at most tiny**, at a factor of at most 2. -/
theorem atKit_le {κ : ℝ≥0∞} (hκ : κ ≤ 2) {o : Odds} (h : shareSmall o = true) :
    atKit κ o ≤ tiny := by
  unfold shareSmall at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact atKit_le_pow hκ h.1 h.2

theorem oneElement_le : oneElement ≤ 2 := kap_pow_le (by norm_num)

/-- **A mark that passes costs at most tiny.** -/
theorem markPrice_le {mk : Mark} (h : markSmall mk = true) : markPrice mk ≤ tiny := by
  unfold markSmall at h
  unfold markPrice
  by_cases h₃ : mk.place.kind = KindName.K3
  · rw [if_pos (Or.inl h₃)] at h
    rw [if_pos h₃]
    exact atKit_le (κ := Iop.kapSl 128 ^ 108) (kap_pow_le (by norm_num))
      (o := ⟨mk.share.num, fieldSize⟩) h
  · rw [if_neg h₃]
    by_cases h₆ : mk.place.kind = KindName.K6
    · rw [if_pos (Or.inr h₆)] at h
      rw [if_pos h₆]
      exact atKit_le oneElement_le (o := ⟨mk.share.num, fieldSize⟩) h
    · rw [if_neg (by tauto)] at h
      rw [if_neg h₆]
      exact atKit_le oneElement_le h

/-- A sum of small things. -/
theorem sum_map_le {α : Type} (f : α → ℝ≥0∞) (e : ℝ≥0∞) : ∀ l : List α, (∀ x ∈ l, f x ≤ e) →
    (l.map f).sum ≤ (l.length : ℝ≥0∞) * e
  | [], _ => by simp
  | a :: t, h => by
    have ih := sum_map_le f e t fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.sum_cons, List.length_cons]
    calc f a + (t.map f).sum ≤ e + (t.length : ℝ≥0∞) * e :=
          add_le_add (h a List.mem_cons_self) ih
      _ = ((t.length + 1 : ℕ) : ℝ≥0∞) * e := by
          push_cast
          ring

/-- A list of falls that passes. -/
theorem fallsPrice_le {S : Type} {fs : List (Fall S)} (h : fs.all (fun f => shareSmall f.share) = true) :
    fallsPrice fs ≤ (fs.length : ℝ≥0∞) * tiny :=
  sum_map_le _ _ fs fun f hf => atKit_le oneElement_le (List.all_eq_true.1 h f hf)

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (G₀ : ProofFile.Ground)
  (s : FallSlots (ProofFileDesc Zp Np cF))

/-- **The test on all records.** -/
def sharesSmall : Bool :=
  (theFalls₁ Zp Np cF G₀ s).all (fun f => shareSmall f.share) &&
    (theFalls₂ Zp Np cF s).all (fun f => shareSmall f.share) &&
    (theFalls₃ Zp Np cF s).all (fun f => shareSmall f.share) &&
    (theMarks Zp G₀).all markSmall

/-- **The number is at most the count of records times tiny.** -/
theorem number_le (h : sharesSmall Zp Np cF G₀ s = true) :
    theFallsNumber Zp Np cF G₀ s ≤
      (((theFalls₁ Zp Np cF G₀ s).length : ℝ≥0∞) + ((theFalls₂ Zp Np cF s).length : ℝ≥0∞) +
        ((theFalls₃ Zp Np cF s).length : ℝ≥0∞) + ((theMarks Zp G₀).length : ℝ≥0∞)) * tiny := by
  unfold sharesSmall at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  rw [add_mul, add_mul, add_mul]
  exact add_le_add (add_le_add (add_le_add (fallsPrice_le h₁) (fallsPrice_le h₂))
    (fallsPrice_le h₃))
    (sum_map_le _ _ _ fun mk hm => markPrice_le (List.all_eq_true.1 h₄ mk hm))

/-- **The lines of the kinds**: each record's test, by the record's kind. -/
structure ShareLines (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) : Prop where
  front : ∀ l, l < 25 →
    shareSmall (K8.frontFallShare (K8.k8ColsAt G₀ l) (K8.k8TauAt G₀ l)) = true
  ledger : ∀ l, l < 25 → shareSmall (P1K8.k8ShareAt Zp G₀ l) = true
  quiet : ∀ l, l < 25 → ∀ u, VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u →
    shareSmall ((K9.batFallShare u.2.2.filled (u.2.1 - 1) K9.sizeOfE).plus (noneNotGood l)) = true
  marksK8 : (P1K8.part1Marks Zp G₀).all markSmall = true
  marksK3 : (K3.Good.k3Marks Zp G₀).all markSmall = true
  marksK4 : (K4.k4MarksWide Zp G₀).all markSmall = true
  marksK5 : (K5.k5Marks Zp G₀).all markSmall = true
  marksK6 : (K6.part4Marks Zp G₀).all markSmall = true

set_option maxRecDepth 100000 in
theorem coinZero_small : shareSmall K4.k4CoinZeroShare = true := by decide +kernel

variable {Zp G₀ Np cF} in
/-- **The lines give the test on the first chain's list.** -/
theorem fallsFull_small (h : ShareLines Zp G₀) {r0 : Nat → Nat} :
    ∀ f ∈ (fallsFull Zp G₀ noneNotGood r0 : List (Fall VerifiableInference.Desc.First.S)),
      shareSmall f.share = true := by
  intro f hf
  unfold fallsFull fallsHead at hf
  rcases List.mem_append.1 hf with hm | hm
  · obtain ⟨l, hl, hF⟩ := List.mem_flatMap.1 hm
    have hl' : l < 25 := List.mem_range.1 hl
    unfold linkFalls at hF
    rcases List.mem_append.1 hF with hF | hF
    · rcases List.mem_append.1 hF with hF | hF
      · obtain rfl := List.mem_singleton.1 hF
        exact h.front l hl'
      · cases hp : IM.k9At Zp l with
        | none =>
          rw [hp] at hF
          cases hF
        | some p =>
          cases hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 with
          | none =>
            rw [hp, hu] at hF
            cases hF
          | some u =>
            rw [hp, hu] at hF
            obtain rfl := List.mem_singleton.1 hF
            exact h.quiet l hl' u hu
    · cases hX : G₀.built[l]? with
      | none =>
        rw [hX] at hF
        cases hF
      | some Xl =>
        rw [hX] at hF
        obtain rfl := List.mem_singleton.1 hF
        exact h.ledger l hl'
  · obtain ⟨g, _, hF⟩ := List.mem_filterMap.1 hm
    cases hh : G₀.W.G[g]? with
    | none =>
      rw [hh] at hF
      cases hF
    | some hp =>
      rw [hh] at hF
      obtain rfl := Option.some.inj hF
      exact coinZero_small

/-- **The lines of the kinds give the test on all records**, at the slots with nothing in them. -/
theorem sharesSmall_of_lines (h : ShareLines Zp G₀) :
    sharesSmall Zp Np cF G₀ (FallSlots.nothing _) = true := by
  obtain ⟨e₁, e₂, e₃⟩ := theFalls_nothing Zp Np cF G₀
  unfold sharesSmall
  rw [e₁, e₂, e₃]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨List.all_eq_true.2 fun f hf => fallsFull_small h f hf, rfl⟩, rfl⟩, ?_⟩
  unfold theMarks
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h.marksK8, h.marksK3⟩, h.marksK4⟩, h.marksK5⟩, h.marksK6⟩

/-- 256 records at tiny fill the room. -/
theorem room_of_count {n : ℕ} (h : n ≤ 256) :
    (n : ℝ≥0∞) * tiny ≤ AtPublicFiles.AtFiles.HonestTerm.fallsRoom := by
  have e : (256 : ℝ≥0∞) * tiny = AtPublicFiles.AtFiles.HonestTerm.fallsRoom := by
    unfold tiny AtPublicFiles.AtFiles.HonestTerm.fallsRoom AtPublicFiles.TheRooms.onlineFallRoom AtPublicFiles.TheRooms.theRoom
    have h₂ : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc (256 : ℝ≥0∞) * 2⁻¹ ^ 108 = ((2 : ℝ≥0∞) * 2⁻¹) ^ 8 * 2⁻¹ ^ 100 := by
          rw [mul_pow, show (108 : ℕ) = 8 + 100 from rfl, pow_add]
          norm_num
          ring
      _ = 2⁻¹ ^ 100 := by rw [h₂, one_pow, one_mul]
  rw [← e]
  exact mul_le_mul_right' (by exact_mod_cast h) _

end AtPublicFiles.TheFalls

namespace AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (PublicFiles)
open P5J
open AtPublicFiles.TheFalls

variable {Z : PublicFiles} (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl)

/-- **Under the head, from the test on all records, the number lies within the room.** -/
theorem fallsWithinRoom (hM : onlineMaker Z = .ok returned) {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain xh)
    (hs : sharesSmall returned.Z places firstChain returned.G
      (theSlots returned places firstChain) = true) :
    FallsWithinRoom returned places firstChain (theSlots returned places firstChain) := by
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  have eG := ground_of_head returned places firstChain hM h O.made
  obtain ⟨e₁, e₂, e₃⟩ := theFalls_nothing returned.Z places firstChain returned.G
  have l₁ : (theFalls₁ returned.Z places firstChain returned.G (FallSlots.nothing _)).length = 87 := by
    rw [← eG]
    exact theFalls₁_length returned.Z places firstChain h O.made
  have l₄ : (theMarks returned.Z returned.G).length = 164 := by
    rw [← eG]
    exact theMarks_164 h O.made
  have hn := number_le returned.Z places firstChain returned.G _ hs
  refine le_trans hn (le_trans (le_of_eq ?_) (room_of_count (n := 251) (by norm_num)))
  rw [l₁, e₂, e₃, l₄]
  norm_num

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.TheFalls.atKit_le
#print axioms AtPublicFiles.TheFalls.markPrice_le
#print axioms AtPublicFiles.TheFalls.number_le
#print axioms AtPublicFiles.TheFalls.sharesSmall_of_lines
#print axioms AtPublicFiles.TheFalls.room_of_count
#print axioms AtPublicFiles.AtFiles.HonestTerm.fallsWithinRoom
