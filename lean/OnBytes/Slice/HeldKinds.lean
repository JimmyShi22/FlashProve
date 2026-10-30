-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/HeldKinds.lean: `held_round` for rounds that are priced by the planner's formulas,
kind by kind, within a third of the distance.

`held_round` (OnBytes/Slice/HeldRound.lean) asks that a count, as a share of the round's typed
values, is at most the planner's number for the round's error. OnBytes/Params/KindLaws.lean says
what the planner's formulas enclose. This file joins them. For a round whose error is the `error` of
one of these formulas, the hypothesis on the count becomes a comparison of natural numbers, with q
for the number of elements of the extension field (`Setting.cardE`) and N for the number of the
round's typed values (`nVals`):
  a field error, degree / q, alone or times a list size L:
                                                 count * q ≤ L * degree * N (alone: without L);
  a combination by powers, (rows - 1) / q, alone or times a list size L:
                                                 count * q ≤ L * (rows - 1) * N (alone: without L);
  a fold's round and the last step's first round, at counts e + 1 and eZ + 1 of the footing
  `.third`:                                      count * q ≤ (the formula's numerator) * N;
  t positions at the radius e of a code of length n, footing `.third`:
                                                 count * n ^ t ≤ (n - e - 1) ^ t * N;
  t positions and one batching element:
                    count * (n ^ t * q) ≤ ((n - e - 1) ^ t * q + n ^ t * (L * (rows - 1))) * N.

Main theorems: `held_of_encl`, `held_of_encl_le`, `held_field`, `held_field_alone`, `held_powers`,
`held_powers_alone`, `held_fold_third`, `held_base_third`, `held_positions_third`, `held_cs_third`.
What is not claimed: that a routine of the planner prices a round by one of these formulas: the
equation on the round's error is a hypothesis, to be read off OnBytes/Params/Planner.lean (`close`
stores the `error` of the formula or, in a request's own rounds if there are several instances, of
the formula times their number; `settingOf` leaves that number at one). That a count meets its
comparison. That a count bounds a prover's chance. Rounds that are priced by `sampleError` or by the
error of the smallness test have no theorem; two rounds of a link and the point of the test on a
table are in OnBytes/Slice/HeldKindsLink.lean [not in this library]; `held_of_encl` serves wherever
the formula encloses a
number that can be named. Nothing at the footing `.johnson`.
What
`held_round` does not
claim is not claimed here. For proofs only; the program, that is the Lean port built from OnBytes/,
does not import this file.

-/
import OnBytes.Params.KindLaws
import OnBytes.Slice.HeldRound

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob _root_.Run OnBytes.Params
open scoped ENNReal

/-- What `held_round` asks of a round beside the count: the setting has the format's field; the
written round d has r's entry; `logN` is at most 64; drawNZ is at most drawE; work + 66 ≤ target if
the round draws an element; and r holds. -/
structure Held (s : Setting) (r : PlanRound) (d : PQ.RD) : Prop where
  p : s.p = 2 ^ 64 - 2 ^ 32 + 1
  degree : s.degree = 3
  entry : d.entry = r.entry
  log : r.entry.logN ≤ 64
  nz : r.entry.drawNZ ≤ r.entry.drawE
  work : r.entry.drawE ≠ 0 → r.entry.work + 66 ≤ s.target
  holds : roundHolds s (capped s) r = true

/-- The conclusion of `held_round`: the count, times the sampler's weight, is at most 2 ^ -target of
the round's written verifier messages. -/
def Meets (s : Setting) (d : PQ.RD) (count : ℕ) : Prop :=
  ((count * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
    (2 : ℝ≥0∞)⁻¹ ^ s.target * (Fintype.card (wRound d).Chal : ℝ≥0∞)

/-- `held_round` for a round whose error is the `error` of a bound that encloses x. -/
theorem held_of_encl {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) {E : Bound} {x : ℚ}
    (hE : Encl E x) (hb : E.bad = false) (hr : r.error = E.error) (count : ℕ)
    (h : (count : ℚ) ≤ x * (nVals (Fmt.dsOf d.entry d.kind) : ℚ)) : Meets s d count :=
  held_round s H.p H.degree r d H.entry H.log H.nz H.work H.holds count
    (hr ▸ share_of_encl hE hb count _ h)

/-- `held_of_encl` for a round whose error is at least the bound's `error`. -/
theorem held_of_encl_le {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) {E : Bound}
    {x : ℚ} (hE : Encl E x) (hb : E.bad = false) (hr : E.error.val ≤ r.error.val) (count : ℕ)
    (h : (count : ℚ) ≤ x * (nVals (Fmt.dsOf d.entry d.kind) : ℚ)) : Meets s d count :=
  held_round s H.p H.degree r d H.entry H.log H.nz H.work H.holds count
    ((share_of_encl hE hb count _ h).trans
      (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)))

/-- The extension field has elements. -/
theorem cardE_pos {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) : 0 < s.cardE := by
  unfold Setting.cardE
  rw [H.p, H.degree]
  decide

/-- The setting's extension field has as many elements as the format's: p ^ 3, which is what `nVals`
counts for an element. -/
theorem cardE_eq {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) :
    s.cardE = Fmt.Fld.two.p ^ 3 := by
  unfold Setting.cardE
  rw [H.p, H.degree]
  rfl

/-- A count as a share K / q, from a comparison of natural numbers. -/
theorem share_div (count K N q : ℕ) (hq : 0 < q) (h : count * q ≤ K * N) :
    (count : ℚ) ≤ (K : ℚ) / (q : ℚ) * (N : ℚ) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hq)]
  exact_mod_cast h

/-- A round that is priced by a list size times a field error. -/
theorem held_field {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (L degree : ℕ)
    (hb : (Bound.ofNat L * fieldError s degree).bad = false)
    (hr : r.error = (Bound.ofNat L * fieldError s degree).error) (count : ℕ)
    (h : count * s.cardE ≤ L * degree * nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_listField s L degree) hb hr count ?_
  have := share_div count (L * degree) _ s.cardE (cardE_pos H) h
  rw [Nat.cast_mul, mul_div_assoc] at this
  exact this

/-- A round that is priced by a list size times the error of a combination by powers. -/
theorem held_powers {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (L rows : ℕ)
    (hb : (Bound.ofNat L * powersError s rows).bad = false)
    (hr : r.error = (Bound.ofNat L * powersError s rows).error) (count : ℕ)
    (h : count * s.cardE ≤ L * (rows - 1) * nVals (Fmt.dsOf d.entry d.kind)) :
    Meets s d count := by
  refine held_of_encl H (encl_listPowers s L rows) hb hr count ?_
  have := share_div count (L * (rows - 1)) _ s.cardE (cardE_pos H) h
  rw [Nat.cast_mul, mul_div_assoc] at this
  exact this

/-- A round that is priced by a field error alone, degree / q, with no list size. -/
theorem held_field_alone {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (degree : ℕ)
    (hb : (fieldError s degree).bad = false) (hr : r.error = (fieldError s degree).error)
    (count : ℕ) (h : count * s.cardE ≤ degree * nVals (Fmt.dsOf d.entry d.kind)) :
    Meets s d count :=
  held_of_encl H (encl_fieldError s degree) hb hr count
    (share_div count degree _ s.cardE (cardE_pos H) h)

/-- A round that is priced by the error of a combination by powers alone, (rows - 1) / q. -/
theorem held_powers_alone {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (rows : ℕ)
    (hb : (powersError s rows).bad = false) (hr : r.error = (powersError s rows).error)
    (count : ℕ) (h : count * s.cardE ≤ (rows - 1) * nVals (Fmt.dsOf d.entry d.kind)) :
    Meets s d count :=
  held_of_encl H (encl_powersError s rows) hb hr count
    (share_div count (rows - 1) _ s.cardE (cardE_pos H) h)

/-- Round j of a fold, where the main code's count has the footing `.third` and is e + 1, and, while
mask rows are folded, the mask code's has it and is eZ + 1. -/
theorem held_fold_third {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (g : GroupSize)
    (a : Analysis) (j e eZ : ℕ)
    (h1 : a.mainAt.source = .third) (c1 : a.mainAt.count = Bound.ofNat (e + 1))
    (hz : (g.hasMask && decide (j ≤ g.h)) = true →
      a.maskAt.source = .third ∧ a.maskAt.count = Bound.ofNat (eZ + 1))
    (hb : (foldRoundError s g a j).bad = false) (hr : r.error = (foldRoundError s g a j).error)
    (count : ℕ)
    (h : count * s.cardE ≤ (e + 1 + a.list * 2 +
      (if (g.hasMask && decide (j ≤ g.h)) = true then 2 * (eZ + 1) else 0)) *
        nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_foldRoundError_third s g a j e eZ h1 c1 hz) hb hr count ?_
  have := share_div count _ _ s.cardE (cardE_pos H) h
  refine this.trans (le_of_eq ?_)
  congr 1
  split <;> (push_cast; ring)

/-- The first round of the last step, where the main code's count has the footing `.third` and is
e + 1, and, if the group has a mask, the mask code's has it and is eZ + 1. -/
theorem held_base_third {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) (g : GroupSize)
    (a : Analysis) (e eZ : ℕ)
    (h1 : a.mainAt.source = .third) (c1 : a.mainAt.count = Bound.ofNat (e + 1))
    (hz : g.hasMask = true → a.maskAt.source = .third ∧ a.maskAt.count = Bound.ofNat (eZ + 1))
    (hb : (baseError s g a).bad = false) (hr : r.error = (baseError s g a).error) (count : ℕ)
    (h : count * s.cardE ≤ (e + 1 + a.list * 1 + (if g.hasMask = true then eZ + 1 else 0)) *
        nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_baseError_third s g a e eZ h1 c1 hz) hb hr count ?_
  have := share_div count _ _ s.cardE (cardE_pos H) h
  refine this.trans (le_of_eq ?_)
  congr 1
  split <;> (push_cast; ring)

/-- Where the footing is `.third`: (n - radius - 1) ^ t is at most a ^ t * n ^ t, for every a that
the agreement encloses. -/
theorem third_pow {s : Setting} {c : Word} {agree : Bound} {a : ℚ} (ha : Encl agree a)
    (h : (atDistance s c agree).source = .third) (t : ℕ) :
    (((c.n - radiusOf (atDistance s c agree) c.n - 1) ^ t : ℕ) : ℚ) ≤
      a ^ t * ((c.n ^ t : ℕ) : ℚ) := by
  obtain ⟨h3, _, _, _, _, hlt⟩ := atDistance_third ha h
  generalize radiusOf (atDistance s c agree) c.n = e at h3 hlt
  have hn : (0 : ℚ) < (c.n : ℚ) := by
    have : 0 < c.n := Nat.pos_of_ne_zero (by unfold Word.n; positivity)
    exact_mod_cast this
  have hle : e + 1 ≤ c.n := by omega
  have hcast : ((c.n - e - 1 : ℕ) : ℚ) = (c.n : ℚ) - (e : ℚ) - 1 := by
    rw [Nat.sub_sub, Nat.cast_sub hle]
    push_cast
    ring
  have h0 : 0 ≤ ((c.n : ℚ) - (e : ℚ) - 1) / (c.n : ℚ) := by
    rw [← hcast]
    positivity
  have hpow := pow_le_pow_left₀ h0 hlt.le t
  rw [div_pow, div_le_iff₀ (by positivity)] at hpow
  rw [Nat.cast_pow, Nat.cast_pow, hcast]
  exact hpow

/-- A round that draws t positions and is priced by the agreement to the power t, where the footing
is `.third`. The radius is `radiusOf (atDistance s c agree) c.n`. -/
theorem held_positions_third {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) {c : Word}
    {agree : Bound} {a : ℚ} (ha : Encl agree a) (h3 : (atDistance s c agree).source = .third)
    (t : ℕ) (hb : (Bound.pow agree t).bad = false) (hr : r.error = (Bound.pow agree t).error)
    (count : ℕ)
    (h : count * c.n ^ t ≤ (c.n - radiusOf (atDistance s c agree) c.n - 1) ^ t *
      nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (Bound.encl_pow ha t) hb hr count ?_
  have hp := third_pow ha h3 t
  generalize (c.n - radiusOf (atDistance s c agree) c.n - 1) ^ t = A at h hp
  generalize nVals (Fmt.dsOf d.entry d.kind) = N at h
  have hnt : (0 : ℚ) < ((c.n ^ t : ℕ) : ℚ) := by
    have : 0 < c.n ^ t := Nat.pos_of_ne_zero (by unfold Word.n; positivity)
    exact_mod_cast this
  have hq : (count : ℚ) * ((c.n ^ t : ℕ) : ℚ) ≤ (A : ℚ) * (N : ℚ) := by exact_mod_cast h
  have hN : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
  have : (count : ℚ) * ((c.n ^ t : ℕ) : ℚ) ≤ a ^ t * (N : ℚ) * ((c.n ^ t : ℕ) : ℚ) := by
    calc (count : ℚ) * ((c.n ^ t : ℕ) : ℚ) ≤ (A : ℚ) * (N : ℚ) := hq
      _ ≤ a ^ t * ((c.n ^ t : ℕ) : ℚ) * (N : ℚ) := mul_le_mul_of_nonneg_right hp hN
      _ = a ^ t * (N : ℚ) * ((c.n ^ t : ℕ) : ℚ) := by ring
  exact le_of_mul_le_mul_right this hnt

/-- A round that draws t positions and one batching element, and is priced by the agreement to the
power t and a list size times the error of a combination by powers, where the footing is
`.third`. -/
theorem held_cs_third {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d) {c : Word}
    {agree : Bound} {a : ℚ} (ha : Encl agree a) (h3 : (atDistance s c agree).source = .third)
    (t L rows : ℕ) (hb : (Bound.pow agree t + Bound.ofNat L * powersError s rows).bad = false)
    (hr : r.error = (Bound.pow agree t + Bound.ofNat L * powersError s rows).error) (count : ℕ)
    (h : count * (c.n ^ t * s.cardE) ≤
      ((c.n - radiusOf (atDistance s c agree) c.n - 1) ^ t * s.cardE +
        c.n ^ t * (L * (rows - 1))) * nVals (Fmt.dsOf d.entry d.kind)) : Meets s d count := by
  refine held_of_encl H (encl_cs s ha t L rows) hb hr count ?_
  have hp := third_pow ha h3 t
  generalize (c.n - radiusOf (atDistance s c agree) c.n - 1) ^ t = A at h hp
  generalize nVals (Fmt.dsOf d.entry d.kind) = N at h
  have hnt : (0 : ℚ) < ((c.n ^ t : ℕ) : ℚ) := by
    have : 0 < c.n ^ t := Nat.pos_of_ne_zero (by unfold Word.n; positivity)
    exact_mod_cast this
  have hq0 : (0 : ℚ) < (s.cardE : ℚ) := by exact_mod_cast cardE_pos H
  generalize c.n ^ t = M at h hp hnt
  generalize s.cardE = q at h hq0
  generalize rows - 1 = R at h
  have hq : (count : ℚ) * ((M : ℚ) * (q : ℚ)) ≤
      ((A : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) := by exact_mod_cast h
  have hN : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
  have hMq : (0 : ℚ) < (M : ℚ) * (q : ℚ) := mul_pos hnt hq0
  have e1 : (a ^ t + (L : ℚ) * ((R : ℚ) / (q : ℚ))) * (N : ℚ) * ((M : ℚ) * (q : ℚ)) =
      (a ^ t * (M : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) := by
    field_simp
  have e2 : ((A : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) ≤
      (a ^ t * (M : ℚ) * (q : ℚ) + (M : ℚ) * ((L : ℚ) * (R : ℚ))) * (N : ℚ) := by
    refine mul_le_mul_of_nonneg_right ?_ hN
    have := mul_le_mul_of_nonneg_right hp hq0.le
    linarith
  refine le_of_mul_le_mul_right ?_ hMq
  rw [e1]
  exact hq.trans e2

end OnBytes.Slice

#print axioms OnBytes.Slice.held_of_encl
#print axioms OnBytes.Slice.held_of_encl_le
#print axioms OnBytes.Slice.cardE_eq
#print axioms OnBytes.Slice.held_field
#print axioms OnBytes.Slice.held_field_alone
#print axioms OnBytes.Slice.held_powers_alone
#print axioms OnBytes.Slice.held_powers
#print axioms OnBytes.Slice.held_fold_third
#print axioms OnBytes.Slice.held_base_third
#print axioms OnBytes.Slice.held_positions_third
#print axioms OnBytes.Slice.held_cs_third
