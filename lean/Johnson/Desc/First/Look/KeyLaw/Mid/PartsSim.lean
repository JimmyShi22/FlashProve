-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/PartsSim.lean: at the parts' steps the course over the field goes
with the lookup's own function of the flat transcript.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean); that the program's run, read in the field, is this
course is not shown in this file.

Statements and proofs: the field parts of the bundle Sims
(Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean) at the relation Sim
(Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean). On one side stands cParts
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean): the steps of the course's sumcheck; on the other
A.partsRun (Cb/Pv/KeyLookup/PartsRun.lean), which by theorem is the output of the verifier of the
parts' steps. A single step is part_step (OnBytes/Tie/Pv/KeyLookup/PortSim.lean).

Main names:
  stepP D j s: one step of cPart. cPart_succ: cPart takes its steps from the front; the same from
    the end.
  fits_step: a flat list that fits a step's formats is three rounds (μ | ε), (q₁, q₂ | β), (v₀, v₁ |
    nothing).
  PlacesAt A sl D wP cP b: step l < m - 1 has its five places at the mask entries number b + 5 l,
    .., b + 5 l + 4 in the order D.ms in which the first ledger gives its entries out, read by sl.
    placesAt_std: so it is at Parts.wStd, Parts.cStd (Cb/Pv/KeyLookup/PartsStd.lean).
  Kept: what holds after k steps, of the course's stand and the flat state.
  parts_goes: under D.S = A.toPub and PlacesAt at b := own + ownAt A.toPub 1: Goes (Sim A sl st own
    idx 1) (Sim A sl st own idx 2) (cParts D) (A.partsRun wP cP) (Parts.fmK (A.m - 1)).

Limits: the two premises named. Nothing is said on the program's routines on machine words.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Relation
import Cb.Pv.KeyLookup.PartsStd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp

/-- One step of the parts' steps in the course. -/
def stepP (D : Dt) (j : ℕ) (s : Cs) : Cs :=
  { (pscC D (onValue s.rest) sProd false 0 id s).2 with
    roots := Function.update (pscC D (onValue s.rest) sProd false 0 id s).2.roots j
      ((pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 0 noClaim)
    rest := (pscC D (onValue s.rest) sProd false 0 id s).1.ends.getD 1 noClaim }

theorem cPart_succ (D : Dt) : ∀ (n j : ℕ) (s : Cs),
    cPart D (n + 1) j s = stepP D (j + n) (cPart D n j s)
  | 0, _, _ => rfl
  | n + 1, j, s => by
    show cPart D (n + 1) (j + 1) (stepP D j s) = _
    rw [cPart_succ D n (j + 1) (stepP D j s)]
    have e : j + 1 + n = j + (n + 1) := by omega
    rw [e]
    rfl

theorem len1 {α : Type} : ∀ l : List α, l.length = 1 → ∃ a, l = [a]
  | [a], _ => ⟨a, rfl⟩

theorem len2 {α : Type} : ∀ l : List α, l.length = 2 → ∃ a b, l = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

theorem len0 {α : Type} : ∀ l : List α, l.length = 0 → l = []
  | [], _ => rfl

/-- A flat list that fits a step's formats. -/
theorem fits_step (g : List (RV GE)) (h : fitsAll Parts.fmStep g = true) :
    ∃ mu eps q1 q2 be v0 v1, g = [([mu], [eps]), ([q1, q2], [be]), ([v0, v1], [])] := by
  have hl := fitsAll_len _ _ h
  match g, hl, h with
  | [r0, r1, r2], _, h =>
    have h' : (Fm.fits ⟨1, 1, false⟩ r0 = true ∧ Fm.fits ⟨2, 1, true⟩ r1 = true) ∧
        Fm.fits ⟨2, 0, false⟩ r2 = true := by
      simpa [fitsAll, Parts.fmStep, and_assoc] using h
    obtain ⟨a0, b0, _⟩ := (Fm.fits_iff _ _).1 h'.1.1
    obtain ⟨a1, b1, _⟩ := (Fm.fits_iff _ _).1 h'.1.2
    obtain ⟨a2, b2, _⟩ := (Fm.fits_iff _ _).1 h'.2
    obtain ⟨mu, e0⟩ := len1 _ a0
    obtain ⟨eps, e1⟩ := len1 _ b0
    obtain ⟨q1, q2, e2⟩ := len2 _ a1
    obtain ⟨be, e3⟩ := len1 _ b1
    obtain ⟨v0, v1, e4⟩ := len2 _ a2
    have e5 := len0 _ b2
    exact ⟨mu, eps, q1, q2, be, v0, v1, by
      rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5]⟩

theorem fmK_length : ∀ k, (Parts.fmK k).length = 3 * k
  | 0 => rfl
  | k + 1 => by
    show (Parts.fmK k ++ Parts.fmStep).length = _
    rw [List.length_append, fmK_length k]
    show 3 * k + 3 = _
    omega

/-- The step of the course at three rounds written out. -/
theorem stepP_at (D : Dt) (j : ℕ) (s : Cs) (mu eps q1 q2 be v0 v1 : GE) (t : List (RV GE))
    (hr : s.rounds = ([mu], [eps]) :: ([q1, q2], [be]) :: ([v0, v1], []) :: t) :
    stepP D j s =
      { s with
        rounds := t
        own := s.own + 5
        rows := s.rows ++ [⟨(PscF.outOf (onValue s.rest) sProd
            [D.ms s.own, D.ms (s.own + 1), D.ms (s.own + 2), D.ms (s.own + 3), D.ms (s.own + 4)]
            ⟨mu, eps, [([q1, q2], be)], [v0, v1]⟩).rowMasks, [],
          (PscF.outOf (onValue s.rest) sProd
            [D.ms s.own, D.ms (s.own + 1), D.ms (s.own + 2), D.ms (s.own + 3), D.ms (s.own + 4)]
            ⟨mu, eps, [([q1, q2], be)], [v0, v1]⟩).rowTarget⟩]
        roots := Function.update s.roots j ⟨[], [(D.ms (s.own + 3), be)], v0⟩
        rest := ⟨[], [(D.ms (s.own + 4), be)], v1⟩ } := by
  obtain ⟨rounds, own, idx, rows, alpha, rest, pow, top, bit, planes, roots, leaves, zt⟩ := s
  subst hr
  rfl

section
variable (A : Dat GE) (sl : Slot → A.J) (D : Dt)
variable (wP : ℕ → PIdx (([] : List (PFmt GE)) ++ [pDummy GE 2]) → A.J) (cP : ℕ → Bool → A.J)

/-- Where the steps' places stand. -/
def PlacesAt (b : ℕ) : Prop :=
  ∀ l, l < A.m - 1 →
    wP l Parts.i0 = sl (D.ms (b + 5 * l)) ∧ wP l Parts.i1 = sl (D.ms (b + 5 * l + 1)) ∧
      wP l Parts.i2 = sl (D.ms (b + 5 * l + 2)) ∧ cP l false = sl (D.ms (b + 5 * l + 3)) ∧
      cP l true = sl (D.ms (b + 5 * l + 4))

theorem placesAt_std (b : ℕ) :
    PlacesAt A sl D (Parts.wStd (fun k => sl (D.ms k)) b) (Parts.cStd (fun k => sl (D.ms k)) b) b :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- What holds after k steps. -/
structure Kept (s : Cs) (k : ℕ) (s' : Cs) (a : Parts.Acc GE A.J) : Prop where
  rounds : s'.rounds = s.rounds.drop (3 * k)
  own : s'.own = s.own + 5 * k
  idx : s'.idx = s.idx
  alpha : s'.alpha = s.alpha
  planes : s'.planes = s.planes
  mf : a.mf = rdMF sl s'.rest.masks
  tg : a.tg = s'.rest.value
  roots : ∀ i, i < k → a.roots i = rdS A sl (s'.roots i)
  rows : a.rows = s'.rows.map (rdRow A sl)

theorem take3 {α : Type} (l : List α) (a b c : α) (h : l.take 3 = [a, b, c]) :
    l = a :: b :: c :: l.drop 3 := by
  have e := List.take_append_drop 3 l
  rw [h] at e
  exact e.symm

theorem kept_chain (s : Cs) (a0 : Parts.Acc GE A.J) (hP : PlacesAt A sl D wP cP s.own)
    (h0 : Kept A sl s 0 s a0) : ∀ k, k ≤ A.m - 1 →
      fitsAll (Parts.fmK k) (s.rounds.take (Parts.fmK k).length) = true →
      Kept A sl s k (cPart D k 0 s)
        (Parts.accK wP cP k a0 (s.rounds.take (Parts.fmK k).length))
  | 0, _, _ => h0
  | k + 1, hk, hf => by
    have hlen : (Parts.fmK (k + 1)).length = (Parts.fmK k).length + 3 := by
      rw [fmK_length, fmK_length]
      omega
    obtain ⟨g1, g2⟩ := fitsAll_app (Parts.fmK k) Parts.fmStep _ hf
    rw [hlen, take_take_add] at g1
    rw [hlen, drop_take_add] at g2
    have ih := kept_chain s a0 hP h0 k (by omega) g1
    obtain ⟨mu, eps, q1, q2, be, v0, v1, hg⟩ := fits_step _ g2
    have hr : (cPart D k 0 s).rounds =
        ([mu], [eps]) :: ([q1, q2], [be]) :: ([v0, v1], []) ::
          (s.rounds.drop (Parts.fmK k).length).drop 3 := by
      rw [ih.rounds, ← fmK_length k]
      exact take3 _ _ _ _ hg
    have ea : Parts.accK wP cP (k + 1) a0 (s.rounds.take (Parts.fmK (k + 1)).length) =
        Parts.stepAcc (wP k Parts.i0) (wP k Parts.i1) (wP k Parts.i2) (cP k false) (cP k true) k
          (Parts.accK wP cP k a0 (s.rounds.take (Parts.fmK k).length))
          [([mu], [eps]), ([q1, q2], [be]), ([v0, v1], [])] := by
      show Parts.stepAcc _ _ _ _ _ k
        (Parts.accK wP cP k a0 ((s.rounds.take (Parts.fmK (k + 1)).length).take
          (Parts.fmK k).length))
        ((s.rounds.take (Parts.fmK (k + 1)).length).drop (Parts.fmK k).length) = _
      rw [hlen, take_take_add, drop_take_add, hg]
    obtain ⟨p0, p1, p2, p3, p4⟩ := hP k (by omega)
    have eo : (cPart D k 0 s).own = s.own + 5 * k := ih.own
    have es := part_step sl (cPart D k 0 s).rest (D.ms (s.own + 5 * k))
      (D.ms (s.own + 5 * k + 1)) (D.ms (s.own + 5 * k + 2)) (D.ms (s.own + 5 * k + 3))
      (D.ms (s.own + 5 * k + 4)) mu eps q1 q2 be v0 v1 k _ ih.mf ih.tg
    have ec := stepP_at D (0 + k) (cPart D k 0 s) mu eps q1 q2 be v0 v1 _ hr
    rw [eo] at ec
    rw [cPart_succ, ec, ea, p0, p1, p2, p3, p4]
    have es' : Parts.stepAcc (sl (D.ms (s.own + 5 * k))) (sl (D.ms (s.own + 5 * k + 1)))
        (sl (D.ms (s.own + 5 * k + 2))) (sl (D.ms (s.own + 5 * k + 3)))
        (sl (D.ms (s.own + 5 * k + 4))) k
        (Parts.accK wP cP k a0 (s.rounds.take (Parts.fmK k).length))
        [([mu], [eps]), ([q1, q2], [be]), ([v0, v1], [])] = _ := es
    rw [es']
    refine ⟨?_, ?_, ih.idx, ih.alpha, ih.planes, rfl, rfl, fun i hi => ?_, ?_⟩
    · show (s.rounds.drop (Parts.fmK k).length).drop 3 = _
      rw [List.drop_drop]
      exact congrArg (fun n => s.rounds.drop n) (by rw [fmK_length]; omega)
    · show s.own + 5 * k + 5 = _
      omega
    · by_cases hik : i = k
      · subst hik
        show (if i = i then _ else _) =
          rdS A sl (Function.update (cPart D i 0 s).roots (0 + i) _ i)
        rw [if_pos rfl, Nat.zero_add, Function.update_self]
        rfl
      · show (if i = k then _ else _) =
          rdS A sl (Function.update (cPart D k 0 s).roots (0 + k) _ i)
        rw [if_neg hik, Nat.zero_add, Function.update_of_ne hik]
        exact ih.roots i (by omega)
    · show _ ++ [_] = ((cPart D k 0 s).rows ++ [_]).map (rdRow A sl)
      rw [List.map_append, ih.rows]
      refine congrArg _ ?_
      show [_] = [rdRow A sl _]
      refine congrArg (fun r => [r]) (congrArg₂ Cb.LdLkp.Row.mk (funext fun j => ?_) rfl)
      show _ = rdMF sl _ j + 0
      rw [add_zero]

/-- The parts' field of the bundle. -/
theorem parts_goes (st : A.St) (own idx : ℕ) (hS : D.S = A.toPub)
    (hP : PlacesAt A sl D wP cP (own + ownAt A.toPub 1)) :
    Goes (Sim A sl st own idx 1) (Sim A sl st own idx 2) (cParts D) (A.partsRun wP cP)
      (Parts.fmK (A.m - 1)) := by
  intro s x h hf
  have hm : D.S.m = A.m := by rw [hS]
  have hP' : PlacesAt A sl D wP cP s.own := by
    rw [h.own]
    exact hP
  have hall := h.all rfl
  have k0 : Kept A sl s 0 s ⟨x.all.mf, x.all.tg, x.roots, x.rows⟩ :=
    ⟨rfl, rfl, rfl, rfl, rfl, congrArg SCl.mf hall, congrArg SCl.tg hall,
      fun i hi => absurd hi (Nat.not_lt_zero i), h.rows⟩
  have K := kept_chain A sl D wP cP s _ hP' k0 (A.m - 1) (Nat.le_refl _) hf
  have ec : cParts D s = { cPart D (A.m - 1) 0 s with
      roots := Function.update (cPart D (A.m - 1) 0 s).roots (A.m - 1)
        (cPart D (A.m - 1) 0 s).rest } := by
    show ({ cPart D (D.S.m - 1) 0 s with
      roots := Function.update (cPart D (D.S.m - 1) 0 s).roots (D.S.m - 1)
        (cPart D (D.S.m - 1) 0 s).rest } : Cs) = _
    rw [hm]
  rw [ec]
  refine ⟨⟨h.st, h.al.trans K.alpha.symm, K.rows, ?_, ?_, fun e => absurd e (by decide),
    fun _ j hj => ?_, fun _ _ i hi => ?_, fun e => absurd e (by decide),
    fun e => absurd e (by decide), fun e => absurd e (by decide)⟩, ?_⟩
  · have e : ownAt A.toPub 2 = ownAt A.toPub 1 + 5 * (A.m - 1) := by simp only [ownAt]
    show (cPart D (A.m - 1) 0 s).own = own + ownAt A.toPub 2
    rw [e, K.own, h.own]
    omega
  · exact K.idx.trans h.idx
  · show x.planes j = rdS A sl ((cPart D (A.m - 1) 0 s).planes j)
    rw [K.planes]
    exact h.planes (by decide) j hj
  · by_cases him : i < A.m - 1
    · show (if i < A.m - 1 then _ else _) =
        rdS A sl (Function.update (cPart D (A.m - 1) 0 s).roots (A.m - 1) _ i)
      rw [if_pos him, Function.update_of_ne (by omega)]
      exact K.roots i him
    · have e : i = A.m - 1 := by omega
      subst e
      show (if A.m - 1 < A.m - 1 then _ else _) =
        rdS A sl (Function.update (cPart D (A.m - 1) 0 s).roots (A.m - 1) _ (A.m - 1))
      rw [if_neg him, Function.update_self]
      exact congrArg₂ SCl.mk K.mf K.tg
  · show (cPart D (A.m - 1) 0 s).rounds = _
    rw [K.rounds, fmK_length]

end
end Lk6.Mid

#print axioms Lk6.Mid.cPart_succ
#print axioms Lk6.Mid.stepP_at
#print axioms Lk6.Mid.kept_chain
#print axioms Lk6.Mid.parts_goes
