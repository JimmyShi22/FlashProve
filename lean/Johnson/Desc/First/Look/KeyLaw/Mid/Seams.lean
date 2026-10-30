-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean: if each of the eight stretches of the course over the
field goes with the same stretch of the lookup's plain function, then the whole course goes with the
whole function.

Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean has the course over the field (our text of the
program's lookup, over the field; that the program's run, read in the field, is this course is
shown, under conditions on public data, in files that are not in this library yet): eight functions
on stands, each of which reads the next rounds and leaves the others. Cb/Pv/KeyLookup/AsmRuns.lean
has what the described lookup's verifier puts out: eight plain functions, each on its own rounds,
joined by `Flat.seqRun`. This file joins eight statements, one for each stretch, into one.

Main names:
  `glue`: the rule for one seam.
  `Sims A R D Sim st`: what is asked of the stretches. `Sim k` is a relation between a stand of the
  course and a state of the description, at the seam number k; it is a letter here. A stretch's
  field says: from related states, on rounds that fit the stretch's formats, the two functions lead
  to related states, and the course has taken just these rounds.
  `chn_sim`: under `Sims`, on every flat list whose first rounds fit all formats, the course's last
  stand and the description's last state on these rounds are related, and the course leaves the
  rounds behind them.

Limits. Nothing on any one stretch: `Sims` is a premise. Nothing on the program's blocks: both sides
of the statement are texts of ours.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Course
import Cb.Pv.KeyLookup.AsmRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

open OnBytes OnBytes.Slice Flat

/-- The first n of the first n + k members. -/
theorem take_take_add {α : Type} : ∀ (n k : ℕ) (l : List α), (l.take (n + k)).take n = l.take n
  | 0, _, _ => rfl
  | _ + 1, _, [] => by simp
  | n + 1, k, x :: l => by
    have e : n + 1 + k = n + k + 1 := by omega
    rw [e, List.take_succ_cons, List.take_succ_cons, List.take_succ_cons, take_take_add n k l]

/-- The members behind the first n among the first n + k. -/
theorem drop_take_add {α : Type} : ∀ (n k : ℕ) (l : List α),
    (l.take (n + k)).drop n = (l.drop n).take k
  | 0, k, l => by rw [Nat.zero_add]; rfl
  | n + 1, k, [] => by simp
  | n + 1, k, x :: l => by
    have e : n + 1 + k = n + k + 1 := by omega
    rw [e, List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons, drop_take_add n k l]

/-- A list that fits has as many rounds as there are formats. -/
theorem fitsAll_len : ∀ (a : List Fm) (f : List (RV GE)), fitsAll a f = true → f.length = a.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [fitsAll])
  | _ :: _, [], h => absurd h (by simp [fitsAll])
  | x :: a, v :: f, h => by
    have h' : x.fits v = true ∧ fitsAll a f = true := by simpa [fitsAll] using h
    rw [List.length_cons, List.length_cons, fitsAll_len a f h'.2]

/-- **One seam.** pa, ra: the course and the plain function up to the seam; c, rb: the next
stretch's. -/
theorem glue {X0 X X' : Type} (Φ : Cs → X → Prop) (Ψ : Cs → X' → Prop)
    (pa : List (RV GE) → Cs) (ra : X0 → List (RV GE) → X) (x0 : X0) (c : Cs → Cs)
    (rb : X → List (RV GE) → X') (fa fb : List Fm)
    (ha : ∀ f, fitsAll fa (f.take fa.length) = true →
      Φ (pa f) (ra x0 (f.take fa.length)) ∧ (pa f).rounds = f.drop fa.length)
    (hb : ∀ s x, Φ s x → fitsAll fb (s.rounds.take fb.length) = true →
      Ψ (c s) (rb x (s.rounds.take fb.length)) ∧ (c s).rounds = s.rounds.drop fb.length)
    (f : List (RV GE)) (hf : fitsAll (fa ++ fb) (f.take (fa ++ fb).length) = true) :
    Ψ (c (pa f)) (seqRun fa.length ra rb x0 (f.take (fa ++ fb).length)) ∧
      (c (pa f)).rounds = f.drop (fa ++ fb).length := by
  rw [List.length_append] at hf ⊢
  obtain ⟨h1, h2⟩ := fitsAll_app fa fb _ hf
  rw [take_take_add] at h1
  rw [drop_take_add] at h2
  obtain ⟨a1, a2⟩ := ha f h1
  rw [← a2] at h2
  obtain ⟨b1, b2⟩ := hb _ _ a1 h2
  refine ⟨?_, ?_⟩
  · show Ψ (c (pa f)) (rb (ra x0 ((f.take (fa.length + fb.length)).take fa.length))
      ((f.take (fa.length + fb.length)).drop fa.length))
    rw [take_take_add, drop_take_add, ← a2]
    exact b1
  · rw [b2, a2, List.drop_drop]

/-- What a stretch behind the first is asked: see the head. -/
def Goes {X X' : Type} (Φ : Cs → X → Prop) (Ψ : Cs → X' → Prop) (c : Cs → Cs)
    (r : X → List (RV GE) → X') (fm : List Fm) : Prop :=
  ∀ s x, Φ s x → fitsAll fm (s.rounds.take fm.length) = true →
    Ψ (c s) (r x (s.rounds.take fm.length)) ∧ (c s).rounds = s.rounds.drop fm.length

/-- **What is asked of the eight stretches.** own, idx: the mask entries taken before the lookup. -/
structure Sims (A : Dat GE) (R : RunD A) (D : Dt) (Sim : ℕ → Cs → A.XS → Prop) (st : A.St)
    (own idx : ℕ) : Prop where
  head : ∀ f, fitsAll R.fHead (f.take R.fHead.length) = true →
    Sim 1 (cHead D f own idx) (R.rHead st (f.take R.fHead.length)) ∧
      (cHead D f own idx).rounds = f.drop R.fHead.length
  parts : Goes (Sim 1) (Sim 2) (cParts D) R.rParts R.fParts
  join : Goes (Sim 2) (Sim 3) (cJoin D) R.rJoin R.fJoin
  keys : Goes (Sim 3) (Sim 4) (cKeys D) R.rKeys R.fKeys
  table : Goes (Sim 4) (Sim 5) (cTable D) R.rTable R.fTable
  clo : Goes (Sim 5) (Sim 6) (cClo D) R.rClo R.fClo
  zero : Goes (Sim 6) (Sim 7) (cZero D) R.rZero R.fZero
  bits : Goes (Sim 7) (Sim 8) (cBits D) R.rBits R.fBits

/-- **The whole course goes with the whole function.** -/
theorem chn_sim (A : Dat GE) (R : RunD A) (D : Dt) (Sim : ℕ → Cs → A.XS → Prop) (st : A.St)
    (own idx : ℕ) (h : Sims A R D Sim st own idx) (f : List (RV GE))
    (hf : fitsAll R.fm (f.take R.fm.length) = true) :
    Sim 8 (chnC D f own idx) (R.chn st (f.take R.fm.length)) ∧
      (chnC D f own idx).rounds = f.drop R.fm.length := by
  have p2 := glue (Sim 1) (Sim 2) _ R.rHead st (cParts D) R.rParts R.fHead R.fParts h.head h.parts
  have p3 := glue (Sim 2) (Sim 3) _ _ st (cJoin D) R.rJoin R.f2 R.fJoin p2 h.join
  have p4 := glue (Sim 3) (Sim 4) _ _ st (cKeys D) R.rKeys R.f3 R.fKeys p3 h.keys
  have p5 := glue (Sim 4) (Sim 5) _ _ st (cTable D) R.rTable R.f4 R.fTable p4 h.table
  have p6 := glue (Sim 5) (Sim 6) _ _ st (cClo D) R.rClo R.f5 R.fClo p5 h.clo
  have p7 := glue (Sim 6) (Sim 7) _ _ st (cZero D) R.rZero R.f6 R.fZero p6 h.zero
  exact glue (Sim 7) (Sim 8) _ _ st (cBits D) R.rBits R.f7 R.fBits p7 h.bits f hf

end Lk6.Mid

#print axioms Lk6.Mid.take_take_add
#print axioms Lk6.Mid.drop_take_add
#print axioms Lk6.Mid.fitsAll_len
#print axioms Lk6.Mid.glue
#print axioms Lk6.Mid.chn_sim
