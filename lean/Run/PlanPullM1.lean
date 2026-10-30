-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullM1.lean: an instance: the conditions on a wiring hold, with challenges as hash blocks,
at the description of the first toy of the programs. In that description 27 of 30 rounds draw field
elements. The first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i;
Fmt/M1Types.lean). "The programs" are the C++ implementation that comes with this Lean code.

Lemmas, two statements (`Spec.planPull_count`, `Spec.planPull_m1`) and proofs.

A wiring is the data that say how deep the trees are, where a position stands among a tree's leaves,
and how blocks of a hash answer give a verifier message (`ProtocolQueryLayout`, Iop/BatchWire.lean); its
conditions are `ProtocolQueryLayout.OKG`. With challenges as hash blocks (`ckP`, Run/PlanPull.lean) a round's
verifier message is its 256-bit blocks, and reads and decision apply the sampling rule; the library
calls the step from challenges as sampled values to challenges as hash blocks "pull". A description
is a value of `Fmt.Spec` (Fmt/Rules8.lean).

Why: `planPull_okg` (Run/PlanPull.lean) has two hypotheses: every round's number of blocks is at
most K; every round's work is at most 64 bits. Here the first holds at K := the greatest of these
numbers, for every list of rounds (`le_kMax`); both hold at the toy's description (`specOf toyPar`,
Fmt/M1Plan.lean), whatever its configuration's digest and further parameter items are.

Main names:
  `Spec.planPull_count`: at the toy's sizes: 30 rounds; 27 draw at least one element of the
    extension field.
  `Spec.planPull_m1`: `(PQ.wqS (ckP .two) K (chalP .two K) ds dec).OKG` at ds := the rounds' data of
    the toy's description, K := their greatest number of blocks, for every decision dec; the same at
    the tiny parameters of this library's own.

Limits: what the head of Run/PlanPull.lean lists as not said is not said here either. In particular
this file says nothing on soundness, it does not say that the protocol is the library's pull, and it
says nothing on a run. That the description is the programs' own is not stated here: it was written
from a restatement of the programs' description of the toy and from no file of the programs; see
Fmt/M1TheirsSpec.lean (`Theirs.specFull` is `specOf toyPar` at the programs' configuration and
items, by definition; a test (#guard) there reads the same sizes and description off the programs'
parameter bytes).
The tiny sizes here are this library's own (`tinyPar`, Fmt/M1Plan.lean), not those of the programs'
tiny files (`tinyPar'`, Fmt/M1Theirs.lean).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPull
import Fmt.M1Plan

set_option autoImplicit false

namespace Run
open Prob Iop

theorem foldl_max_le (g : PQ.RD → ℕ) :
    ∀ (ds : List PQ.RD) (a : ℕ),
      a ≤ ds.foldl (fun a d => max a (g d)) a ∧ ∀ d ∈ ds, g d ≤ ds.foldl (fun a d => max a (g d)) a
  | [], a => ⟨le_refl a, fun _ h => absurd h List.not_mem_nil⟩
  | d :: ds, a => by
    obtain ⟨h1, h2⟩ := foldl_max_le g ds (max a (g d))
    refine ⟨le_trans (le_max_left _ _) h1, fun d' hd' => ?_⟩
    rcases List.mem_cons.1 hd' with rfl | h
    · exact le_trans (le_max_right _ _) h1
    · exact h2 d' h

theorem le_kMax (kOf : _root_.Fmt.Entry → _root_.Fmt.Kind → ℕ) (ds : List PQ.RD) :
    ∀ d ∈ ds, kOf d.entry d.kind ≤ PQ.kMax kOf ds :=
  (foldl_max_le (fun d => kOf d.entry d.kind) ds 0).2

/-- The rounds' data of the toy's description; they do not depend on the configuration or on further
parameter items (`count_c`). -/
abbrev m1 (P : _root_.Fmt.M1.Par) : List PQ.RD :=
  PQ.rds (_root_.Fmt.M1.specOf P _root_.Fmt.zero32 [])
/-- the greatest number of blocks of a round -/
abbrev kM1 (P : _root_.Fmt.M1.Par) : ℕ := PQ.kMax (fun e k => (bsRound .two e k).b) (m1 P)

namespace Spec

def planPull_count : Prop :=
  (m1 _root_.Fmt.M1.toyPar).length = 30 ∧
  ((m1 _root_.Fmt.M1.toyPar).filter fun d => decide (0 < d.entry.drawE)).length = 27 ∧
  ∀ cfg others,
    PQ.rds (_root_.Fmt.M1.specOf _root_.Fmt.M1.toyPar cfg others) = m1 _root_.Fmt.M1.toyPar

def planPull_m1 : Prop :=
  ∀ dec : PQ.View → Bool,
    (PQ.wqS (ckP .two) (kM1 _root_.Fmt.M1.toyPar) (chalP .two (kM1 _root_.Fmt.M1.toyPar))
      (m1 _root_.Fmt.M1.toyPar) dec).OKG ∧
    (PQ.wqS (ckP .two) (kM1 _root_.Fmt.M1.tinyPar) (chalP .two (kM1 _root_.Fmt.M1.tinyPar))
      (m1 _root_.Fmt.M1.tinyPar) dec).OKG

end Spec

theorem count_a : (m1 _root_.Fmt.M1.toyPar).length = 30 := by decide +kernel
theorem count_b :
    ((m1 _root_.Fmt.M1.toyPar).filter fun d => decide (0 < d.entry.drawE)).length = 27 := by
  decide +kernel
/-- The rounds' data depend on a description's rounds and on the number of its first tree alone. -/
theorem rds_congr (S S' : _root_.Fmt.Spec)
    (h : S.rounds = S'.rounds) (hf : S.firstTree = S'.firstTree) : PQ.rds S = PQ.rds S' := by
  have ho : ∀ n, PQ.shapeOfOwn S n = PQ.shapeOfOwn S' n := fun n => by
    unfold PQ.shapeOfOwn PQ.allOpens
    rw [h]
  have hr : ∀ (l : List _root_.Fmt.Round) (n : ℕ), PQ.rdsFrom S n l = PQ.rdsFrom S' n l := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons r rs ih =>
      intro n
      simp only [PQ.rdsFrom, ho, hf, ih]
  unfold PQ.rds
  rw [hr, h]

theorem count_c (P : _root_.Fmt.M1.Par) (cfg : ByteArray) (others : List (String × ByteArray)) :
    PQ.rds (_root_.Fmt.M1.specOf P cfg others) = m1 P :=
  rds_congr _ _ rfl rfl

theorem planPull_count : Spec.planPull_count := ⟨count_a, count_b, count_c _⟩

theorem work_toy : (m1 _root_.Fmt.M1.toyPar).all (fun d => decide (d.entry.work ≤ 64)) = true := by
  decide +kernel
theorem work_tiny :
    (m1 _root_.Fmt.M1.tinyPar).all (fun d => decide (d.entry.work ≤ 64)) = true := by decide +kernel

theorem okgAt (P : _root_.Fmt.M1.Par)
    (h : (m1 P).all (fun d => decide (d.entry.work ≤ 64)) = true) (dec : PQ.View → Bool) :
    (PQ.wqS (ckP .two) (kM1 P) (chalP .two (kM1 P)) (m1 P) dec).OKG :=
  planPull_okg .two (kM1 P) (m1 P) dec (le_kMax (fun e k => (bsRound .two e k).b) (m1 P))
    fun d hd => of_decide_eq_true (List.all_eq_true.1 h d hd)

theorem planPull_m1 : Spec.planPull_m1 := fun dec => ⟨okgAt _ work_toy dec, okgAt _ work_tiny dec⟩

end Run
