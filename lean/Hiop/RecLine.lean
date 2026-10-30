-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecLine.lean: this file writes the record phase of the holographic interactive oracle proof as
two rounds in front of a protocol, and states index binding of such a phase as one round-by-round
statement.

Terms, statements and proofs.

Hiop/RecInterface.lean keeps the record phase outside the three protocols: it has the set of seeds,
the set of answers and the honest answer, and the record is in the explicit instances. Whoever runs
the object (a compiler, a program) plays the phase as two rounds in front of the first protocol on a
new encoded index: the offline IOP for the first, the link for a further one. [The written
description says otherwise of the compiler: there the seed is the answer of a record oracle at the
root alone, a query of its own, before the chains, and each chain's first query holds the record
beside the root. So "two rounds in front" is a form of the statement on the level of the IOP (index
binding of a phase in one line); it is not how the compiled scheme plays the phase there. The
theorems below stand as statements on IOPs.]

The prover has lost (`Doomed`), at a list of errors, towards a property of full transcripts: at a
full transcript, if the property holds; earlier, if, whatever it sends next, at most that round's
error many values of the next verifier message lead to a position in which it has not lost. A list
of errors (`Err`) holds one number for each round, a count, not a probability: how many values of
that round's verifier message may let a prover that has lost (`Doomed`) escape.

Main names:
  `recShape Seed Ans a0`: the two rounds, nothing merged: (the prover sends nothing; the verifier
    draws the seed), (the prover sends the answer, in the clear; the verifier sends nothing). a0: a
    fixed answer, the round's substitute. Seed is a finite set that is not empty.
  `Q.led rc a0`: the IOP Q with the two rounds in front. Its instance y is Q's, and holds the
    claimed record rc y of the new encoded index (offline: the instance itself; link: its second
    component). The verifier compares the claimed record with the seed drawn and the answer sent,
    then decides as Q's. It reads what Q's verifier reads.
A prover names the claimed record only after it has seen the seed. So the first two statements below
speak of all claimed records at once, inside the goal on transcripts:
  `Spec.rec_line_test`: index binding of the offline phase in one line. Under
    `L.SoundAtR Rno wit eR εT εL εB`: for every word the prover has lost, at the start, towards "for
    every claimed record: the verifier rejects, or the index decoder answers". The input relation is
    empty, the output relation holds the statements at which the index decoder says none. Errors:
    the record clause's eR (round of the seed), 0 (round of the answer), then the offline list.
  `Spec.rec_line_link`: the same for a further encoded index. Under
    `L.SoundAtR Rno wit eR εT εL εB`: for every pair of words and every record of the first at which
    the index decoder answers, towards "for every claimed record of the further one: the verifier
    rejects, or the further one decodes to the same index". Errors: eR, 0, then the link's list.
  `Spec.rec_line_honest`: see its docstring.

Notation: `L` : `HolographicProtocol I X` (Hiop/RecInterface.lean): the algorithms, with a record phase after each
encoded index, and the honest sides; `eR` : ℕ: in `HolographicProtocol.SoundAtR` (Hiop/RecInterface.lean), seeds;
`εT`, `εL`, `εB` : `Err` of a shape: in `HolographicProtocol.SoundAtR` (Hiop/RecInterface.lean), the three lists.

Limits: no converse: the record clause and the offline clause are not recovered from the one line.
With rounds counted by non-empty verifier messages the entry 0 falls. Zero knowledge: once message
and pads are chosen, the seed determines the answer; somebody who may only read a few symbols of the
word cannot compute it. So these two rounds belong to no IOP that has a zero-knowledge item: record
and encoded index are simulated as one thing (Hiop/RecWhole.lean).
Terms: lean/GLOSSARY.md.
-/
import Hiop.RecInterface
import Blocks.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob Blocks

section Terms
variable (Seed Ans : Type) [Fintype Seed] [Nonempty Seed] (a0 : Ans)

/-- The two rounds of a record phase. -/
abbrev recShape : Shape := [plainRound Unit Seed (), plainRound Ans Unit a0]

variable {Seed Ans a0}

/-- the record in a transcript that begins with the two rounds -/
def recTr {s : Shape} (τ : Tr (recShape Seed Ans a0 ++ s)) : Seed × Ans := (τ.2.1, τ.2.2.1.2)
/-- what follows the two rounds -/
def recRest {s : Shape} (τ : Tr (recShape Seed Ans a0 ++ s)) : Tr s := τ.2.2.2.2

variable {Y : Type} {E : ExtSpec}

open Classical in
/-- Q with the record phase in front; rc y is the claimed record. -/
def InteractiveOracleProof.led (Q : InteractiveOracleProof Y E) (rc : Y → Seed × Ans) (a0 : Ans) : InteractiveOracleProof Y E where
  shape := recShape Seed Ans a0 ++ Q.shape
  blinded := fun p => match p with
    | .inl e => e.elim
    | .inr (.inl e) => e.elim
    | .inr (.inr p) => Q.blinded p
  extReads := fun y ρ => Q.extReads y ρ.2.2
  reads := fun y ρ pl => (Q.reads y ρ.2.2 pl.2.2).image fun p => .inr (.inr p)
  accept := fun y e τ => decide (recTr τ = rc y) && Q.accept y e (recRest τ)

end Terms

variable {I X Wn : Type}

namespace Spec

/-- Index binding of the offline phase in one line. -/
def rec_line_test : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (a0 : L.OutOfDomainAnswer),
    L.SoundAtR Rno wit eR εT εL εB →
    ∀ y, Doomed (recShape L.OutOfDomainSeed L.OutOfDomainAnswer a0 ++ L.offline.shape) (eR, 0, εT) fun τ =>
      ∀ rec : L.Rec, (L.offline.led id a0).accept rec y τ = true → L.decodeIndex y rec ≠ none

/-- The same for a further encoded index and its link. -/
def rec_line_link : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (a0 : L.OutOfDomainAnswer),
    L.SoundAtR Rno wit eR εT εL εB →
    ∀ (y : (twoExternalStrings L.wordLength L.Symbol).Str) (rec0 : L.Rec), L.decodeIndex y.1 rec0 ≠ none →
      Doomed (recShape L.OutOfDomainSeed L.OutOfDomainAnswer a0 ++ L.link.shape) (eR, 0, εL) fun τ =>
        ∀ rec : L.Rec,
          (L.link.led Prod.snd a0).accept (rec0, rec) y τ = true → L.decodeIndex y.2 rec = L.decodeIndex y.1 rec0

/-- On the record that the two rounds hold, the led verifier decides as Q's (Seed not empty). -/
def rec_line_honest : Prop :=
  ∀ (Seed Ans Y : Type) [Fintype Seed] [Nonempty Seed] (E : ExtSpec) (Q : InteractiveOracleProof Y E)
      (rc : Y → Seed × Ans) (a0 : Ans) (y : Y) (e : E.Str)
      (τ : Tr (recShape Seed Ans a0 ++ Q.shape)),
    recTr τ = rc y → (Q.led rc a0).accept y e τ = Q.accept y e (recRest τ)

end Spec

open Classical in
theorem led_accept {Seed Ans Y : Type} [Fintype Seed] [Nonempty Seed] {E : ExtSpec} (Q : InteractiveOracleProof Y E)
    (rc : Y → Seed × Ans) (a0 : Ans) (y : Y) (e : E.Str)
    (τ : Tr (recShape Seed Ans a0 ++ Q.shape)) :
    (Q.led rc a0).accept y e τ = true ↔ recTr τ = rc y ∧ Q.accept y e (recRest τ) = true := by
  show (decide (recTr τ = rc y) && Q.accept y e (recRest τ)) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_iff]

open Classical in
theorem rec_line_honest : Spec.rec_line_honest := by
  intro Seed Ans Y _ _ E Q rc a0 y e τ h
  show (decide (recTr τ = rc y) && Q.accept y e (recRest τ)) = _
  rw [decide_eq_true h, Bool.true_and]

/-- The two rounds in front of a game (Seed not empty): if for all but at most e seeds, and every
answer, the prover has lost the rest, it has lost the whole, with the errors e, 0 in front. -/
theorem doomed_rec {Seed Ans : Type} [Fintype Seed] [Nonempty Seed] (a0 : Ans) (s : Shape) (e : ℕ)
    (ε : Err s) (badSeed : Seed → Prop) (goal : Seed × Ans → Tr s → Prop) (hb : cnt badSeed ≤ e)
    (h : ∀ sd a, ¬ badSeed sd → Doomed s ε (goal (sd, a))) :
    Doomed (recShape Seed Ans a0 ++ s) (e, 0, ε) fun τ => goal (recTr τ) (recRest τ) := by
  intro m
  refine le_trans (cnt_mono fun sd hsd => ?_) hb
  by_contra hn
  apply hsd
  intro m2
  refine le_of_eq (cnt_false fun u hu => hu ?_)
  exact h sd m2.2 hn

theorem rec_line_test : Spec.rec_line_test := by
  intro I X Wn L Rno wit eR εT εL εB a0 h y
  refine Doomed.mono _ _ ?_
    (doomed_rec a0 L.offline.shape eR εT (fun s => L.hasCollisionAt y s)
      (fun rec τ => L.offline.accept rec y τ = true → L.decodeIndex y rec ≠ none) (h.rcd y) ?_)
  · intro τ hτ rec hacc
    obtain ⟨h1, h2⟩ := (led_accept L.offline id a0 rec y τ).1 hacc
    have h1 : recTr τ = rec := h1
    subst h1
    exact hτ h2
  · intro sd a hsd
    by_cases hd : L.decodeIndex y (sd, a) = none
    · refine Doomed.mono _ _ ?_ (h.sndT (sd, a) y fun hh => hh.elim hsd fun h2 => h2 hd)
      intro τ hτ hacc
      rw [hτ] at hacc
      cases hacc
    · exact Doomed.of_forall _ _ fun _ _ => hd

theorem rec_line_link : Spec.rec_line_link := by
  intro I X Wn L Rno wit eR εT εL εB a0 h y rec0 h0
  refine Doomed.mono _ _ ?_
    (doomed_rec a0 L.link.shape eR εL (fun s => L.hasCollisionAt y.2 s)
      (fun rec τ => L.link.accept (rec0, rec) y τ = true → L.decodeIndex y.2 rec = L.decodeIndex y.1 rec0)
      (h.rcd y.2) ?_)
  · intro τ hτ rec hacc
    obtain ⟨h1, h2⟩ := (led_accept L.link Prod.snd a0 (rec0, rec) y τ).1 hacc
    have h1 : recTr τ = rec := h1
    subst h1
    exact hτ h2
  · intro sd a hsd
    by_cases hd : L.decodeIndex y.2 (sd, a) = L.decodeIndex y.1 rec0
    · exact Doomed.of_forall _ _ fun _ _ => hd
    · refine Doomed.mono _ _ ?_
        (h.sndL (rec0, (sd, a)) y fun hh => hh.elim h0 fun h2 => h2.elim hsd hd)
      intro τ hτ hacc
      rw [hτ] at hacc
      cases hacc

end Iop
