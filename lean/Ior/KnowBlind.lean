-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowBlind.lean: a yardstick: what knowledge soundness says without running times lies in the
type of the extractor.

A toy, four statements on it, one general lemma; all proved here.
The question: Lean models no running time. An extractor that may read the whole statement can pick a
witness by choice whenever there is one. Is a knowledge clause then more than soundness?
(1) For `Know` (Ior/Know.lean), over all extractors: no (`know_by_choice`). The extractor of `Know`
may read the whole input statement. For every reduction that is round-by-round sound for the
languages of two relations, the type of input witnesses being non-empty, `Know` holds with the same
errors and the extractor "some witness of the input statement, by choice", which reads no
transcript. So `Know` says more than soundness only through the extractor that a theorem names;
Ior/KnowTest.lean tells a right extractor from a wrong one, it does not separate `Know` from
soundness over all extractors.
(2) For `SndBK` (Ior/Batch.lean): yes, by type (`forced`, `reads`). There the extractor wit is given
the explicit instance and the prover's oracles, and by type nothing else: not the external oracle y,
no verifier message, no plain part. In the toy no function of the explicit instance alone is a
witness for every y: there neither choice nor search can replace reading (`forced`, under its
hypotheses). (That the relation depends on y is not enough: `blind_passes`: for "w = y or w = 1" the
constant extractor 1 passes.)
The toy (`BlindTest.Q`, `BlindTest.R`), for every finite non-empty set C of verifier messages: the
external oracle is one bit y; the witness of (x, y) is y itself, so every statement has a witness
and soundness for the language is empty; the prover sends one bit as an oracle; the verifier accepts
if and only if that bit equals y.

Main names (in `Iop.BlindTest`; `SndBK` stands at early = id, late = none throughout; the number of
slots is its first argument N):
  `forced`: any wit with which the toy has `SndBK`, for one slot, at an error below the number of
    values of the verifier message returns the prover's bit, on every transcript.
  `reads`: the wit that returns the prover's bit has `SndBK` with error 0 (so `forced` is not about
    nothing).

Limits: what this means for the library. Blind in this sense, by type: the argument `wit` of
`BatchProtocol.SoundK` (Hiop/Interface.lean: the instance and the oracles sent). Its clauses say that a valid
witness stands in the oracles that the prover sent.





Not blind: the extractors of `IOR.Good` (Ior/Chain.lean) are handed the implicit instance y, the
oracles sent and the output witness; the extractor of `Know` may read the whole statement and
transcript. For these, (1) applies: the content is in the name.
In the compiled argument's definition (ZKCP/Gen.lean) the witness extractor is handed the key and
the committer's trace; blindness to the index is gone there, and where a witness can be recomputed
from index and instance the clause is free (CompileK/Recompute.lean).
This file says nothing on running times. The toy has one slot and one local round (`reads` and
`blind_passes` are stated for any number of slots).
Terms: lean/GLOSSARY.md.
-/
import Ior.BatchKProofsBad
import Ior.KnowTest

set_option autoImplicit false

namespace Iop

/-! ## 1. `Know` with an extractor by choice is soundness -/

namespace Spec

open Classical in
/-- States: for every reduction that is sound for the languages of two relations, the type of input
witnesses being non-empty, `Know` holds with an extractor by choice, which reads no transcript, same
errors. -/
def know_by_choice : Prop :=
  ∀ (A B WA WB : Type) [Nonempty WA] (K : Reduction A B) (RA : A → WA → Prop)
      (RB : B → WB → Prop) (ε : Err K.shape),
    K.Sound (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) ε →
    K.Know (fun _ => True) RA RB (fun a _ _ => Classical.epsilon (RA a)) ε

end Spec

theorem know_by_choice : Spec.know_by_choice := fun _ _ _ _ _ _ _ _ _ h =>
  Reduction.Know.of_sound h _ (fun _ _ hL => Classical.epsilon_spec hL) (fun _ w hw => ⟨w, hw⟩)

/-! ## 2. The toy -/

namespace BlindTest
open Prob

/-- the external oracle: one bit -/
abbrev extBit : ExtSpec := ⟨Bool, Unit, Bool, fun y _ => y⟩

/-- One round: the prover sends one bit as an oracle; the verifier accepts if and only if it equals
the external bit. -/
def Q (C : Type) [Fintype C] [Nonempty C] : BatchInteractiveOracleProof Unit extBit where
  loc :=
    { shape := [KnowTest.oracleBit C]
      blinded := fun _ => false
      extReads := fun _ _ => {()}
      reads := fun _ _ _ => {(Sum.inl () : Unit ⊕ Empty)}
      accept := fun _ (y : Bool) (τ : (Bool × Unit) × C × Unit) => τ.1.1 == y }
  ann := RoundSplits.allLocal _

/-- The witness of (x, y) is y itself: every statement has a witness. -/
def R : Unit → extBit.Str → Bool → Prop := fun _ y w => w = y

/-- The full transcript in which the prover sends the bit b and the verifier c. -/
def tr (C : Type) [Fintype C] [Nonempty C] (b : Bool) (c : C) : Tr (Q C).loc.shape :=
  (((b, ()), c, ()) : (KnowTest.oracleBit C).Msg × C × Unit)

/-- The extractor that returns the prover's bit. -/
def witRead (C : Type) [Fintype C] [Nonempty C] : Unit → Orcs (Q C).loc.shape → Bool := fun _ o =>
  (o (Sum.inl ()) : Bool)

namespace Spec

/-- States: whatever extractor meets `SndBK`, for one slot, with an error below the number of
verifier messages returns the prover's bit. -/
def forced : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C] (wit : Unit → Orcs (Q C).loc.shape → Bool) (e : ℕ), e <
      Fintype.card C →
    (Q C).SndBK 1 id none R wit (e, ()) → ∀ (b : Bool) (c : C), wit () (tr C b c).read = b

/-- States: the extractor that returns the prover's bit meets `SndBK` with error 0, for any number
of slots. -/
def reads : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C] (N : ℕ), (Q C).SndBK N id none R (witRead C) (0, ())

/-- States: the toy's verifier depends on the oracles only at the positions that it declares. -/
def isLocal : Prop := ∀ (C : Type) [Fintype C] [Nonempty C], (Q C).loc.IsLocal

/-- That the relation depends on y is not enough. States: for "w = y or w = 1" the constant
extractor 1 meets `SndBK` with error 0. -/
def blind_passes : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C] (N : ℕ),
    (Q C).SndBK N id none (fun _ y w => w = y ∨ w = true) (fun _ _ => true) (0, ())

end Spec

theorem forced : Spec.forced := by
  intro C _ _ wit e he h b c
  have hd := one_of_sndBK Unit Bool extBit (Q C) 1 R wit (e, ()) Nat.one_pos h () b
  have h2 : cnt (fun c : C =>
        ¬ ((Q C).loc.accept () b (tr C b c) = true → R () b (wit () (tr C b c).read))) ≤ e :=
    hd (b, ())
  by_contra hn
  have h3 : Fintype.card C ≤ e := by
    refine le_trans (le_of_eq cnt_true.symm) (le_trans (cnt_mono fun c' _ hall => ?_) h2)
    have h4 := hall (show (b == b) = true by simp)
    apply hn
    -- the oracles of a transcript do not hold the verifier message
    have e1 : (tr C b c).read = (tr C b c').read := by
      funext p
      cases p with
      | inl p => rfl
      | inr p => exact nomatch p
    rw [e1]
    exact h4
  omega

theorem reads : Spec.reads := by
  intro C _ _ N
  refine BatchInteractiveOracleProof.sndBK_of_badFam (Q C) N R (witRead C) (0, ()) (fun _ _ => BadFam.empty _) ?_ ?_
  · intro _ y (τ : (Bool × Unit) × C × Unit) _ hacc
    have hacc' : (τ.1.1 == y) = true := hacc
    exact beq_iff_eq.1 hacc'
  · intro y x
    refine jWithin_of_within N RAnn.allLocal (fun _ => rfl) _ _ _ fun j p hp => ?_
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact BadFam.empty_within _ _

theorem isLocal : Spec.isLocal := by
  intro C _ _ _ y y' (τ : (Bool × Unit) × C × Unit) (τ' : (Bool × Unit) × C × Unit) _ _ he ho
  have h1 : y = y' := he () (Finset.mem_singleton_self _)
  have h2 : τ.1.1 = τ'.1.1 := ho (Sum.inl ()) (Finset.mem_singleton_self _)
  show (τ.1.1 == y) = (τ'.1.1 == y')
  rw [h1, h2]

theorem blind_passes : Spec.blind_passes := by
  intro C _ _ N
  refine BatchInteractiveOracleProof.sndBK_of_badFam
    (Q C) N _ _ (0, ()) (fun _ _ => BadFam.empty _) (fun _ _ _ _ _ => Or.inr rfl) ?_
  intro y x
  refine jWithin_of_within N RAnn.allLocal (fun _ => rfl) _ _ _ fun j p hp => ?_
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact BadFam.empty_within _ _

end BlindTest

end Iop
