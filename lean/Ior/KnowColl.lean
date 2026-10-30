-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowColl.lean: round-by-round knowledge soundness "on the statements with `on`, into the
statements with `on'`"; a bad event that is charged once; extractors where the relation determines
its witness.

The matter is round-by-round knowledge soundness of interactive reductions on the statements that
meet a condition, where a reduction's output may fail to meet the next condition.
Definitions, statements and proofs. No protocol, no code occurs here.
A reduction K (`Reduction`, Iop/Compose.lean): rounds, then a verifier that rejects or outputs a
statement. `K.Know on RA RB ext ε` (Ior/Know.lean) is round-by-round knowledge soundness in its
working form: on every statement with `on` the prover has lost, at the start (`Doomed`,
Iop/Rbr.lean), towards: every witness in RB of an output extracts, by ext, to a witness in RA of
the input.

Why: beyond unique decoding a word has a list of codewords near it. Uniqueness is restored by a
sample: the verifier draws a seed, the prover answers, and but for a collision (two members of the
list with different messages and the same answers) at most one member agrees with the answer. A
collision is an event of the round of the seed. After that round, statements carry the sample, and
all later rounds are argued "on collision-free statements". In the form of the notion with a
knowledge state function ("the field's form"; Ior/Know.lean: `IsKState`, `HasRbrKnowledge`) the
state after the seed is "the state before, or a collision": once a collision has happened the state
is 1 for every witness and no extraction can fail.
`Know.of_badFam` proves `Know` from sets of bad verifier messages, each charged to its own round,
and a backward step on witnesses that is asked on clean transcripts only: so a collision inside one
reduction needs nothing new. What did not fit: `Know.seq` asks that every output of the first
reduction on a statement with its own condition meets the condition of the second. "Collision-free"
is not so: it fails with the chance of the bad event. `KnowInto` is the form that composes.

Main names:
  `orOff on R`, `K.KnowInto on on' RA RB ext ε`: the two definitions; see their docstrings.
  `Spec.knowInto_of_carry`: a reduction that carries the condition.
  `Spec.knowInto_seq`, `Spec.knowInto_seq_ext`: composition: `on₁` into `on₂`, then `on₂` into
    `on₃`, is `on₁` into `on₃`: errors in a row, extractors composed.
  `Spec.knowInto_of_badFam`: how "into" is proved.
  `Spec.know_of_det`: where the relation determines its witness, any extractor may be replaced by
    the decoder of the statement. (A relaxation by decoding with a sample, on collision-free
    statements.)

Limits: this file says nothing on lists, samples or collisions themselves: `on`, `on'` are any
conditions. It says nothing on running times. The field's form of these rules (the state function
"state, or outside the condition") is not written out here (for a reduction that carries the
condition: Ior/KnowCollLit.lean, `stCf`, `Spec.with_cf`: by reading). By Ior/KnowLit.lean
(`know_iff_literal`), for a reduction with at least one round and one extractor on full
transcripts, the two forms are the same, with the same errors.
The convention and the rule for carried conditions follow this protocol's technical report, which
follows the paper that this protocol builds on and, for the convention, the worked example named in
lean/CREDITS.md; the clause "the state before, or a collision" follows that paper.
Terms: lean/GLOSSARY.md.
-/
import Ior.Know
import Ior.ChainProofs

set_option autoImplicit false

namespace Iop
open Prob

namespace Reduction
variable {A B : Type}

/-- The relation R enlarged by all (a, w) whose statement a is outside `on`. -/
def orOff {W : Type} (on : A → Prop) (R : A → W → Prop) : A → W → Prop := fun a w => R a w ∨ ¬ on a

/-- Round-by-round knowledge soundness on the statements with `on`, into the statements with `on'`.
In words: on the statements with `on` the prover has lost, at the start (`Doomed`, Iop/Rbr.lean),
towards: "whenever the verifier outputs b, and b is outside `on'` or w is a witness of b,
`ext a τ w` is a witness of a". So reaching an output outside `on'` counts as a win of the prover
(unless `ext a τ w` is a witness of a for every w), and is paid in ε. -/
def KnowInto {WA WB : Type} (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape) :
    Prop :=
  K.Know on RA (orOff on' RB) ext ε

end Reduction

namespace Spec
open Reduction

/-- States: a condition on the input statements is an enlargement of the input relation. -/
def know_iff_orOff : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    K.Know on RA RB ext ε ↔ K.Know (fun _ => True) (orOff on RA) RB ext ε

/-- States: `KnowInto` is equivalent to `Know`, on all statements, for the two enlarged
relations. -/
def knowInto_iff : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop) (RA : A → WA → Prop)
      (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    K.KnowInto on on' RA RB ext ε ↔ K.Know (fun _ => True) (orOff on RA) (orOff on' RB) ext ε

/-- States: at `on'` = all statements, `KnowInto` is equivalent to `Know`. -/
def know_of_knowInto : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    K.KnowInto on (fun _ => True) RA RB ext ε ↔ K.Know on RA RB ext ε

/-- States: if the reduction carries the condition (its output is outside `on'` only if its input is
outside `on`), `Know` on `on` gives `KnowInto on on'`, same errors, same extractor. -/
def knowInto_of_carry : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop) (RA : A → WA → Prop)
      (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    (∀ a τ b, K.out a τ = some b → on a → on' b) →
    K.Know on RA RB ext ε → K.KnowInto on on' RA RB ext ε

/-- Composition, with any extractor that agrees with "the second's, then the first's" wherever the
first verifier outputs a statement. (not all hypotheses are named here: see the statement below) -/
def knowInto_seq_ext : Prop :=
  ∀ (A B C WA WB WC : Type) (K₁ : Reduction A B) (K₂ : Reduction B C) (on₁ : A → Prop)
      (on₂ : B → Prop) (on₃ : C → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (RC : C → WC → Prop) (e₁ : A → Tr K₁.shape → WB → WA) (e₂ : B → Tr K₂.shape → WC → WB)
      (ε₁ : Err K₁.shape) (ε₂ : Err K₂.shape) (ext : A → Tr (K₁.seq K₂).shape → WC → WA),
    K₁.KnowInto on₁ on₂ RA RB e₁ ε₁ → K₂.KnowInto on₂ on₃ RB RC e₂ ε₂ →
    (∀ a τ₁ τ₂ b w, K₁.out a τ₁ = some b → ext a (Tr.app τ₁ τ₂) w = e₁ a τ₁ (e₂ b τ₂ w)) →
    (K₁.seq K₂).KnowInto on₁ on₃ RA RC ext (Err.app ε₁ ε₂)

/-- Composition, with the composed extractor `extSeq` of Ior/Know.lean (d: its value where the
first verifier rejects). (not all hypotheses are named here: see the statement below) -/
def knowInto_seq : Prop :=
  ∀ (A B C WA WB WC : Type) (K₁ : Reduction A B) (K₂ : Reduction B C) (on₁ : A → Prop)
      (on₂ : B → Prop) (on₃ : C → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (RC : C → WC → Prop) (e₁ : A → Tr K₁.shape → WB → WA) (e₂ : B → Tr K₂.shape → WC → WB)
      (ε₁ : Err K₁.shape) (ε₂ : Err K₂.shape) (d : WA),
    K₁.KnowInto on₁ on₂ RA RB e₁ ε₁ → K₂.KnowInto on₂ on₃ RB RC e₂ ε₂ →
    (K₁.seq K₂).KnowInto on₁ on₃ RA RC (extSeq K₁ K₂ e₁ e₂ d) (Err.app ε₁ ε₂)

/-- How "into" is proved: on the statements with `on`, bad sets within the errors; on clean
transcripts the output meets the condition `on'` and the backward step holds. -/
def knowInto_of_badFam : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
      (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA)
      (ε : Err K.shape) (bad : A → BadFam K.shape),
    (∀ a, on a → (bad a).Within ε) →
    (∀ a τ b, on a → (bad a).Clean τ → K.out a τ = some b → on' b) →
    (∀ a τ b w, on a → (bad a).Clean τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) →
    K.KnowInto on on' RA RB ext ε

/-- States: if on the statements with `on` RA a w implies w = d a, then `Know` with any extractor
gives `Know`, same relations and errors, with the extractor that returns d a. The new extractor
reads the input statement alone: no transcript, no later witness. -/
def know_of_det : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape) (d : A → WA),
    (∀ a w, on a → RA a w → w = d a) → K.Know on RA RB ext ε → K.Know on RA RB (fun a _ _ => d a) ε

/-- States: an extractor is read only on the statements with `on`, where the verifier outputs a
statement, at witnesses of that statement: one that agrees with `ext` there may replace it in
`Know`. -/
def know_ext_congr : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext ext' : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    (∀ a τ b w, on a → K.out a τ = some b → RB b w → ext' a τ w = ext a τ w) →
    K.Know on RA RB ext ε → K.Know on RA RB ext' ε

end Spec

open Reduction

theorem know_iff_orOff : Spec.know_iff_orOff := by
  intro A B WA WB K on RA RB ext ε
  constructor
  · intro h a _
    by_cases ha : on a
    · exact Doomed.mono _ _ (fun _ hτ b w hb hw => Or.inl (hτ b w hb hw)) (h a ha)
    · exact Doomed.of_forall _ _ fun _ _ _ _ _ => Or.inr ha
  · intro h a ha
    exact Doomed.mono _ _
      (fun _ hτ b w hb hw => (hτ b w hb hw).elim id fun hn => absurd ha hn) (h a trivial)

theorem knowInto_iff : Spec.knowInto_iff := fun A B WA WB K on on' RA RB ext ε =>
  know_iff_orOff A B WA WB K on RA (orOff on' RB) ext ε

theorem know_of_knowInto : Spec.know_of_knowInto := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => h.conseq (fun _ ha => ha) (fun _ _ _ hw => hw) (fun _ _ hw => Or.inl hw),
    fun h =>
      h.conseq (fun _ ha => ha) (fun _ _ _ hw => hw)
        (fun _ _ hw => hw.elim id fun hn => absurd trivial hn)⟩

theorem knowInto_of_carry : Spec.knowInto_of_carry := by
  intro A B WA WB K on on' RA RB ext ε hc h a ha
  exact Doomed.mono _ _
    (fun τ hτ b w hb hw => hw.elim (hτ b w hb) fun hn => absurd (hc a τ b hb ha) hn) (h a ha)

theorem knowInto_seq_ext : Spec.knowInto_seq_ext := by
  intro A B C WA WB WC K₁ K₂ on₁ on₂ on₃ RA RB RC e₁ e₂ ε₁ ε₂ ext h₁ h₂ he
  exact Know.seq_ext h₁ ((know_iff_orOff B C WB WC K₂ on₂ RB (orOff on₃ RC) e₂ ε₂).1 h₂)
    (fun _ _ _ _ _ => trivial) ext he

theorem knowInto_seq : Spec.knowInto_seq := by
  intro A B C WA WB WC K₁ K₂ on₁ on₂ on₃ RA RB RC e₁ e₂ ε₁ ε₂ d h₁ h₂
  exact Know.seq h₁ ((know_iff_orOff B C WB WC K₂ on₂ RB (orOff on₃ RC) e₂ ε₂).1 h₂)
    (fun _ _ _ _ _ => trivial) d

theorem knowInto_of_badFam : Spec.knowInto_of_badFam := by
  intro A B WA WB K on on' RA RB ext ε bad hW hin hback
  exact Know.of_badFam bad hW fun a τ b w ha hτ hb hw =>
    hw.elim (hback a τ b w ha hτ hb) fun hn => absurd (hin a τ b ha hτ hb) hn

theorem know_of_det : Spec.know_of_det := by
  intro A B WA WB K on RA RB ext ε d hd h a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b w hb hw
  have h1 := hτ b w hb hw
  show RA a (d a)
  rw [← hd a _ ha h1]
  exact h1

theorem know_ext_congr : Spec.know_ext_congr := by
  intro A B WA WB K on RA RB ext ext' ε he h a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b w hb hw
  rw [he a τ b w ha hb hw]
  exact hτ b w hb hw

end Iop
