-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Know.lean: round-by-round knowledge soundness for the reductions of Iop/Compose.lean, with a
relaxation pair and a named extractor.

Definitions, rules with their proofs, and two statements (`Iop.Spec`), which Ior/KnowLit.lean
proves.
A reduction (`Reduction`, Iop/Compose.lean) is a protocol after whose rounds the verifier rejects or
outputs a new statement. "The prover has lost" towards a goal (`Doomed`, Iop/Rbr.lean) means:
whatever it sends, in each round at most the error's number of verifier messages lead to a position
in which it has not lost, and at the end the goal holds.

The working form (`Know`). A reduction K from statements A to statements B, relations RA on (a, w),
RB on (b, w') (the relaxation pair), and a function ext that turns a witness of the output statement
into a witness of the input statement (it may read the input statement and the whole transcript).
`K.Know on RA RB ext ε` says: on every statement a with "on a", the prover has lost at the start
(`Iop.Doomed`, with the error list ε) towards
      "whenever the verifier outputs b and w' is a witness of b in RB, ext a τ w' is a witness of a
      in RA".
There is no premise "a is outside the language": the game "reach an output statement with a valid
witness whose extraction is invalid" is lost from the start, for true and for false statements.
"on" is a condition on the input statements: the statements of which soundness speaks.


The form with a knowledge state function (`HasRbrKnowledge`): a knowledge state function on (partial
transcript, knowledge state witness) with the laws for the empty transcript, for prover moves and
for full transcripts, an extractor for each round, and for each round a bound on the verifier
messages after which some witness is in state 1 while its extraction was in state 0.
`Spec.know_of_literal` and `Spec.literal_of_know` say that each form gives the other (the second:
for at least one round), with the same errors; see their docstrings.

Why the extractor is an argument and not under an existential: Lean models no running time. With
"there is an extractor" the notion would follow from soundness for every relation (pick a witness by
choice: `know_by_choice`, Ior/KnowBlind.lean, for a non-empty type of input witnesses). So every
theorem of this file names its extractor. For the relaxations by decoding it is: decode the oracles
of the statement, then forget what the input relation does not name.


Limits: this file says nothing on running times, and nothing on queries (Ior/Ior.lean).
The notions restate, in our own words and in this library's recursion on shapes, definitions of the
paper that this protocol builds on (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Iop.Compose

set_option autoImplicit false

namespace Iop
open Prob

namespace Reduction
variable {A B C WA WB WC : Type}

/-- Round-by-round knowledge soundness, working form, on the statements with "on". -/
def Know (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape) : Prop :=
  ∀ a, on a → Doomed K.shape ε (fun τ => ∀ b w, K.out a τ = some b → RB b w → RA a (ext a τ w))

section Rules
variable {K : Reduction A B} {on on' : A → Prop} {RA RA' : A → WA → Prop} {RB RB' : B → WB → Prop}
  {ext : A → Tr K.shape → WB → WA} {ε ε' : Err K.shape}

/-- Fewer statements, a larger input relation, a smaller output relation. -/
theorem Know.conseq (h : K.Know on RA RB ext ε) (ho : ∀ a, on' a → on a)
    (hA : ∀ a w, on' a → RA a w → RA' a w) (hB : ∀ b w, RB' b w → RB b w) :
    K.Know on' RA' RB' ext ε := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b w hb hw => hA a _ ha (hτ b w hb (hB b w hw))) (h a (ho a ha))

theorem Know.mono_err (h : K.Know on RA RB ext ε) (hε : Err.le ε ε') : K.Know on RA RB ext ε' :=
  fun a ha => Doomed.mono_err _ hε (h a ha)

/-- Two sets of statements, each with its own errors: the larger error in each round. -/
theorem Know.union (h : K.Know on RA RB ext ε) (h' : K.Know on' RA RB ext ε') :
    K.Know (fun a => on a ∨ on' a) RA RB ext (Err.max ε ε') :=
  fun a ha =>
    ha.elim (fun x => Doomed.mono_err _ (Err.le_max_left ε ε') (h a x))
      (fun x => Doomed.mono_err _ (Err.le_max_right ε ε') (h' a x))

/-- Knowledge soundness gives soundness for the languages of the two relations, the first enlarged
by the statements outside "on". -/
theorem Know.toSound (h : K.Know on RA RB ext ε) :
    K.Sound (fun a => ¬ on a ∨ ∃ w, RA a w) (fun b => ∃ w, RB b w) ε := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb hw => hw.elim fun w hw => ha (Or.inr ⟨_, hτ b w hb hw⟩))
    (h a (by_contra fun hn => ha (Or.inl hn)))

/-- From soundness to knowledge soundness when the statement determines its witness (relaxations by
decoding) and every output statement with a witness is in the output language (`hB`): the extractor
is d, a function of the input statement alone. -/
theorem Know.of_sound {LA : A → Prop} {LB : B → Prop} (h : K.Sound LA LB ε) (d : A → WA)
    (hA : ∀ a, on a → LA a → RA a (d a)) (hB : ∀ b w, RB b w → LB b) :
    K.Know on RA RB (fun a _ _ => d a) ε := fun a ha => by
  by_cases hL : LA a
  · exact Doomed.of_forall _ _ fun _ _ _ _ _ => hA a ha hL
  · exact Doomed.mono _ _ (fun _ hτ b w hb hw => absurd (hB b w hw) (hτ b hb)) (h a hL)

/-- How knowledge soundness is proved: sets of bad values and a backward step on witnesses. -/
theorem Know.of_badFam (bad : A → BadFam K.shape) (hW : ∀ a, on a → (bad a).Within ε)
    (hback : ∀ a τ b w, on a → (bad a).Clean τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) :
    K.Know on RA RB ext ε :=
  fun a ha =>
    doomed_of_clean _ _ (bad a) _ (hW a ha) fun τ hτ b w hb hw => hback a τ b w ha hτ hb hw

end Rules

/-- The extractor of a composition: that of the second reduction, then that of the first. Where the
first verifier rejects there is nothing to extract from: the value is d. -/
def extSeq (K₁ : Reduction A B) (K₂ : Reduction B C) (e₁ : A → Tr K₁.shape → WB → WA)
    (e₂ : B → Tr K₂.shape → WC → WB) (d : WA) :
    A → Tr (K₁.seq K₂).shape → WC → WA := fun a τ w =>
  match K₁.out a (Tr.fst τ) with
  | some b => e₁ a (Tr.fst τ) (e₂ b (Tr.snd (s := K₁.shape) τ) w)
  | none => d

/-- Sequential composition: the middle relations agree, the condition of the second holds of every
output of the first on a statement with on₁; errors are concatenated, extractors composed. -/
theorem Know.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {on₁ : A → Prop} {on₂ : B → Prop}
    {RA : A → WA → Prop} {RB : B → WB → Prop} {RC : C → WC → Prop} {e₁ : A → Tr K₁.shape → WB → WA}
    {e₂ : B → Tr K₂.shape → WC → WB} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    (h₁ : K₁.Know on₁ RA RB e₁ ε₁) (h₂ : K₂.Know on₂ RB RC e₂ ε₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b) (d : WA) :
    (K₁.seq K₂).Know on₁ RA RC (extSeq K₁ K₂ e₁ e₂ d) (Err.app ε₁ ε₂) := by
  intro a ha
  refine Doomed.append K₁.shape K₂.shape ε₁ ε₂ _ (Doomed.mono _ _ ?_ (h₁ a ha))
  intro τ₁ hτ₁
  cases hout : K₁.out a τ₁ with
  | none =>
      refine Doomed.of_forall _ _ fun τ₂ c w hc _ => ?_
      rw [seq_out_app, hout] at hc
      exact absurd hc (by simp)
  | some b =>
      refine Doomed.mono _ _ ?_ (h₂ b (hon a τ₁ b ha hout))
      intro τ₂ h c w hc hw
      rw [seq_out_app, hout] at hc
      have := hτ₁ b _ hout (h c w hc hw)
      simpa [extSeq, Tr.fst_app, Tr.snd_app, hout] using this

end Reduction

/-! ## The form with a knowledge state function -/

/-- One extractor for each round: it is given all earlier messages, the prover message and the
verifier message of its round. -/
def RExt (S : Type) : Shape → Type
  | [] => Unit
  | r :: s => (r.Msg → r.Chal → S → S) × (r.Msg → r.Chal → RExt S s)

/-- The extractor of the current round at a transcript at the verifier. -/
def RExt.at {S : Type} : {s : Shape} → RExt S s → (τ : AtV s) → τ.round.Chal → S → S
  | _ :: _, (e, _), .inl m => e m
  | _ :: _, (_, k), .inr (m, c, τ) => RExt.at (k m c) τ

/-- All rounds' extractors, composed backwards: the last round's first. -/
def RExt.back {S : Type} : {s : Shape} → RExt S s → Tr s → S → S
  | [], _, _, w => w
  | _ :: _, (e, k), (m, c, τ), w => e m c (RExt.back (k m c) τ w)

namespace Reduction
variable {A B : Type}

/-- A knowledge state function for the statement a, with relaxation (RA, RB); S is the set of
knowledge state witnesses. -/
structure IsKState (K : Reduction A B) {S : Type} (RA : A → S → Prop) (RB : B → S → Prop)
    (a : A) (St : PTr K.shape → S → Bool) : Prop where
  empty  : ∀ s, St (PTr.empty K.shape) s = true ↔ RA a s
  prover : ∀ (τ : AtP K.shape) (m : τ.round.Msg) s, St (.atP τ) s = false → St (.atV (τ.snoc m)) s = false
  full   : ∀ (τ : Tr K.shape) s, St (.full τ) s = true ↔ ∃ b, K.out a τ = some b ∧ RB b s

/-- Round-by-round knowledge soundness, the form with a knowledge state function, with the round
extractors named. Errors are counts of values of one verifier message. -/
def HasRbrKnowledge (K : Reduction A B) {S : Type} (on : A → Prop) (RA : A → S → Prop)
    (RB : B → S → Prop) (Ex : A → RExt S K.shape) (ε : Err K.shape) : Prop :=
  ∃ St : A → PTr K.shape → S → Bool, ∀ a, on a →
    K.IsKState RA RB a (St a) ∧
    ∀ τ : AtV K.shape,
      cnt (fun c : τ.round.Chal =>
          ∃ s, St a (.atV τ) ((Ex a).at τ c s) = false ∧ St a (τ.snoc c) s = true) ≤ τ.err ε

end Reduction

/-- A relation on WA, read on the sum: no witness of the other kind is in it. -/
def onLeft {A WA WB : Type} (R : A → WA → Prop) : A → WA ⊕ WB → Prop := fun a s => match s with
  | .inl w => R a w
  | .inr _ => False
def onRight {B WA WB : Type} (R : B → WB → Prop) : B → WA ⊕ WB → Prop := fun b s => match s with
  | .inl _ => False
  | .inr w => R b w

/-- Round extractors from one extractor on full transcripts: the last round applies it, the earlier
rounds change nothing. -/
def RExt.ofFull {WA WB : Type} : (s : Shape) → (Tr s → WB → WA) → RExt (WA ⊕ WB) s
  | [], _ => ()
  | [_], e => (fun m c w => match w with
      | .inl w => .inl w
      | .inr w => .inl (e (m, c, ()) w), fun _ _ => ())
  | _ :: r' :: s, e => (fun _ _ w => w, fun m c => RExt.ofFull (r' :: s) fun τ => e (m, c, τ))

namespace Spec
open Reduction

/-- States: `HasRbrKnowledge` gives the working form: same errors; the extractor is the composition
of the round extractors. -/
def know_of_literal : Prop :=
  ∀ (A B S : Type) (K : Reduction A B) (on : A → Prop) (RA : A → S → Prop) (RB : B → S → Prop)
      (Ex : A → RExt S K.shape) (ε : Err K.shape),
    K.HasRbrKnowledge on RA RB Ex ε → K.Know on RA RB (fun a τ s => (Ex a).back τ s) ε

/-- States: the working form gives `HasRbrKnowledge`, for a protocol with at least one round: same
errors; the knowledge state witnesses are the sum WA ⊕ WB, with RA read on the left (`onLeft`) and
RB on the right (`onRight`); the round extractors are `RExt.ofFull`. -/
def literal_of_know : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    K.shape ≠ [] → K.Know on RA RB ext ε →
    K.HasRbrKnowledge on (onLeft (WB := WB) RA) (onRight (WA := WA) RB)
      (fun a => RExt.ofFull K.shape (ext a)) ε

end Spec
end Iop
