-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Carry.lean: maps of messages, round by round, from one shape to another, along which "the prover
has lost" (`Doomed`, Iop/Rbr.lean) is carried back.

Definitions and statements; the proofs are in Iop/CarryProofs.lean.
Two shapes s (what is sent) and s' (the shape with a theorem) have the same number of rounds. For
each round there are a map of prover messages from s to s' and a map of verifier messages from s to
s' that may be undefined at some values. Both may depend on all that was sent before. No map needs
to be injective or onto. If in each round at most w verifier messages of s go to one verifier
message of s', each error count of s' times w is an error count for s. The rule is of the family of
`Doomed.pull` (Iop/PullProofs.lean), `Doomed.grind`, `Doomed.recutS` and `Doomed.splitS`.

What the freedom is for. A map of prover messages that depends on the past can fill in what is not
sent because the verifier can compute it (a coefficient of a round polynomial that follows from the
running claim), and can put into its round what was sent in an earlier round (a mask that rides in
an earlier oracle). A verifier message without an image stands for a test on the verifier message
that fails.

Main names:
  `Carry s s'`: the maps. `F.tr`: the image of a full transcript, `none` if a verifier message has
    no image. `F.Fib ws`: in each round at most w verifier messages go to one.
  `mulErr s s' ws ε`: each count of ε times the w of its round. `Err.ones s`: all w = 1.
  `Rate s s' ws k`: in each round w |Chal'| ≤ k |Chal|.
  `Carry.id s`; `F.app G`: the maps of two shapes in a row; those of the second part may read the
    whole transcript of the first.
  `Spec.carry_doomed`: the rule. `Spec.carry_sound`: the same for round-by-round soundness of two
    protocols. `Spec.carry_below`: the errors as probabilities.
  `Spec.carry_id`, `Spec.carry_app`: image, fibres and errors of `Carry.id` and `F.app G`.

Limits: nothing on completeness or zero knowledge: they speak of an honest prover. Nothing on
what a verifier reads: a `Carry` has no map of positions, and no map from the verifier randomness of
s to that of s' (its map of verifier messages may read prover messages). The error counts are the
same only where all w are 1. As probabilities they are then the same only if the two rounds have
equally many verifier messages (`Rate`, `Spec.carry_below`).

Terms: lean/GLOSSARY.md.

-/
import Iop.InteractiveOracleProof

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- Maps from a shape s to a shape s', round by round: the map of prover messages; the map of
verifier messages, which may look at the round's prover message and is `none` where it is
undefined; and the maps of the later rounds, which may depend on this round's two messages.
There is no such thing between shapes of different lengths. -/
def Carry : Shape → Shape → Type
  | [], [] => Unit
  | r :: s, r' :: s' =>
      (r.Msg → r'.Msg) × (r.Msg → r.Chal → Option r'.Chal) × (r.Msg → r.Chal → Carry s s')
  | [], _ :: _ => Empty
  | _ :: _, [] => Empty

namespace Carry

/-- The image of a full transcript. It is `none` if a verifier message has no image. -/
def tr : {s s' : Shape} → Carry s s' → Tr s → Option (Tr s')
  | [], [], _, _ => some ()
  | _ :: _, _ :: _, (fm, fc, k), (m, c, τ) =>
      (fc m c).bind fun c' => (tr (k m c) τ).map fun τ' => (fm m, c', τ')
  | [], _ :: _, F, _ => nomatch F
  | _ :: _, [], F, _ => nomatch F

/-- In each round at most w verifier messages go to one verifier message, whatever was sent
before. The list ws holds the numbers w. -/
def Fib : {s s' : Shape} → Carry s s' → Err s → Prop
  | [], [], _, _ => True
  | r :: _, r' :: _, (_, fc, k), (w, ws) =>
      (∀ (m : r.Msg) (c' : r'.Chal), cnt (fun c => fc m c = some c') ≤ w) ∧ ∀ m c, Fib (k m c) ws
  | [], _ :: _, _, _ => True
  | _ :: _, [], _, _ => True

/-- Nothing is changed. -/
protected def id : (s : Shape) → Carry s s
  | [] => ()
  | _ :: s => (fun m => m, fun _ c => some c, fun _ _ => Carry.id s)

/-- Two shapes in a row: the maps of the first part, then those of the second, which may read the
whole transcript of the first. -/
def app : {s₁ s₁' s₂ s₂' : Shape} → Carry s₁ s₁' → (Tr s₁ → Carry s₂ s₂') →
    Carry (s₁ ++ s₂) (s₁' ++ s₂')
  | [], [], _, _, _, G => G ()
  | _ :: _, _ :: _, _, _, (fm, fc, k), G =>
      (fm, fc, fun m c => app (k m c) fun τ => G (m, c, τ))
  | [], _ :: _, _, _, F, _ => nomatch F
  | _ :: _, [], _, _, F, _ => nomatch F

end Carry

/-- The error counts for s that follow from error counts for s': each is multiplied by the
number w of its round. (Where s is longer than s' the count is 0; no `Carry` exists there.) -/
def mulErr : (s s' : Shape) → Err s → Err s' → Err s
  | [], _, _, _ => ()
  | _ :: s, [], (_, ws), _ => (0, mulErr s [] ws ())
  | _ :: s, _ :: s', (w, ws), (e, ε) => (e * w, mulErr s s' ws ε)

/-- the number 1 in each round -/
def Err.ones : (s : Shape) → Err s
  | [] => ()
  | _ :: s => (1, Err.ones s)

/-- In each round w * |Chal'| ≤ k * |Chal|: a value of the image is at most k times as likely as
under the uniform law. -/
def Rate : (s s' : Shape) → Err s → ℝ≥0∞ → Prop
  | [], _, _, _ => True
  | _ :: _, [], _, _ => True
  | r :: s, r' :: s', (w, ws), k =>
      (w : ℝ≥0∞) * (Fintype.card r'.Chal : ℝ≥0∞) ≤ k * (Fintype.card r.Chal : ℝ≥0∞) ∧
        Rate s s' ws k

namespace Spec

/-- The prover's loss is carried back. Let the prover have lost in s' towards the goal bad'. Let the
goal bad hold of every transcript of s without an image, and of every transcript whose image is in
bad'. Then the prover has lost in s towards bad, with each error count times w. -/
def carry_doomed : Prop :=
  ∀ (s s' : Shape) (F : Carry s s') (ws : Err s), F.Fib ws → ∀ (ε : Err s')
      (bad : Tr s → Prop) (bad' : Tr s' → Prop), (∀ τ, F.tr τ = none → bad τ) →
    (∀ τ τ', F.tr τ = some τ' → bad' τ' → bad τ) → Doomed s' ε bad' →
    Doomed s (mulErr s s' ws ε) bad

/-- Round-by-round soundness is carried along a change of types. fx and fy translate statements and
external oracles; the maps F may depend on both. A statement whose translation is in the language L'
is in the language L; what Q accepts has an image that Q' accepts. -/
def carry_sound : Prop :=
  ∀ (X X' : Type) (E E' : ExtSpec) (Q : InteractiveOracleProof X E) (Q' : InteractiveOracleProof X' E')
      (F : X → E.Str → Carry Q.shape Q'.shape) (ws : Err Q.shape), (∀ x y, (F x y).Fib ws) →
    ∀ (fx : X → X') (fy : E.Str → E'.Str) (L : X → E.Str → Prop) (L' : X' → E'.Str → Prop)
      (ε : Err Q'.shape),
    (∀ x y, L' (fx x) (fy y) → L x y) →
    (∀ x y τ, Q.accept x y τ = true →
      ∃ τ', (F x y).tr τ = some τ' ∧ Q'.accept (fx x) (fy y) τ' = true) →
    Q'.Sound L' ε → Q.Sound L (mulErr Q.shape Q'.shape ws ε)

/-- The errors as probabilities: if all error counts of s' are at most the probability c, those that
follow for s are at most k * c. -/
def carry_below : Prop :=
  ∀ (s s' : Shape) (ws : Err s) (k c : ℝ≥0∞) (ε : Err s'), Rate s s' ws k →
    Err.Below ε c → Err.Below (mulErr s s' ws ε) (k * c)

/-- `Carry.id`: every transcript is its own image; one verifier message goes to one; the errors are
unchanged. -/
def carry_id : Prop :=
  ∀ s : Shape, (∀ τ : Tr s, (Carry.id s).tr τ = some τ) ∧ (Carry.id s).Fib (Err.ones s) ∧
    ∀ ε : Err s, mulErr s s (Err.ones s) ε = ε

/-- `F.app G`: the image of a transcript is the two images in a row; fibres and errors in a row. -/
def carry_app : Prop :=
  ∀ (s₁ s₁' s₂ s₂' : Shape) (F : Carry s₁ s₁') (G : Tr s₁ → Carry s₂ s₂'),
    (∀ (τ₁ : Tr s₁) (τ₂ : Tr s₂), (F.app G).tr (Tr.app τ₁ τ₂) =
      (F.tr τ₁).bind fun τ₁' => ((G τ₁).tr τ₂).map fun τ₂' => Tr.app τ₁' τ₂') ∧
    (∀ (ws₁ : Err s₁) (ws₂ : Err s₂), F.Fib ws₁ → (∀ τ, (G τ).Fib ws₂) →
      (F.app G).Fib (Err.app ws₁ ws₂)) ∧
    ∀ (ws₁ : Err s₁) (ws₂ : Err s₂) (ε₁ : Err s₁') (ε₂ : Err s₂'),
      mulErr (s₁ ++ s₂) (s₁' ++ s₂') (Err.app ws₁ ws₂) (Err.app ε₁ ε₂) =
        Err.app (mulErr s₁ s₁' ws₁ ε₁) (mulErr s₂ s₂' ws₂ ε₂)

end Spec
end Iop
