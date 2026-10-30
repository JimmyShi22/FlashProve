-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/State.lean: partial transcripts, and the predicate `Lost` ("the prover has lost") on them.

In this library round-by-round soundness is a recursion from the end of the protocol to its start
(`Doomed`, Iop/Rbr.lean). The literature says instead: there is a state function on partial
transcripts with four laws.
This file defines partial transcripts of a list of rounds (`AtP`, `AtV`, `PTr`) and the predicate
`Lost` on them: `Doomed` for the remaining rounds. `Lost` is `Doomed` at the empty transcript
(`lost_empty`) and `bad` at a full one (`lost_full`); a prover message preserves it (`Lost.prover`);
at most as many values of a verifier message as the round's error lead out of it (`Lost.verifier`).
Not in this library: a definition of state functions (the textbook's Definition 31.1.1), and a
proof that the two notions are the same. (the two directions stand apart: `Lost`, Iop/State.lean;
`doomed_of_jointLaw`, Ior/BatchKProofs.lean, with `jointLaw_one`, Iop/BatchOne.lean; this file
joins them in no statement) Not in this file: the textbook's Claim 31.1.3 (the soundness error is
at most the sum of the round-by-round errors).

"The textbook" in the comments below: A. Chiesa, E. Yogev, "Building Cryptographic Proofs from Hash
Functions" (edition of March 25, 2026).

On a word. Our Doomed means: the prover has lost; this is State = 0, as in Canetti, Chen, Holmgren,
Lombardi, Rothblum, Rothblum (ePrint 2018/1004). As we read it, the informal prose of the textbook's
Section 31.1 uses the word "doomed" in more than one sense.
We go by its formal definitions, in which State = 0 at the start for a false statement and State = 0
at the end forces rejection.

Errors are counts of values of one verifier message; `AtV.errPr` turns them into probabilities.
Section 4 only turns the error law at one transcript from a count into a probability
(`cnt_le_err_iff_pr_le`): the law for a randomised malicious prover, which that section's opening
comment tells, is not stated in this file.

Related published work, which has not been compared with this file: Justin Holmgren,
"On Round-By-Round Soundness and State Restoration
Attacks", ePrint 2019/1261, Definition 2.5, restates the definition of round-by-round soundness of
ePrint 2018/1004 with a "doomed set" of partial transcripts; Alexander R. Block, Albert Garreta,
Jonathan Katz, Justin Thaler, Pratyush Ranjan Tiwari and Michał Zając, "Fiat-Shamir Security of FRI
and Related SNARKs", ePrint 2023/1071, Definition 3.12 (doomed sets); Alexander R. Block, Albert
Garreta, Pratyush Ranjan Tiwari and Michał Zając, "On Soundness Notions for Interactive Oracle
Proofs", ePrint 2023/1256, Definition 3.11 and Theorem 1.4 (a bound by the sum of the errors).
On where the idea of `Doomed` comes from: lean/CREDITS.md, section 9.

Round-by-round soundness is the notion of R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G.
Rothblum, R. Rothblum, ePrint 2018/1004, Definition 5.3.

Notation: `Tr s : Type` (Iop/Shape.lean): full transcripts; `Rho s : Type` (there): the verifier's
randomness of a whole execution; `Err s : Type` (Iop/Rbr.lean): one number for each round; in
`Doomed s ε bad` (there), how many values of the challenge may lead from a doomed transcript to one
that is not doomed; `Err.Below ε c : Prop` (Iop/InteractiveOracleProof.lean): every error of the list, as a
probability, is at most c, for a round r with the error e:
`(e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞)`; `cnt P : ℕ` (Prob/Cnt.lean): the number of
elements of a finite type with the property P.
-/
import Prob.Count
import Iop.InteractiveOracleProof
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

universe u

/-! ## 0. The order on error lists

Err.le, Err.max and Doomed.mono_err are in Iop/Rbr.lean; here are the remaining laws of the order.
They are used where a proof splits into cases on the statement and each case has its own errors,
while the definition of soundness asks for one list of errors for all statements. -/

theorem Err.le_refl : ∀ {s : Shape} (a : Err s), Err.le a a
  | [], _ => trivial
  | _ :: _, (_, a) => ⟨Nat.le_refl _, Err.le_refl a⟩

theorem Err.le_trans : ∀ {s : Shape} {a b c : Err s}, Err.le a b → Err.le b c → Err.le a c
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _), h, h' => ⟨Nat.le_trans h.1 h'.1, Err.le_trans h.2 h'.2⟩

theorem Err.max_le : ∀ {s : Shape} {a b c : Err s}, Err.le a c → Err.le b c → Err.le (Err.max a b) c
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _), h, h' => ⟨Nat.max_le.2 ⟨h.1, h'.1⟩, Err.max_le h.2 h'.2⟩

/-- If the prover has lost with the errors ε, it has lost with `Err.max ε ε'` (`max_right`: the same
from ε'). -/
theorem Doomed.max_left (s : Shape) {ε : Err s} (ε' : Err s)
    {bad : Tr s → Prop} (h : Doomed s ε bad) : Doomed s (Err.max ε ε') bad :=
  Doomed.mono_err s (Err.le_max_left ε ε') h

theorem Doomed.max_right (s : Shape) (ε : Err s) {ε' : Err s}
    {bad : Tr s → Prop} (h : Doomed s ε' bad) : Doomed s (Err.max ε ε') bad :=
  Doomed.mono_err s (Err.le_max_right ε ε') h

/-- A bound on all errors of a list holds for every smaller list. -/
theorem Err.Below.mono :
    ∀ {s : Shape} {a b : Err s} {c : ℝ≥0∞}, Err.le a b → Err.Below b c → Err.Below a c
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), _, h, h' =>
      ⟨_root_.le_trans (Nat.cast_le.2 h.1) h'.1, Err.Below.mono h.2 h'.2⟩

/-- A bound on all errors of two lists holds for their maximum. -/
theorem Err.Below.max : ∀ {s : Shape} {a b : Err s} {c : ℝ≥0∞},
    Err.Below a c → Err.Below b c → Err.Below (Err.max a b) c
  | [], _, _, _, _, _ => trivial
  | r :: _, (e, _), (e', _), c, h, h' => ⟨by
      show ((Max.max e e' : ℕ) : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞)
      rcases Nat.le_total e e' with hh | hh
      · rw [max_eq_right hh]; exact h'.1
      · rw [max_eq_left hh]; exact h.1, Err.Below.max h.2 h'.2⟩

/-! ## 1. Partial transcripts

A transcript (Π₁, ρ₁, Π₂, ...) of a protocol with k rounds is of exactly one of three kinds: at the
prover (empty, or it ends with a verifier message and has fewer than k of them), at the verifier (it
ends with a prover message), or full (k verifier messages).
Each kind is a separate type, defined by recursion on the list of rounds, and a partial transcript
is an element of one of the three. -/

/-- Transcripts at the prover: (Π₁, ρ₁, ..., Πᵢ, ρᵢ) with i < k. Sum.inl () is the empty
transcript. -/
def AtP : Shape → Type
  | [] => Empty
  | r :: s => Unit ⊕ (r.Msg × r.Chal × AtP s)

/-- Transcripts at the verifier: (Π₁, ρ₁, ..., ρᵢ₋₁, Πᵢ) with 1 ≤ i ≤ k. Sum.inl Π is the transcript
(Π). -/
def AtV : Shape → Type
  | [] => Empty
  | r :: s => r.Msg ⊕ (r.Msg × r.Chal × AtV s)

/-- Partial transcripts: at the prover, at the verifier, or full. -/
inductive PTr (s : Shape) : Type
  | atP (τ : AtP s)
  | atV (τ : AtV s)
  | full (τ : Tr s)

/-- The empty transcript. It is at the prover, except in a protocol without rounds, where it is
full. -/
def PTr.empty : (s : Shape) → PTr s
  | [] => .full ()
  | _ :: _ => .atP (Sum.inl ())

/-- Put one round (Π, ρ) before a partial transcript of the remaining rounds. -/
def PTr.cons {r : Round} {s : Shape} (m : r.Msg) (c : r.Chal) : PTr s → PTr (r :: s)
  | .atP τ => .atP (Sum.inr (m, c, τ))
  | .atV τ => .atV (Sum.inr (m, c, τ))
  | .full τ => .full (m, c, τ)

namespace AtP

/-- The number of rounds that are complete. -/
def idx : {s : Shape} → AtP s → ℕ
  | _ :: _, .inl _ => 0
  | _ :: _, .inr (_, _, τ) => idx τ + 1

/-- The round that begins now: it fixes the format of the next prover message. -/
def round : {s : Shape} → AtP s → Round
  | r :: _, .inl _ => r
  | _ :: _, .inr (_, _, τ) => round τ

/-- τ ‖ Π: the prover moves. -/
def snoc : {s : Shape} → (τ : AtP s) → τ.round.Msg → AtV s
  | _ :: _, .inl _, m => Sum.inl m
  | _ :: _, .inr (m', c', τ), m => Sum.inr (m', c', snoc τ m)

/-- The round that begins is the one with this number in the list of rounds (counted from 0). -/
theorem getElem?_idx : ∀ {s : Shape} (τ : AtP s), s[τ.idx]? = some τ.round
  | _ :: _, .inl _ => rfl
  | r :: s, .inr (_, _, τ) => by
      show (r :: s)[τ.idx + 1]? = some τ.round
      rw [List.getElem?_cons_succ]
      exact getElem?_idx τ

end AtP

namespace AtV

/-- The number of rounds that are complete; the current round has this number, counted from 0. -/
def idx : {s : Shape} → AtV s → ℕ
  | _ :: _, .inl _ => 0
  | _ :: _, .inr (_, _, τ) => idx τ + 1

/-- The current round: it fixes the set from which the next verifier message is sampled. -/
def round : {s : Shape} → AtV s → Round
  | r :: _, .inl _ => r
  | _ :: _, .inr (_, _, τ) => round τ

/-- The error of the current round: εᵢ for τ = (Π₁, ρ₁, ..., ρᵢ₋₁, Πᵢ). -/
def err : {s : Shape} → AtV s → Err s → ℕ
  | _ :: _, .inl _, (e, _) => e
  | _ :: _, .inr (_, _, τ), (_, ε) => err τ ε

/-- τ ‖ ρ: the verifier moves. The result is at the prover, or full after the last round. -/
def snoc : {s : Shape} → (τ : AtV s) → τ.round.Chal → PTr s
  | _ :: s, .inl m, c => PTr.cons m c (PTr.empty s)
  | _ :: _, .inr (m', c', τ), c => PTr.cons m' c' (snoc τ c)

theorem getElem?_idx : ∀ {s : Shape} (τ : AtV s), s[τ.idx]? = some τ.round
  | _ :: _, .inl _ => rfl
  | r :: s, .inr (_, _, τ) => by
      show (r :: s)[τ.idx + 1]? = some τ.round
      rw [List.getElem?_cons_succ]
      exact getElem?_idx τ

/-- The error of the current round as a probability: the count divided by the number of values of
the verifier message. -/
def errPr {s : Shape} (τ : AtV s) (ε : Err s) : ℝ≥0∞ :=
  (τ.err ε : ℝ≥0∞) / Fintype.card τ.round.Chal

end AtV


/-- A bound on all errors of the list, as probabilities, bounds the error of the current round. -/
theorem Err.Below.errPr_le :
    ∀ {s : Shape} {ε : Err s} {c : ℝ≥0∞}, Err.Below ε c → ∀ τ : AtV s, τ.errPr ε ≤ c
  | r :: _, (_, _), _, h, .inl _ =>
    (ENNReal.div_le_iff (card_ne_zero' r.Chal) (card_ne_top' r.Chal)).2 h.1
  | _ :: _, (_, _), _, h, .inr (_, _, τ) => Err.Below.errPr_le h.2 τ

/-- A prover message does not complete a round. -/
theorem AtP.idx_snoc : ∀ {s : Shape} (τ : AtP s) (m : τ.round.Msg), (τ.snoc m).idx = τ.idx
  | _ :: _, .inl _, _ => rfl
  | _ :: _, .inr (_, _, τ), m => congrArg (· + 1) (AtP.idx_snoc τ m)

/-- Nothing else is a partial transcript: every partial transcript arises from the empty one by
moves of the prover and of the verifier in turn. (So the lemmas below, which are about the empty
transcript and the two moves, cover all of them.) -/
theorem PTr.snoc_induction : ∀ (s : Shape) (P : PTr s → Prop), P (PTr.empty s) →
    (∀ (τ : AtP s) (m : τ.round.Msg), P (.atP τ) → P (.atV (τ.snoc m))) →
    (∀ (τ : AtV s) (c : τ.round.Chal), P (.atV τ) → P (τ.snoc c)) → ∀ τ, P τ
  | [], _, h0, _, _, .full () => h0
  | [], _, _, _, _, .atP τ => Empty.elim τ
  | [], _, _, _, _, .atV τ => Empty.elim τ
  | r :: s, P, h0, hP, hV, τ => by
      have h1 : ∀ m : r.Msg, P (.atV (Sum.inl m)) := fun m => hP (Sum.inl ()) m h0
      have h2 : ∀ (m : r.Msg) (c : r.Chal) (t : PTr s), P (PTr.cons m c t) := fun m c =>
        PTr.snoc_induction s (fun t => P (PTr.cons m c t)) (hV (Sum.inl m) c (h1 m))
          (fun t m' h => hP (Sum.inr (m, c, t)) m' h) (fun t c' h => hV (Sum.inr (m, c, t)) c' h)
      match τ with
      | .atP (.inl ()) => exact h0
      | .atP (.inr (m, c, t)) => exact h2 m c (.atP t)
      | .atV (.inl m) => exact h1 m
      | .atV (.inr (m, c, t)) => exact h2 m c (.atV t)
      | .full (m, c, t) => exact h2 m c (.full t)

/-! ## 2. The predicate `Lost`, for one false statement

The statement is fixed and does not appear. `bad` is the property of full transcripts that the
prover tries to avoid (for an IOP: the verifier rejects). For a Boolean state function (`St`,
section 4), false is the value 0 of the literature, true the value 1. -/



/-- The prover has lost at a partial transcript: Doomed for the rest of the protocol. At the
verifier: at most e values of the next verifier message lead to a position in which the prover has
not lost. -/
def Lost : (s : Shape) → Err s → (Tr s → Prop) → PTr s → Prop
  | [], _, bad, _ => bad ()
  | r :: s, (e, ε), bad, .atP (.inl _) => Doomed (r :: s) (e, ε) bad
  | r :: s, (e, ε), bad, .atV (.inl m) => cnt (fun c : r.Chal => ¬ Doomed s ε (fun t => bad (m, c, t))) ≤ e
  | _ :: s, (_, ε), bad, .atP (.inr (m, c, τ)) => Lost s ε (fun t => bad (m, c, t)) (.atP τ)
  | _ :: s, (_, ε), bad, .atV (.inr (m, c, τ)) => Lost s ε (fun t => bad (m, c, t)) (.atV τ)
  | _ :: s, (_, ε), bad, .full (m, c, τ) => Lost s ε (fun t => bad (m, c, t)) (.full τ)

theorem lost_empty :
    ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop), Lost s ε bad (PTr.empty s) ↔ Doomed s ε bad
  | [], _, _ => Iff.rfl
  | _ :: _, (_, _), _ => Iff.rfl

theorem lost_cons {r : Round} {s : Shape} (e : ℕ) (ε : Err s) (bad : Tr (r :: s) → Prop)
    (m : r.Msg) (c : r.Chal) :
    ∀ τ : PTr s, Lost (r :: s) (e, ε) bad (PTr.cons m c τ) ↔ Lost s ε (fun t => bad (m, c, t)) τ
  | .atP _ => Iff.rfl
  | .atV _ => Iff.rfl
  | .full _ => Iff.rfl

theorem lost_full :
    ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop) (τ : Tr s), Lost s ε bad (.full τ) ↔ bad τ
  | [], _, _, () => Iff.rfl
  | _ :: s, (_, ε), bad, (m, c, τ) => lost_full s ε (fun t => bad (m, c, t)) τ

theorem Lost.prover : ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop) (τ : AtP s) (m : τ.round.Msg),
    Lost s ε bad (.atP τ) → Lost s ε bad (.atV (τ.snoc m))
  | _ :: _, (_, _), _, .inl _, m, h => h m
  | _ :: s, (_, ε), bad, .inr (m', c', τ), m, h => Lost.prover s ε (fun t => bad (m', c', t)) τ m h

theorem Lost.verifier : ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop) (τ : AtV s),
    Lost s ε bad (.atV τ) → cnt (fun c : τ.round.Chal => ¬ Lost s ε bad (τ.snoc c)) ≤ τ.err ε
  | _ :: s, (e, ε), bad, .inl m, h =>
      le_trans (cnt_mono fun c hc hd =>
        hc ((lost_cons e ε bad m c _).2 ((lost_empty s ε _).2 hd))) h
  | _ :: s, (e, ε), bad, .inr (m', c', τ), h =>
      le_trans (cnt_mono fun _ hc hl => hc ((lost_cons e ε bad m' c' _).2 hl))
        (Lost.verifier s ε (fun t => bad (m', c', t)) τ h)

/-- One round (the textbook remarks after Definition 31.1.2 that for k = 1 the definition is the
soundness of a PCP):
whatever the prover sends, at most e values of the verifier's randomness are not bad for it. -/
theorem doomed_singleton (r : Round) (e : ℕ) (bad : Tr [r] → Prop) :
    Doomed [r] (e, ()) bad ↔ ∀ m : r.Msg, cnt (fun c : r.Chal => ¬ bad (m, c, ())) ≤ e := Iff.rfl

/-! ## 4. The error law with a randomised malicious prover (textbook, Definition 31.1.2, as printed)

(The law itself is not stated in this file; below is only the step from a count to a probability at
one transcript.)
The textbook's clause reads: for every malicious prover that outputs ((Πⱼ)_{j ≤ i}, (ρⱼ)_{j < i}),
Pr[ State(.., Πᵢ, ρᵢ) = 1 | State(.., Πᵢ) = 0 ] ≤ εᵢ over the prover's coins and a uniform ρᵢ.
A malicious prover is a distribution p on transcripts at the verifier. The conditional probability
can be written without a division:
Pr[ State(τ) = 0 and State(τ ‖ ρ) = 1 ] ≤ δ · Pr[ State(τ) = 0 ], where δ bounds the error of the
rounds in which p stops (for a prover that always stops in round i: δ = εᵢ). -/

section Randomised
variable {s : Shape} {ε : Err s}

/-- The error law at one transcript, as a probability. -/
theorem cnt_le_err_iff_pr_le (St : PTr s → Bool) (τ : AtV s) :
    cnt (fun c : τ.round.Chal => St (τ.snoc c) = true) ≤ τ.err ε ↔
      pr (unif τ.round.Chal) {c | St (τ.snoc c) = true} ≤ τ.errPr ε :=
  (pr_unif_le_iff_cnt_le _ _).symm



end Randomised



theorem card_rho_cons (r : Round) (s : Shape) :
    Fintype.card (Rho (r :: s)) = Fintype.card r.Chal * Fintype.card (Rho s) :=
  (Fintype.card_congr (Equiv.refl (r.Chal × Rho s))).trans (Fintype.card_prod r.Chal (Rho s))

end Iop
