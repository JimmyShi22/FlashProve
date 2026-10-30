-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Rbr.lean: round-by-round soundness, as a recursion on the list of rounds.

Errors (`Err s`: one number for each round) are counts of challenge values, not probabilities.
`doomed_of_clean` derives `Doomed` from a set of bad challenges for each round, under the hypotheses
of its statement; Blocks/Block.lean, Iop/Compose.lean and Iop/Late.lean use it.

Limits: That `Doomed` is equivalent to "there is a state function with four laws" is not proved in
this library (Iop/State.lean). (the two directions stand apart: `Lost`, Iop/State.lean;
`doomed_of_jointLaw`, Ior/BatchKProofs.lean, with `jointLaw_one`, Iop/BatchOne.lean; this file
joins them in no statement)

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
-/
import Iop.Shape
import Prob.Cnt

namespace Iop
open Prob

/-- One number for each round: how many values of the challenge may lead from a doomed transcript to
one that is not doomed. -/
def Err : Shape → Type
  | [] => Unit
  | _ :: s => ℕ × Err s

def Err.app : {s t : Shape} → Err s → Err t → Err (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (e, a), b => (e, Err.app a b)

/-- The empty transcript is doomed with respect to `bad` (a property of full transcripts, bad for
the prover): whatever the prover sends, at most e values of the next challenge lead to a transcript
that is not doomed; at the end, `bad` holds. The literature says instead: there is a state function
on partial transcripts with four laws (Iop/State.lean). Read as State = 0, `Doomed` is the canonical
state function: the least one as a function, that is, the largest set of partial transcripts with
State = 0; this is not proved in this library. -/
def Doomed : (s : Shape) → Err s → (Tr s → Prop) → Prop
  | [], _, bad => bad ()
  | r :: s, (e, ε), bad =>
    ∀ m : r.Msg, cnt (fun c : r.Chal => ¬ Doomed s ε (fun τ => bad (m, c, τ))) ≤ e

theorem Doomed.mono : ∀ (s : Shape) (ε : Err s) {bad bad' : Tr s → Prop},
    (∀ τ, bad τ → bad' τ) → Doomed s ε bad → Doomed s ε bad'
  | [], _, _, _, h, hd => h _ hd
  | _ :: s, (_, ε), _, _, h, hd => fun m =>
      le_trans (cnt_mono (fun c hc hd' => hc (Doomed.mono s ε (fun τ => h (m, c, τ)) hd'))) (hd m)

/-- Pointwise order and maximum of error lists. -/
def Err.le : {s : Shape} → Err s → Err s → Prop
  | [], _, _ => True
  | _ :: _, (e, ε), (e', ε') => e ≤ e' ∧ Err.le ε ε'

def Err.max : {s : Shape} → Err s → Err s → Err s
  | [], _, _ => ()
  | _ :: _, (e, ε), (e', ε') => (Nat.max e e', Err.max ε ε')

theorem Err.le_max_left : ∀ {s : Shape} (ε ε' : Err s), Err.le ε (Err.max ε ε')
  | [], _, _ => trivial
  | _ :: _, (_, ε), (_, ε') => ⟨Nat.le_max_left _ _, Err.le_max_left ε ε'⟩

theorem Err.le_max_right : ∀ {s : Shape} (ε ε' : Err s), Err.le ε' (Err.max ε ε')
  | [], _, _ => trivial
  | _ :: _, (_, ε), (_, ε') => ⟨Nat.le_max_right _ _, Err.le_max_right ε ε'⟩

/-- Larger errors give a weaker statement. With `Err.max`, a proof that splits into two cases on the
statement can take for each round the larger of its errors in the two cases. -/
theorem Doomed.mono_err :
    ∀ (s : Shape) {ε ε' : Err s} {bad : Tr s → Prop}, Err.le ε ε' → Doomed s ε bad → Doomed s ε' bad
  | [], _, _, _, _, hd => hd
  | _ :: s, (_, _), (_, _), _, h, hd => fun m =>
      le_trans (le_trans (cnt_mono (fun _ hc hd' => hc (Doomed.mono_err s h.2 hd'))) (hd m)) h.1

/-- Sequential composition: if s is doomed to "t is doomed", then s ++ t is doomed, with the errors
concatenated. -/
theorem Doomed.append :
    ∀ (s t : Shape) (ε : Err s) (ε' : Err t) (bad : Tr (s ++ t) → Prop),
      Doomed s ε (fun a => Doomed t ε' (fun b => bad (Tr.app a b))) →
      Doomed (s ++ t) (Err.app ε ε') bad
  | [], _, _, _, _, h => h
  | _ :: s, t, (_, ε), ε', bad, h => fun m =>
      le_trans (cnt_mono
        (fun c hc hd' => hc (Doomed.append s t ε ε' (fun τ => bad (m, c, τ)) hd'))) (h m)

/-- A family of bad sets: for each round a set of values of the challenge that is fixed before the
challenge (it may depend on everything earlier, the prover message of the round included). -/
def BadFam : Shape → Type
  | [] => Unit
  | r :: s => (r.Msg → Set r.Chal) × (r.Msg → r.Chal → BadFam s)

/-- No challenge of the transcript is bad (the transcript is clean). -/
def BadFam.Clean : {s : Shape} → BadFam s → Tr s → Prop
  | [], _, _ => True
  | _ :: _, (B, k), (m, c, τ) => c ∉ B m ∧ BadFam.Clean (k m c) τ

/-- The bad sets are within the errors. -/
def BadFam.Within : {s : Shape} → BadFam s → Err s → Prop
  | [], _, _ => True
  | _ :: _, (B, k), (e, ε) => (∀ m, cnt (fun c => c ∈ B m) ≤ e) ∧ ∀ m c, BadFam.Within (k m c) ε

/-- Bad sets give round-by-round soundness: if they are within the errors and `bad` holds of every
clean full transcript, the empty transcript is doomed. -/
theorem doomed_of_clean : ∀ (s : Shape) (ε : Err s) (B : BadFam s) (bad : Tr s → Prop),
    B.Within ε → (∀ τ, B.Clean τ → bad τ) → Doomed s ε bad
  | [], _, _, _, _, h => h () trivial
  | _ :: s, (_, ε), (_, k), _, hW, h => fun m =>
      le_trans (cnt_mono (fun c hc => by
        by_contra hcB
        exact hc (doomed_of_clean s ε (k m c) _ (hW.2 m c) (fun τ hτ => h (m, c, τ) ⟨hcB, hτ⟩)))) (hW.1 m)

end Iop
