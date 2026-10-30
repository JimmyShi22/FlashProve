-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LowerKit.lean: lemmas on `Doomed` (Iop/Rbr.lean): one round (`doomed_cons`), two protocols
that must both accept (`doomed_and`), two counting rules (`cnt_exists_unique_le`, `cnt_and_le`).
Also: `Setup.div_mod_aux`. (Words of this library: lean/GLOSSARY.md.)

Notation:
 * `Doomed` s ε bad: a proposition: whatever the prover sends, at most e values (e: the number that
   ε has for this round) of the next challenge lead to a transcript that is not doomed; at the end,
   `bad` holds (Iop/Rbr.lean).
 * `Err` s: one number for each round: how many values of the challenge may lead from a doomed
   transcript to one that is not doomed (Iop/Rbr.lean).

Round-by-round soundness is the notion of R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G.
Rothblum, R. Rothblum, ePrint 2018/1004, Definition 5.3.
-/
import Blocks.EqN
import Blocks.Decode
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks

open Iop Prob Finset

/-! ## 1. Lemmas on `Doomed` -/

section Doomed

/-- If every full transcript is bad for the prover, the prover is doomed, with any errors. -/
theorem doomed_of_forall :
    ∀ (s : Shape) (ε : Err s) {bad : Tr s → Prop}, (∀ τ, bad τ) → Doomed s ε bad
  | [], _, _, h => h ()
  | _ :: s, (_, ε), _, h => fun m => by
      rw [cnt_false fun c hc => hc (doomed_of_forall s ε fun τ => h (m, c, τ))]
      exact Nat.zero_le _

/-- One round: if at most e values of the verifier message are bad (a set fixed by the prover
message), and after every other value the prover is doomed, it is doomed before the round. -/
theorem doomed_cons {r : Round} {s : Shape} {e : ℕ} {ε : Err s} {bad : Tr (r :: s) → Prop}
    (B : r.Msg → r.Chal → Prop) (hB : ∀ m, cnt (B m) ≤ e)
    (h : ∀ m c, ¬ B m c → Doomed s ε fun τ => bad (m, c, τ)) : Doomed (r :: s) (e, ε) bad :=
  fun m => (cnt_mono fun c hc => by
    by_contra hn
    exact hc (h m c hn)).trans (hB m)

/-- Two protocols one after the other, both of which must accept: the prover is doomed if it is
doomed in one of them. -/
theorem doomed_and {s t : Shape} (εs : Err s) (εt : Err t) (f : Tr s → Bool) (g : Tr t → Bool)
    (h : Doomed s εs (fun a => f a = false) ∨ Doomed t εt (fun b => g b = false)) :
    Doomed (s ++ t) (Err.app εs εt) fun τ => (f (Tr.fst τ) && g (Tr.snd (s := s) τ)) = false := by
  refine Doomed.append s t εs εt _ ?_
  simp only [Tr.fst_app, Tr.snd_app]
  rcases h with h | h
  · exact Doomed.mono s εs (fun a ha => doomed_of_forall t εt fun b => by rw [ha, Bool.false_and]) h
  · exact doomed_of_forall s εs fun a => Doomed.mono t εt (fun b hb => by rw [hb, Bool.and_false]) h

/-- A set of bad values that is described through a witness which is unique if it exists (here: the
decoding of a word) has at most N elements if each Q b has. -/
theorem cnt_exists_unique_le {α β : Type} [Finite α] {P : β → Prop} {Q : β → α → Prop} {N : ℕ}
    (hu : ∀ b b', P b → P b' → b = b') (hQ : ∀ b, P b → cnt (Q b) ≤ N) :
    cnt (fun a => ∃ b, P b ∧ Q b a) ≤ N := by
  by_cases h : ∃ b, P b
  · obtain ⟨b, hb⟩ := h
    refine (cnt_mono ?_).trans (hQ b hb)
    rintro a ⟨b', hb', hq⟩
    rw [hu b b' hb hb']
    exact hq
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro a ⟨b, hb, -⟩
      exact h ⟨b, hb⟩

/-- A set of bad values with a condition p that does not depend on the verifier message has at most
N elements if Q has under p. -/
theorem cnt_and_le {α : Type} [Finite α] {p : Prop} {Q : α → Prop} {N : ℕ} (h : p → cnt Q ≤ N) :
    cnt (fun a => p ∧ Q a) ≤ N := by
  by_cases hp : p
  · exact (cnt_mono fun _ ha => ha.2).trans (h hp)
  · rw [cnt_false fun _ ha => hp ha.1]
    exact Nat.zero_le _

end Doomed

/-! ## 2. Arithmetic on indices -/

namespace Setup

variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [DecidableEq E]
    [Algebra F E]


omit [Field F] [Fintype F] in
theorem div_mod_aux (B a c : ℕ) (hc : c < B) : (a * B + c) / B = a ∧ (a * B + c) % B = c := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hc
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

end Setup

end Blocks
