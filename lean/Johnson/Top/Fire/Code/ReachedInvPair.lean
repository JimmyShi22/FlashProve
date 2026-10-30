-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/ReachedInvPair.lean: AN INVARIANT INDEXED BY THE BORDER ALONG A HISTORY
(Reached), THAT READS BOTH HALVES OF THE STATE: what was handed to the chain
(held: no block turns it) AND the chain's own state. THE GENERAL FORM OF
reached_held_inv (ReachedInv.lean), whose invariant reads the own half alone. A NEAR TWIN BY DESIGN.

WHY: at the shared chain Tests₂ has two fields that TIE the halves (key · codes)
and six that read the handed half alone.
  StepInvP            what a step asks: at the block's yes on fitting rounds, AT EVERY HANDED HALF p
  reached_held_invP   PROVED: reached_held_inv's recursion, with held_decide's first half spent too
  reached_held_inv_is PROVED: THE FIT: reached_held_inv is this one at I k a := I' k a.2
  stepP_of_step       PROVED: a step of StepInv's form is a step of this form, at the own half
  stepP_imp           PROVED: a premise on the handed half alone may be carried in front of a step
THE SILLY MEMBERS: K := 0: it says h0 alone · I := fun _ _ => True: nothing.
OBJECT: Reached ft (l.map held) st₀ · USER: KeyASide2AtFk.lean · LETTERS: all.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.ReachedInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {P S Cl : Type}

/-- What a step of the invariant asks: at the block's yes on fitting rounds, at every handed half.
-/
def StepInvP (b : Block S Cl) (A B : P × S → Prop) : Prop :=
  ∀ (p : P) (s s' : S) (rs : List _root_.Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' → A (p, s) → B (p, s')

theorem reached_held_invP (ft : ℕ) (l : List (Block S Cl)) (st₀ : P × S → Prop)
    (I : ℕ → P × S → Prop) (K : ℕ) (h0 : ∀ a, st₀ a → I 0 a)
    (hs : ∀ k, k < K → ∀ b, l[k]? = some b → StepInvP b (I k) (I (k + 1))) :
    ∀ (k : ℕ) (a : P × S), k ≤ K → Reached ft (l.map held) st₀ k a → I k a
  | 0, a, _, h => h0 a h
  | k + 1, a, hk, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨e1, e2⟩ := held_decide b₀ a' _ _ a hd
    have h' : I (k + 1) (a'.1, a.2) := hs k (by omega) b₀ hb₀ a'.1 a'.2 a.2 rs _ hf e2
      (reached_held_invP ft l st₀ I K h0 hs k a' (by omega) hr)
    have ea : a = (a'.1, a.2) := Prod.ext e1 rfl
    rw [ea]
    exact h'

/-- **The fit**: reached_held_inv is this one at an invariant that reads the own half alone. -/
theorem reached_held_inv_is (ft : ℕ) (l : List (Block S Cl)) (st₀ : P × S → Prop)
    (I : ℕ → S → Prop) (K : ℕ) (h0 : ∀ a, st₀ a → I 0 a.2)
    (hs : ∀ k, k < K → ∀ b, l[k]? = some b → StepInv b (I k) (I (k + 1))) (k : ℕ) (a : P × S)
    (hk : k ≤ K) (h : Reached ft (l.map held) st₀ k a) : I k a.2 :=
  reached_held_invP ft l st₀ (fun k a => I k a.2) K h0
    (fun k hk b hb _ s s' rs gs hf hy hA => hs k hk b hb s s' rs gs hf hy hA) k a hk h

/-- A step of StepInv's form is a step of this form, at the own half. -/
theorem stepP_of_step (b : Block S Cl) (A B : S → Prop) (h : StepInv b A B) :
    StepInvP (P := P) b (fun a => A a.2) (fun a => B a.2) :=
  fun _ s s' rs gs hf hy hA => h s s' rs gs hf hy hA

/-- A premise on the handed half alone may be carried in front of a step. -/
theorem stepP_imp (b : Block S Cl) (Q : P → Prop) (A B : P × S → Prop) (h : StepInvP b A B) :
    StepInvP b (fun a => Q a.1 → A a) (fun a => Q a.1 → B a) :=
  fun p s s' rs gs hf hy hA hq => h p s s' rs gs hf hy (hA hq)

end

end LPFD

#print axioms LPFD.reached_held_invP
#print axioms LPFD.reached_held_inv_is
#print axioms LPFD.stepP_of_step
#print axioms LPFD.stepP_imp
