-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/ReachedInv.lean: AN INVARIANT INDEXED BY THE BORDER ALONG A HISTORY (Reached: Johnson/Top/Fire/Code/Reached.lean): where I 0 holds at the start and the k-th block's yes carries I k to I (k + 1) for every k below K, I k holds at every record that is reached at a border k ≤ K. General: no letter of any kind.
  reached_held_inv   PROVED. KIN: reached_held_fst (RowsWoven.lean:42: ONE predicate of the held part; the same recursion) · Keeps.foldBlocks_keeps | chainAt_keeps | keeps_of_inv (Johnson/Desc/FoldKeeps.lean: ONE relation, on a run). [A search, not held against the library that ships, found no rule with an invariant indexed by the border.]
  reached_held_from  PROVED: the like from a border j on: every record reached at k ≥ j has a record reached at j in front of it from which the blocks j … k − 1 said yes: so I j THERE carries to I k HERE.
THE SILLY MEMBERS: K := 0: it says h0 alone · I := fun _ _ => True: nothing.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowsWoven

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {P S Cl : Type}

/-- What a step of the invariant asks: at the block's yes on fitting rounds. -/
def StepInv (b : Block S Cl) (A B : S → Prop) : Prop :=
  ∀ (s s' : S) (rs : List _root_.Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' → A s → B s'

theorem reached_held_inv (ft : ℕ) (l : List (Block S Cl)) (st₀ : P × S → Prop) (I : ℕ → S → Prop) (K : ℕ)
    (h0 : ∀ a, st₀ a → I 0 a.2) (hs : ∀ k, k < K → ∀ b, l[k]? = some b → StepInv b (I k) (I (k + 1))) :
    ∀ (k : ℕ) (a : P × S), k ≤ K → Reached ft (l.map held) st₀ k a → I k a.2
  | 0, a, _, h => h0 a h
  | k + 1, a, hk, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact hs k (by omega) b₀ hb₀ a'.2 a.2 rs _ hf (held_decide b₀ a' _ _ a hd).2 (reached_held_inv ft l st₀ I K h0 hs k a' (by omega) hr)

theorem reached_held_from (ft : ℕ) (l : List (Block S Cl)) (st₀ : P × S → Prop) (I : ℕ → S → Prop) (j K : ℕ)
    (hj : ∀ a, Reached ft (l.map held) st₀ j a → I j a.2) (hs : ∀ k, j ≤ k → k < K → ∀ b, l[k]? = some b → StepInv b (I k) (I (k + 1))) :
    ∀ (n : ℕ) (a : P × S), j + n ≤ K → Reached ft (l.map held) st₀ (j + n) a → I (j + n) a.2
  | 0, a, _, h => hj a h
  | n + 1, a, hk, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last (k := j + n) h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact hs (j + n) (by omega) (by omega) b₀ hb₀ a'.2 a.2 rs _ hf (held_decide b₀ a' _ _ a hd).2 (reached_held_from ft l st₀ I j K hj hs n a' (by omega) hr)

end

end LPFD

#print axioms LPFD.reached_held_inv
#print axioms LPFD.reached_held_from
