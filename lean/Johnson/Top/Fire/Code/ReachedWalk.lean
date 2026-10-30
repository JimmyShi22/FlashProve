-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/ReachedWalk.lean: FROM THE GENERIC HISTORY AT THE PIECES' BLOCKS TO A WALK OF THE KIND's OWN BLOCKS AT THE KIND's OWN RECORD. Book-keeping, general: it names no kind.
Why. `Reached` (Reached.lean) speaks of the blocks as a piece holds them (`held b`: the record beside what was handed; the test «below the prime» in front) and of `Block.step`'s yes. A kind's histories speak of its own blocks' decisions at its own record, from some record d0, and begin at a later block than the chain's first.
Main names.
  `Walked bs d0 k a`: from d0 the first k blocks of bs have each DECIDED yes, at some rounds and columns, and have led to a.
  `walked_of_reached`: `Reached ft (l.map held) st₀ (m + j) x` gives a d0 with `Walked (l.drop m) d0 j x.2`: THE LAST j STEPS, AT THE BARE BLOCKS, AT THE RECORD ALONE (`Reached.last`; `held_decide`).
  `Walked.map`: a walk of blocks `bs.map f` is a walk of bs wherever f leaves the decision as it is (a block seated at another type of claims).
  `Walked.of_eq`: along an equation of lists.
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Reached
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {P S Cl Cl' : Type}

/-- **From d0 the first k blocks have each decided yes and have led to a.** -/
def Walked (bs : List (Block S Cl)) (d0 : S) : ℕ → S → Prop
  | 0, a => a = d0
  | k + 1, a => ∃ (a' : S) (b : Block S Cl) (rs : List _root_.Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      Walked bs d0 k a' ∧ bs[k]? = some b ∧ b.decide a' rs gs = .ok a

/-- **The last j steps of a history, at the bare blocks, at the record alone.** -/
theorem walked_of_reached (ft : ℕ) (l : List (Block S Cl)) (st₀ : P × S → Prop) (m : ℕ) :
    ∀ (j : ℕ) (x : P × S), Reached ft (l.map held) st₀ (m + j) x → ∃ d0, Walked (l.drop m) d0 j x.2
  | 0, x, _ => ⟨x.2, rfl⟩
  | j + 1, x, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, _⟩ := Reached.last (k := m + j) h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨d0, hw⟩ := walked_of_reached ft l st₀ m j a' hr
    exact ⟨d0, a'.2, b₀, _, _, hw, by rw [List.getElem?_drop]; exact hb₀, (held_decide b₀ a' _ _ x hd).2⟩

/-- A walk of seated blocks is a walk of the blocks. -/
theorem Walked.map (f : Block S Cl → Block S Cl') (hf : ∀ b a rs gs, (f b).decide a rs gs = b.decide a rs gs) (bs : List (Block S Cl)) (d0 : S) :
    ∀ (k : ℕ) (a : S), Walked (bs.map f) d0 k a → Walked bs d0 k a
  | 0, _, h => h
  | k + 1, a, h => by
    obtain ⟨a', b, rs, gs, hw, hb, hd⟩ := h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨a', b₀, rs, gs, Walked.map f hf bs d0 k a' hw, hb₀, (hf b₀ a' rs gs).symm.trans hd⟩

theorem Walked.of_eq {bs bs' : List (Block S Cl)} (e : bs = bs') {d0 : S} {k : ℕ} {a : S} (h : Walked bs d0 k a) : Walked bs' d0 k a := e ▸ h

/-- A walk reads of its list the first k blocks alone. -/
theorem Walked.take (bs more : List (Block S Cl)) (d0 : S) : ∀ (k : ℕ) (a : S), k ≤ bs.length → Walked (bs ++ more) d0 k a → Walked bs d0 k a
  | 0, _, _, h => h
  | k + 1, a, hk, h => by
    obtain ⟨a', b, rs, gs, hw, hb, hd⟩ := h
    rw [List.getElem?_append_left (by omega)] at hb
    exact ⟨a', b, rs, gs, Walked.take bs more d0 k a' (by omega) hw, hb, hd⟩

end

end LPFD

#print axioms LPFD.walked_of_reached
#print axioms LPFD.Walked.map
#print axioms LPFD.Walked.take
