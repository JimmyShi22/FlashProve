-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Slots.lean: the rows' first equation (D1) (the hiding polynomial's
coefficients are
the world's values under the slots from the record's first on) as a lemma, for parameters whose
places are
the slots' own numbers.

Main names:
  `posP l s i`: the number of the slot at which the library's place
    (OnBytes/Tie/Pv/Psc/StepWalk.lean) lays the
    coefficient named i, from the slot s on.
  `place_pos`: place mask (pVars l d) s i = mask (posP l s (pIx l d i)).
  `degSum`, `posP_lt`: s ≤ posP l s i < s + 1 + the sum of the formats' degrees.
  `D1_of_places`: where the entry at the place of the coefficient named i is slot (posP … first i):
    (D1).

Sources: Cb/Ld/LdHide.lean (HVar, HIdx); Cb/Ld/LdPsc.lean (PFmt, PDats, pVars, PIdx, pIx, PscPar);
StepWalk.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Psc.StepWalk
import Cb.Ld.LdPsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Cb

variable {K : Type}

/-- The slot of the coefficient named i, from the slot s on. -/
def posP : (l : List (PFmt K)) → ℕ → PIdx l → ℕ
  | [], s, _ => s
  | [_], s, Sum.inl t => s + 1 + (t : ℕ)
  | [_], s, Sum.inr _ => s
  | _ :: _ :: _, s, Sum.inl t => s + (t : ℕ)
  | f :: f' :: l, s, Sum.inr i => posP (f' :: l) (s + f.n) i

theorem place_pos (mask : ℕ → K) : ∀ (l : List (PFmt K)) (d : PDats l) (s : ℕ) (i : HIdx (pVars l d)),
    OnBytes.Road.Hd.place mask (pVars l d) s i = mask (posP l s (pIx l d i))
  | [], _, _, _ => rfl
  | [_], _, _, Sum.inl _ => rfl
  | [_], _, _, Sum.inr _ => rfl
  | _ :: _ :: _, _, _, Sum.inl _ => rfl
  | f :: f' :: l, d, s, Sum.inr i => place_pos mask (f' :: l) d.2 (s + f.n) i

/-- The sum of the formats' degrees. -/
def degSum : List (PFmt K) → ℕ
  | [] => 0
  | f :: l => f.n + degSum l

theorem posP_lt : ∀ (l : List (PFmt K)) (s : ℕ) (i : PIdx l), s ≤ posP l s i ∧ posP l s i < s + 1 + degSum l
  | [], s, _ => ⟨le_refl _, by show s < s + 1 + 0; omega⟩
  | [f], s, Sum.inl t => ⟨by show s ≤ s + 1 + t.1; omega, by
      show s + 1 + t.1 < s + 1 + (f.n + 0)
      have := t.2
      omega⟩
  | [f], s, Sum.inr _ => ⟨le_refl _, by show s < s + 1 + (f.n + 0); omega⟩
  | f :: f' :: l, s, Sum.inl t => ⟨by show s ≤ s + t.1; omega, by
      show s + t.1 < s + 1 + (f.n + degSum (f' :: l))
      have := t.2
      omega⟩
  | f :: f' :: l, s, Sum.inr i => by
    obtain ⟨a, b⟩ := posP_lt (f' :: l) (s + f.n) i
    exact ⟨by show s ≤ posP (f' :: l) (s + f.n) i; omega, by
      show posP (f' :: l) (s + f.n) i < s + 1 + (f.n + degSum (f' :: l))
      omega⟩

/-- **(D1) from the places.** -/
theorem D1_of_places [Field K] (Y : PscPar K) (st : Y.St) (m : Y.J → K) (slot : ℕ → K) (first : ℕ)
    (h : ∀ i : PIdx Y.fmt, m (Y.wAt i) = slot (posP Y.fmt first i)) :
    Y.W st m = OnBytes.Road.Hd.place slot (Y.vars st) first := by
  funext i
  rw [place_pos]
  exact h _

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.place_pos
#print axioms VerifiableInference.Desc.First.Att.P.posP_lt
#print axioms VerifiableInference.Desc.First.Att.P.D1_of_places
