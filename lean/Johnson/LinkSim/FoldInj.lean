-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/FoldInj.lean: the coefficients of a hiding polynomial at plain variables of degree 2
are determined by its sum and by the coefficients 0 and 2 of its round polynomials. Statements and
proofs. Pure algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  hW_inj        In the library's names: if two coefficient vectors W and W' give the same sum (hMu)
                and the same coefficients 0 and 2 of their round polynomials (pairsOf of hTr), at
                the same carried value A (see Johnson/LinkSim/FoldTriTie.lean) and the same point
                g, then W = W'.
  mu_shown_inj  Two lists of pairs with constants that have the same sum and the same rounds' pairs
                are equal (by unW_shown, Johnson/LinkSim/FoldTri.lean).
  listW_inj     listW (Johnson/LinkSim/FoldTriTie.lean) is injective.
  addW_cancel   If a + x = b + x entry by entry, for lists a, b, x of the same length, then a = b.

How it fits. Johnson/LinkSim/AtText/FoldInjAt.lean uses hW_inj and addW_cancel, for the negative
test of Johnson/LinkSim/AtText/ShortTail.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.FoldShift

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb

/-- Same sum and same rounds' pairs give the same coefficients and constant. -/
theorem mu_shown_inj {R : Type} [CommRing R] {l l' : List (R × R)} {c c' : R}
    (h1 : mu l c = mu l' c') (h2 : shownW l c = shownW l' c') : (l, c) = (l', c') := by
  rw [← unW_shown l c, ← unW_shown l' c', h1, h2]

/-- Adding the same list x, entry by entry, is injective on lists of x's length. -/
theorem addW_cancel {R : Type} [CommRing R] : ∀ (a b x : List (R × R)), a.length = x.length →
    b.length = x.length → addW a x = addW b x → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, [], _, h, _ => by cases h
  | [], _ :: _, _ :: _, h, _, _ => by cases h
  | _ :: _, [], [], h, _, _ => by cases h
  | _ :: _, [], _ :: _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], h, _, _ => by cases h
  | u :: a, w :: b, y :: x, ha, hb, h => by
      have h1 : (u.1 + y.1, u.2 + y.2) = (w.1 + y.1, w.2 + y.2) := (List.cons.inj h).1
      have h2 : addW a x = addW b x := (List.cons.inj h).2
      rw [addW_cancel a b x (Nat.succ.inj ha) (Nat.succ.inj hb) h2,
        Prod.ext (add_right_cancel (Prod.ext_iff.mp h1).1)
          (add_right_cancel (Prod.ext_iff.mp h1).2)]

variable {E : Type} [Field E]

/-- listW is injective. -/
theorem listW_inj : ∀ (k : ℕ) (W W' : HIdx (sVars E 2 k) → E), listW k W = listW k W' → W = W'
  | 0, W, W', h => funext fun _ => (Prod.ext_iff.mp h).2
  | k + 1, W, W', h => by
      have h1 : (W (.inl (0 : Fin 2)), W (.inl (1 : Fin 2))) :: (listW k fun i => W (.inr i)).1 =
          (W' (.inl (0 : Fin 2)), W' (.inl (1 : Fin 2))) :: (listW k fun i => W' (.inr i)).1 :=
        (Prod.ext_iff.mp h).1
      have h2 : (listW k fun i => W (.inr i)).2 = (listW k fun i => W' (.inr i)).2 :=
        (Prod.ext_iff.mp h).2
      have ht := listW_inj k (fun i => W (.inr i)) (fun i => W' (.inr i))
        (Prod.ext (List.cons.inj h1).2 h2)
      have hh := Prod.ext_iff.mp (List.cons.inj h1).1
      funext i
      rcases i with t | i
      · have ht2 : t = (0 : Fin 2) ∨ t = (1 : Fin 2) := by
          rcases t with ⟨n, hn⟩
          have hn' : n < 2 := hn
          rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases ht2 with rfl | rfl
        · exact hh.1
        · exact hh.2
      · exact congrFun ht i

/-- The coefficients are determined by the sum and the rounds' coefficients 0 and 2, at fixed A and
g. -/
theorem hW_inj (k : ℕ) (W W' : HIdx (sVars E 2 k) → E) (A : E) (g : HPt (sVars E 2 k))
    (h1 : hMu (sVars E 2 k) W = hMu (sVars E 2 k) W')
    (h2 : pairsOf k (hTr (sVars E 2 k) A W g) = pairsOf k (hTr (sVars E 2 k) A W' g)) : W = W' := by
  rw [hMu_list, hMu_list] at h1
  rw [hTr_list, hTr_list] at h2
  exact listW_inj k W W' (mu_shown_inj h1 h2)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.mu_shown_inj
#print axioms OnBytes.LinkSim.addW_cancel
#print axioms OnBytes.LinkSim.listW_inj
#print axioms OnBytes.LinkSim.hW_inj
