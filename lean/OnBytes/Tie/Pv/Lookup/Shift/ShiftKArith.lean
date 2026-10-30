-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Shift/ShiftKArith.lean.
Every error of a sub-proof's lookup is below the number of its round's challenges, if the field is
large enough for the lookup's sizes.

`LT q c e`: the count c is below the size of the challenge set that the entry e says at a field of q
elements (1 where nothing is drawn).
 * `lt_entN`: 4 < q, 2 ^ (v' + 1) ≤ q and w + d < q give `LT q` between the list of errors
   `epsN v' d w n q` and the list of entries `entN 0 v' d w n`, round by round.
 * `lt_all`: the same with the shift's round before them, if 2 ^ dS < q.
 * `allK_sizes`, `allK_small`: on the block's own errors and its own shape: each error is below the
   number of challenges of its round. Premises: the closing binds its variables from the last to the
   first (`A0.oE = Fin.revPerm`); for `allK_small` also the four bounds of `lt_all`, at q = |E| and
   dS = P.d.
Limits: each round's quotient is below 1, and no more is said: no sum of quotients is bounded here.

-/
import OnBytes.Tie.Pv.Lookup.Lists.ShiftKLists

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 List

/-- the count c is below the size of the challenge set that the entry says -/
def LT (q c : ℕ) (e : Fmt.Entry) : Prop := c < sizeOf q e

theorem lt_rd {q c k : ℕ} (name : String) (s : ℕ) (h : c < q ^ k) : LT q c (rd 0 name s k) := by
  simpa [LT, sizeOf, rd] using h
theorem lt_Y {q c : ℕ} (s : ℕ) (h : c < q - 1) : LT q c (rd 0 "PSC Y" s 1 1) := by
  simpa [LT, sizeOf, rd] using h
theorem lt_none (q : ℕ) (name : String) (s : ℕ) : LT q 0 (rdNone name s) := by
  simp [LT, sizeOf, rdNone]

theorem f2_flat {α β γ : Type} {R : α → β → Prop} (f : γ → List α) (g : γ → List β)
    (h : ∀ x, Forall₂ R (f x) (g x)) : ∀ l : List γ, Forall₂ R (l.flatMap f) (l.flatMap g)
  | [] => .nil
  | a :: t => by
    rw [flatMap_cons, flatMap_cons]
    exact f2_append (h a) (f2_flat f g h t)

theorem f2_rep {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ∀ k, Forall₂ R (replicate k a) (replicate k b)
  | 0 => .nil
  | k + 1 => .cons h (f2_rep h k)

/-- n + 1 equal pieces against a first piece and n further ones -/
theorem f2_first {α β : Type} {R : α → β → Prop} {c : List α} {c₁ c₂ : List β} (h₁ : Forall₂ R c c₁)
    (h₂ : Forall₂ R c c₂) : ∀ n, Forall₂ R ((range (n + 1)).flatMap fun _ => c)
      (c₁ ++ (range n).flatMap fun _ => c₂)
  | 0 => by simpa [range_succ] using h₁
  | n + 1 => by
    have e₁ : (range (n + 1 + 1)).flatMap (fun _ => c) =
        (range (n + 1)).flatMap (fun _ => c) ++ c := by
      rw [range_succ, flatMap_append, flatMap_singleton]
    have e₂ : (range (n + 1)).flatMap (fun _ => c₂) = (range n).flatMap (fun _ => c₂) ++ c₂ := by
      rw [range_succ, flatMap_append, flatMap_singleton]
    rw [e₁, e₂, ← append_assoc]
    exact f2_append (f2_first h₁ h₂ n) h₂

theorem lt_psc (q k g gY vals : ℕ) (h1 : 1 < q) (hg : g < q) (hY : gY < q - 1) :
    Forall₂ (LT q) (pscC k g gY) (pscN 0 (replicate k g) true gY vals) := by
  unfold pscC pscN
  rw [if_pos rfl, map_replicate]
  exact f2_append (f2_append (.cons (lt_rd _ _ (by simpa using h1)) .nil)
    (f2_rep (lt_rd _ _ (by simpa using hg)) k)) (.cons (lt_Y _ hY) (.cons (lt_none _ _ _) .nil))

theorem lt_clo (q d w : ℕ) (h2 : 2 < q) :
    Forall₂ (LT q) ([1] ++ replicate d 2 ++ replicate w 1)
      (pscN 0 (replicate d 2 ++ replicate w 1) false 0 0) := by
  have e : pscN 0 (replicate d 2 ++ replicate w 1) false 0 0 =
      [rd 0 "PSC epsilon" 1 1] ++ replicate d (rd 0 "PSC round" 2 1) ++
        replicate w (rd 0 "PSC round" 1 1) := by
    simp [pscN]
  rw [e]
  exact f2_append (f2_append (.cons (lt_rd _ _ (by simpa using (by omega : 1 < q))) .nil)
    (f2_rep (lt_rd _ _ (by simpa using h2)) d))
    (f2_rep (lt_rd _ _ (by simpa using (by omega : 1 < q))) w)

theorem point_lt {q w : ℕ} (h : w < q) : w * q ^ (w - 1) < q ^ w := by
  cases w with
  | zero => simp
  | succ k =>
    have hq : 0 < q := by omega
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_comm]
    exact mul_lt_mul_of_pos_left h (pow_pos hq k)

theorem lt_entN (q v' d w n : ℕ) (h4 : 4 < q) (hv : 2 ^ (v' + 1) ≤ q) (hw : w + d < q) :
    Forall₂ (LT q) (epsN v' d w n q) (entN 0 v' d w n) := by
  have h1 : 1 < q := by omega
  have h2 : 2 < q := by omega
  have h3 : 3 < q - 1 := by omega
  have h2' : 2 < q - 1 := by omega
  have hp : 0 < 2 ^ (v' + 1) := by positivity
  unfold epsN entN
  rw [append_assoc [rd 0 "LKP" 0 1]]
  refine f2_append (f2_append (f2_append (f2_append (f2_append (f2_append (f2_append
    (.cons (lt_rd _ _ (by simpa using (by omega : 2 ^ (v' + 1) - 1 < q))) .nil)
    (f2_first (lt_psc q 0 0 3 3 h1 (by omega) h3) (lt_psc q 0 0 3 2 h1 (by omega) h3) n))
    (.cons (lt_rd _ _ (point_lt (by omega))) .nil))
    (f2_flat _ _ (fun l => f2_append (lt_psc q l 2 2 2 h1 h2 h2')
      (.cons (lt_rd _ _ (by simpa using h1)) .nil)) _))
    (f2_flat _ _ (fun l => f2_append (lt_psc q (w + l) 2 2 2 h1 h2 h2')
      (.cons (lt_rd _ _ (by simpa using h1)) .nil)) _))
    (lt_clo q d w h2))
    (.cons (lt_rd _ _ (point_lt hw)) .nil))
    (lt_psc q (w + d) 2 2 1 h1 h2 h2')

theorem lt_all (q v' d w n dS : ℕ) (several : Bool) (h4 : 4 < q) (hv : 2 ^ (v' + 1) ≤ q)
    (hw : w + d < q) (hS : 2 ^ dS < q) :
    Forall₂ (LT q) (shHead several (2 ^ dS) ++ epsN v' d w n q)
      (shHead several (shiftN 0) ++ entN 0 v' d w n) := by
  refine f2_append ?_ (lt_entN q v' d w n h4 hv hw)
  cases several with
  | true => exact .cons (lt_rd _ _ (by simpa using hS)) .nil
  | false => exact .nil

section
variable {E St : Type} [Field E] [Fintype E]
variable (V : ∀ (Y : PscPar E) Ex, TWhole.ShortK Y Ex)
  (VC : ∀ (Y : PscPar E) Ex, TWhole.ShortKC Y Ex)
  (Ex : ExtSpec) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E)) (several : Bool)

/-- The sizes of the challenge sets, round by round. -/
theorem allK_sizes (ho : A0.oE = Fin.revPerm) :
    (P.allK A0 several V VC (Ex := Ex)).R.shape.map (fun r => Nat.card r.Chal) =
      (shHead several (shiftN 0) ++ entN 0 A0.v' A0.d A0.w A0.n).map (sizeOf (Nat.card E)) :=
  shapeIs_sizes (allK_shape V VC Ex A0 P several 0 ho)

/-- Every error is below its round's number of challenges. -/
theorem allK_small (ho : A0.oE = Fin.revPerm) (h4 : 4 < Fintype.card E)
    (hv : 2 ^ (A0.v' + 1) ≤ Fintype.card E) (hw : A0.w + A0.d < Fintype.card E)
    (hS : 2 ^ P.d < Fintype.card E) :
    Forall₂ (· < ·) (TWhole.errList (P.allK A0 several V VC (Ex := Ex)).e)
      ((P.allK A0 several V VC (Ex := Ex)).R.shape.map fun r => Nat.card r.Chal) := by
  rw [allK_eps V VC Ex A0 P several ho, allK_sizes V VC Ex A0 P several ho,
    Nat.card_eq_fintype_card]
  exact forall₂_map_right_iff.2 (lt_all _ _ _ _ _ _ several h4 hv hw hS)

end
end TwRound
