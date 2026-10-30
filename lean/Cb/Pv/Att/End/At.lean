-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/At.lean: what the three reading forms of Cb/Pv/Att/End/Tabs.lean are worth at any
values of the late entries.

Statements and proofs. Cb/Pv/Att/End/Tabs.lean says what a reading form is worth if every late entry
has its meant value. Here the late entries are free: a reading form is a public combination of late
entries, written out. This is the form in which a reading form can be held against a form of the
verifier, which reads the entries of the message as they were sent.

Main names: entF_at, rdRow_at, rdLong_at, rdCol_at: the forms written out. rdRow_congr,
rdLong_congr, rdCol_congr: a reading form reads only some coordinates of its points. endF_at: the
claim on an end value, at any values of the entries. rowF_at: the claim on the row. plainCl_at: all
claims of a sumcheck's ledger.

Limits: algebra on the definitions. Nothing is said on a verifier.


-/
import Cb.Pv.Att.End.Tabs
import Cb.Pv.Att.End.Step
import Cb.Pv.Att.Mean.BitsScore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] {Tn J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] (D : Dim) (ls lmS : ℕ) (Y : LateLay Tn J₂) (x : J₁ ⊕ J₂ → E)

/-- The form of a late entry is worth the entry. -/
theorem entF_at (n : Tn × Raw) : (entF (J₁ := J₁) Y n).val x = x (.inr (Y.at' n)) := by
  unfold entF
  exact val_aEnt x _

theorem rdRow_at (T : Tn) (vg : ℕ → E) (n : ℕ) (base : ℕ → ℕ → Raw) :
    (rdRow (J₁ := J₁) D Y T vg n base).val x =
      ∑ g ∈ range D.nG, eqN D.lg 0 vg g *
        ∑ k ∈ range n, 256 ^ k * x (.inr (Y.at' (T, base k g))) := by
  unfold rdRow
  rw [val_aSum]
  refine sum_congr rfl fun g _ => ?_
  rw [val_aSmul, val_aSum]
  congr 1
  exact sum_congr rfl fun k _ => by rw [val_aSmul, entF_at]

theorem rdCol_at (T : Tn) (l : ℕ) (z : ℕ → E) (r : Raw) :
    (rdCol (J₁ := J₁) lmS Y T l z r).val x =
      ∑ hi ∈ range (2 ^ (l - lmS)), eqN (l - lmS) 0 z hi *
        x (.inr (Y.at' (T, r.addX (hi * 2 ^ lmS)))) := by
  unfold rdCol
  rw [val_aSum]
  exact sum_congr rfl fun hi _ => by rw [val_aSmul, entF_at]

theorem rdLong_at (T : Tn) (vg vn : ℕ → E) (n : ℕ) (base : ℕ → ℕ → Raw) :
    (rdLong (J₁ := J₁) D ls Y T vg vn n base).val x =
      ∑ g ∈ range D.nG, eqN D.lg 0 vg g *
        ∑ ch ∈ range (2 ^ (D.ln - ls)), eqN (D.ln - ls) 0 vn ch *
          ∑ k ∈ range n, 256 ^ k * x (.inr (Y.at' (T, (base k g).addN (ch * 2 ^ ls)))) := by
  unfold rdLong
  rw [val_aSum]
  refine sum_congr rfl fun g _ => ?_
  rw [val_aSmul, val_aSum]
  congr 1
  refine sum_congr rfl fun ch _ => ?_
  rw [val_aSmul, val_aSum]
  congr 1
  exact sum_congr rfl fun k _ => by rw [val_aSmul, entF_at]

/-! ### The coordinates that are read -/

theorem rdRow_congr (T : Tn) {vg vg' : ℕ → E} (h : ∀ k < D.lg, vg k = vg' k) (n : ℕ)
    (base : ℕ → ℕ → Raw) :
    (rdRow (J₁ := J₁) D Y T vg n base).val x = (rdRow (J₁ := J₁) D Y T vg' n base).val x := by
  rw [rdRow_at, rdRow_at]
  refine sum_congr rfl fun g _ => ?_
  rw [eqN_agree (a := vg) (a' := vg') (off := 0) (off' := 0)
    (fun k hk => by rw [Nat.zero_add]; exact h k hk) g]

theorem rdCol_congr (T : Tn) (l : ℕ) {z z' : ℕ → E} (h : ∀ k < l - lmS, z k = z' k) (r : Raw) :
    (rdCol (J₁ := J₁) lmS Y T l z r).val x = (rdCol (J₁ := J₁) lmS Y T l z' r).val x := by
  rw [rdCol_at, rdCol_at]
  refine sum_congr rfl fun hi _ => ?_
  rw [eqN_agree (a := z) (a' := z') (off := 0) (off' := 0)
    (fun k hk => by rw [Nat.zero_add]; exact h k hk) hi]

theorem rdLong_congr (T : Tn) {vg vg' vn vn' : ℕ → E} (hg : ∀ k < D.lg, vg k = vg' k)
    (hn : ∀ k < D.ln - ls, vn k = vn' k) (n : ℕ) (base : ℕ → ℕ → Raw) :
    (rdLong (J₁ := J₁) D ls Y T vg vn n base).val x =
      (rdLong (J₁ := J₁) D ls Y T vg' vn' n base).val x := by
  rw [rdLong_at, rdLong_at]
  refine sum_congr rfl fun g _ => ?_
  rw [eqN_agree (a := vg) (a' := vg') (off := 0) (off' := 0)
    (fun k hk => by rw [Nat.zero_add]; exact hg k hk) g]
  congr 1
  refine sum_congr rfl fun ch _ => ?_
  rw [eqN_agree (a := vn) (a' := vn') (off := 0) (off' := 0)
    (fun k hk => by rw [Nat.zero_add]; exact hn k hk) ch]

end Cb.Pv.Att.End

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset

/-! ### The claim on an end value, at any values of the entries -/

section End
variable {E : Type} [Field E] [Fintype E] (T : PlainSc E) {J₂ : Type} [Fintype J₂]
  [DecidableEq J₂] [DecidableEq T.J]

/-- The claim on end value a holds of x if and only if what was shown, less the last coordinate
times the mask entry, is what the form r is worth. -/
theorem endF_at (o : T.our.par.Out) (a : T.A) (r : Aff E (T.J ⊕ J₂)) (x : T.J ⊕ J₂ → E) :
    (endF T o a r).Holds x ↔
      o.vals a - T.our.lst o.st (T.our.par.hp o.st o.pt) * x (.inl (T.cAt a)) = r.val x := by
  unfold endF
  rw [Aff.claim_holds, val_aSub, val_aSub, val_aConst, val_aSmul, val_aEnt]
  exact sub_eq_zero

omit [Fintype E] [DecidableEq J₂] in
/-- A form on the early entries, lifted, holds of early and late entries if and only if it holds of
the early ones. -/
theorem liftF_at {J₁ : Type} [Fintype J₁] (f : Form E J₁) (m : J₁ → E) (u : J₂ → E) :
    (liftF (J₂ := J₂) f).Holds (Sum.elim m u) ↔ f.Holds m := by
  unfold Form.Holds Form.gap liftF
  rw [Fintype.sum_sum_type]
  simp

omit [DecidableEq T.J] [DecidableEq J₂] in
/-- The claim on the row holds of early and late entries if and only if the block's first output
claim holds of the early ones. -/
theorem rowF_at (o : T.our.par.Out) (m : T.J → E) (u : J₂ → E) :
    (rowF (J₂ := J₂) T o).Holds (Sum.elim m u) ↔ T.our.par.UHolds o m := by
  unfold rowF
  rw [liftF_at]
  exact formU_holds T.our.par _ (fun _ _ b _ => b.elim) o m

/-- All claims of a sumcheck's ledger hold of early and late entries, if the block's first output
claim holds of the early ones and the claims on the end values of the list hold. -/
theorem plainCl_at (o : T.our.par.Out) (l : List T.A) (r : T.A → Aff E (T.J ⊕ J₂)) (m : T.J → E)
    (u : J₂ → E) (hU : T.our.par.UHolds o m)
    (hE : ∀ a ∈ l, (endF T o a (r a)).Holds (Sum.elim m u)) :
    ∀ f ∈ plainCl T o l r, f.Holds (Sum.elim m u) := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact (rowF_at T o m u).mpr hU
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
    exact hE a ha

end End

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.rdLong_congr
#print axioms Cb.Pv.Att.End.endF_at
#print axioms Cb.Pv.Att.End.plainCl_at
#print axioms Cb.Pv.Att.End.rdRow_at
#print axioms Cb.Pv.Att.End.rdCol_at
#print axioms Cb.Pv.Att.End.rdLong_at
