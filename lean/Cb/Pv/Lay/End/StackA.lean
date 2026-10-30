-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/StackA.lean: what the chain of a layers' sub-proof's own rounds owes at its end for
the batched sumcheck, as three claims of a ledger.

At its end the chain owes three of the output claims of the batched sumcheck, at the parameters of
Cb/Pv/Lay/At/Inner.lean: the first output row, and the rows on the end values of the two form parts,
the parts of the two sides that are forms in the cells. Each form part, at a point, is an affine
function of the entries, if the cells are read linearly off the entries. So each of the three claims
is a linear claim on the early entries.

Main names:
  `IsAff`: a function of the entries is affine. Its closure under sums, factors and tests.
  `a0_aff`, `b0_aff`: the two form parts at a point are affine in the entries.
  `affF`: an affine function as a form. `rowG`, `rowF`: the claim "map + mask * factor = shown
  value".
  `stackCl`, `stackLed`: the three claims, as forms on early and late entries, and as a ledger.
  `stack_pull`: if the pull-back of stackLed holds of the early entries, the three output claims
  hold.
Limits: the three claims are written on the early entries: they read no late entry. The programs'
claims on the two form parts read tables that are sent late. That these, pulled back to the early
entries, are the claims of this file is not said here. rd is asked to be linear in the entries.


-/
import Cb.Sub.Late
import Cb.Pv.Lay.End.NormsRows
import Cb.Pv.Lay.At.Inner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr Pan pans val valU xU ew)
open Blocks (Form)

/-! ### Affine functions of the entries -/

section Aff
variable {E J : Type} [Field E]

/-- g is an affine function of the entries. -/
def IsAff (g : (J → E) → E) : Prop :=
  ∀ (a b : E) (m m' : J → E),
    g (fun j => a * m j + b * m' j) = a * g m + b * g m' + (1 - a - b) * g 0

theorem IsAff.const (c : E) : IsAff fun _ : J → E => c := fun a b _ _ => by ring

theorem IsAff.add {g h : (J → E) → E} (hg : IsAff g) (hh : IsAff h) :
    IsAff fun m => g m + h m := fun a b m m' => by
  show g _ + h _ = _
  rw [hg a b m m', hh a b m m']
  ring

theorem IsAff.const_mul {g : (J → E) → E} (c : E) (hg : IsAff g) : IsAff fun m => c * g m :=
  fun a b m m' => by
    show c * g _ = _
    rw [hg a b m m']
    ring

theorem IsAff.sum {ι : Type} (s : Finset ι) {g : ι → (J → E) → E} (h : ∀ i, IsAff (g i)) :
    IsAff fun m => ∑ i ∈ s, g i m := fun a b m m' => by
  show ∑ i ∈ s, g i _ = _
  rw [sum_congr rfl fun i _ => h i a b m m', sum_add_distrib, sum_add_distrib, mul_sum, mul_sum,
    mul_sum]

theorem IsAff.listSum {ι : Type} (l : List ι) {g : ι → (J → E) → E} (h : ∀ i, IsAff (g i)) :
    IsAff fun m => (l.map fun i => g i m).sum := by
  induction l with
  | nil => exact IsAff.const 0
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i).add ih

theorem IsAff.ite (c : Prop) [Decidable c] {g : (J → E) → E} (hg : IsAff g) :
    IsAff fun m => if c then g m else 0 := by
  by_cases h : c
  · simp only [if_pos h]
    exact hg
  · simp only [if_neg h]
    exact IsAff.const 0

variable (rd : (J → E) → Cell → E)
  (hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
    rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c)

include hrd

theorem aff_cell (c : Cell) : IsAff fun m => rd m c := fun a b m m' => by
  have h0 : rd 0 c = 0 := by
    have h := hrd 0 0 0 0 c
    simp only [zero_mul, add_zero] at h
    exact h
  show rd _ c = a * rd m c + b * rd m' c + (1 - a - b) * rd 0 c
  rw [hrd, h0]
  ring

theorem aff_val (X : Arr) (i j p : ℕ) : IsAff fun m => val (rd m) X i j p :=
  (IsAff.sum _ fun _ => (aff_cell rd hrd _).const_mul _).add (IsAff.const _)

omit hrd in
theorem aff_ext (g : ℕ) (u : ℕ → E) {v : (J → E) → ℕ → E} (h : ∀ p, IsAff fun m => v m p) :
    IsAff fun m => Blocks.ext g (v m) u :=
  IsAff.sum _ fun p => (h p).const_mul _

theorem aff_valU (D : Dim) (X : Arr) (i j : ℕ) (u : ℕ → E) :
    IsAff fun m => valU D (rd m) X i j u :=
  aff_ext _ u fun p => aff_val rd hrd X i j p

theorem aff_xU (D : Dim) (s j : ℕ) (u : ℕ → E) : IsAff fun m => xU D (rd m) s j u :=
  aff_ext _ u fun p => aff_val rd hrd _ _ j p

end Aff

/-! ### An affine function as a form -/

section Gen
variable {E J J₂ : Type} [Field E] [Fintype J] [DecidableEq J] [DecidableEq J₂]

/-- A function of the early entries as a form on early and late entries: its value at 0, and at
entry j its value at the unit vector less that. -/
noncomputable def affF (g : (J → E) → E) : Form (J ⊕ J₂) E :=
  Form.const (g 0) + ∑ j, (g (fun i => if j = i then 1 else 0) - g 0) • Form.ent (.inl j)

theorem val_affF [Fintype J₂] {g : (J → E) → E} (hg : IsAff g) (m : J → E) (u : J₂ → E) :
    Form.val (Sum.elim m u) (affF (J₂ := J₂) g) = g m := by
  unfold affF
  rw [map_add, map_sum, Form.val_const, form_of_comb g hg m]
  congr 1
  exact sum_congr rfl fun j _ => by rw [map_smul, Form.val_ent, smul_eq_mul, Sum.elim_inl]

/-- The claim "g, plus β times entry j, is v". -/
noncomputable def rowG (g : (J → E) → E) (β v : E) (j : J) : Form (J ⊕ J₂) E :=
  affF g + β • Form.ent (.inl j) - Form.const v

theorem val_rowG [Fintype J₂] {g : (J → E) → E} (hg : IsAff g) (β v : E) (j : J) (m : J → E)
    (u : J₂ → E) :
    Form.val (Sum.elim m u) (rowG (J₂ := J₂) g β v j) = g m + β * m j - v := by
  unfold rowG
  rw [map_sub, map_add, map_smul, val_affF hg, Form.val_ent, Form.val_const, smul_eq_mul,
    Sum.elim_inl]

end Gen

/-! ### The two form parts -/

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : InnPar0 E)
  (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
    P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)

include hrd

/-- The first factor of an entry of a panel is affine in the entries, but on the panels D and Dr. -/
theorem A_aff (st : P.St) {p : Pan} (hv : isVirt p = false) (ρ ι : ℕ) :
    IsAff fun m => p.A P.D (P.rP st m p) ρ ι := by
  cases p with
  | G => exact aff_valU P.rd hrd P.D .m ρ ι _
  | U => exact aff_valU P.rd hrd P.D .m ρ ι _
  | V => exact aff_valU P.rd hrd P.D .a ρ ι _
  | O => exact aff_valU P.rd hrd P.D .o ρ ι _
  | LR => exact aff_valU P.rd hrd P.D .m (2 * ρ + 1) ι _
  | QK => exact aff_valU P.rd hrd P.D .a ρ ι _
  | N1 => exact IsAff.const _
  | N2 => exact IsAff.const _
  | XR => exact IsAff.const _
  | DD => exact IsAff.const _
  | MR => exact IsAff.const _
  | Gr l' => exact (aff_valU P.rd hrd P.D .xr l' ι _).const_mul _
  | Ur l' => exact (aff_valU P.rd hrd P.D .xr l' ι _).const_mul _
  | D => cases hv
  | Dr l' => cases hv

/-- The second factor of an entry of a panel without weights is affine in the entries. -/
theorem B_aff (st : P.St) {p : Pan} (hw : p.weight = false) (ρ ι : ℕ) :
    IsAff fun m => P.FB st m p ρ ι := by
  cases p with
  | N1 =>
    show IsAff fun m => ∑ x ∈ range P.D.d,
      ew P.D st.o3.st (if 2 * ρ % 2 = 0 then .N1 else .N2) x * xU P.D (P.rd m) (2 * ρ) x (P.rt st)
    exact IsAff.sum _ fun x => (aff_xU P.rd hrd P.D _ x _).const_mul _
  | N2 =>
    show IsAff fun m => ∑ x ∈ range P.D.d,
      ew P.D st.o3.st (if (2 * ρ + 1) % 2 = 0 then .N1 else .N2) x *
        xU P.D (P.rd m) (2 * ρ + 1) x (P.rt st)
    exact IsAff.sum _ fun x => (aff_xU P.rd hrd P.D _ x _).const_mul _
  | XR =>
    show IsAff fun m => ∑ x ∈ range P.D.d,
      ew P.D st.o3.st .XR x * valU P.D (P.rd m) .m (2 * ρ + 1) x (P.rt st)
    exact IsAff.sum _ fun x => (aff_valU P.rd hrd P.D .m _ x _).const_mul _
  | DD => exact aff_valU P.rd hrd P.D .lr ρ ι _
  | MR => exact aff_valU P.rd hrd P.D .lr ρ ι _
  | _ => cases hw

omit hrd in
/-- A panel's block of a vector of entries that are affine. -/
theorem onP_aff {F : (P.J → E) → ℕ → ℕ → E} (p : Pan) (h : ∀ ρ ι, IsAff fun m => F m ρ ι)
    (y : ℕ) : IsAff fun m => blk (p.wid P.D) (nP P.D p) (cellOf P.D p (F m)) y :=
  IsAff.ite _ (IsAff.ite _ (h _ _))

/-- The form part of the first side, at a point, is affine in the entries. -/
theorem a0_aff (st : P.St) (z : Fin (kS P.D) → E) :
    IsAff fun m => P.inn.F st m (.inl (.inl ())) z := by
  show IsAff fun m => ∑ y ∈ range (2 ^ kS P.D),
    Blocks.eqN (kS P.D) (kS P.D - kS P.D) (Blocks.nat z) y *
      ((pans P.D).map fun p => if isVirt p then 0 else P.onP (P.VA st m) p y).sum
  refine IsAff.sum _ fun y => IsAff.const_mul _ (IsAff.listSum _ fun p => ?_)
  by_cases hv : isVirt p = true
  · simp only [if_pos hv]
    exact IsAff.const 0
  · simp only [if_neg hv]
    have hv' : isVirt p = false := by simpa using hv
    have e : ∀ m, P.onP (P.VA st m) p y =
        blk (p.wid P.D) (nP P.D p) (cellOf P.D p (P.FA st m p)) y := fun m => by
      unfold InnPar0.onP InnPar0.VA
      rw [if_neg hv]
    simp only [e]
    exact onP_aff P p (fun ρ ι => (A_aff P hrd st hv' ρ ι).const_mul _) y

/-- The form part of the second side, at a point, is affine in the entries. -/
theorem b0_aff (st : P.St) (z : Fin (kS P.D) → E) :
    IsAff fun m => P.inn.F st m (.inr (.inl ())) z := by
  show IsAff fun m => ∑ y ∈ range (2 ^ kS P.D),
    Blocks.eqN (kS P.D) (kS P.D - kS P.D) (Blocks.nat z) y *
      ((pans P.D).map fun p => if p.weight then 0 else P.onP (P.VB st m) p y).sum
  refine IsAff.sum _ fun y => IsAff.const_mul _ (IsAff.listSum _ fun p => ?_)
  by_cases hw : p.weight = true
  · simp only [if_pos hw]
    exact IsAff.const 0
  · simp only [if_neg hw]
    have hw' : p.weight = false := by simpa using hw
    exact onP_aff P p (fun ρ ι => (B_aff P hrd st hw' ρ ι).const_mul _) y

omit hrd

/-! ### The claims -/

section Claims
variable {J₂ : Type} [DecidableEq P.J] [DecidableEq J₂]

/-- The claim "the map at the last point, plus the mask entry times the factor, is the value that
was shown". -/
noncomputable def rowF (o : P.inn.toSum.T.par.Out) (a : IA P.D ⊕ IB P.D) :
    Form (P.J ⊕ J₂) E :=
  rowG (fun m => P.inn.F o.st m a (P.inn.Kp.outPt P.inn.Mk o)) (P.inn.Kp.outB P.inn.Mk o)
    (o.vals a) (P.cI a)

/-- The three claims. -/
noncomputable def stackCl (o : P.inn.toSum.T.par.Out) : List (Form (P.J ⊕ J₂) E) :=
  [upForm (Cb.Sub.formU P.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b) o),
    rowF P o (.inl (.inl ())), rowF P o (.inr (.inl ()))]

/-- The three claims as a ledger. -/
noncomputable def stackLed (o : P.inn.toSum.T.par.Out) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (stackCl P o)

variable [Fintype J₂]

/-- What the claim rowF says, for a map that is affine in the entries. -/
theorem rowF_iff (o : P.inn.toSum.T.par.Out) (a : IA P.D ⊕ IB P.D)
    (ha : IsAff fun m => P.inn.F o.st m a (P.inn.Kp.outPt P.inn.Mk o)) (m : P.J → E)
    (u : J₂ → E) :
    Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o a) = 0 ↔ P.inn.toSum.T.par.EHolds o m a := by
  have e : Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o a) =
      P.inn.F o.st m a (P.inn.Kp.outPt P.inn.Mk o) + P.inn.Kp.outB P.inn.Mk o * m (P.cI a) -
        o.vals a := val_rowG (J := P.J) ha _ _ _ m u
  have hev : P.inn.toSum.T.par.EHolds o m a ↔
      P.inn.F o.st m a (P.inn.Kp.outPt P.inn.Mk o) + m (P.cI a) * P.inn.Kp.outB P.inn.Mk o =
        o.vals a := P.inn.ev_iff o m a
  rw [e]
  refine Iff.trans ?_ hev.symm
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

include hrd in
/-- The three output claims that the chain owes at its end for the batched sumcheck, from the
pull-back of the ledger of the three claims to the early entries. -/
theorem stack_pull (a : J₂ → TWhole.Aff E P.J) (o : P.inn.toSum.T.par.Out) (m : P.J → E)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL a (stackLed P o)) m) :
    P.inn.toSum.T.par.UHolds o m ∧ P.inn.toSum.T.par.EHolds o m (.inl (.inl ())) ∧
      P.inn.toSum.T.par.EHolds o m (.inr (.inl ())) := by
  have k := (ledOf_holds _ _).1 ((Cb.Sub.pullL_holds _ _ _).1 h)
  refine ⟨?_, ?_, ?_⟩
  · have k1 := k _ (List.mem_cons_self)
    rw [val_upForm] at k1
    exact (Cb.Sub.formU_holds _ _ (fun _ _ b _ => PEmpty.elim b) o m).1 k1
  · exact (rowF_iff P o _ (a0_aff P hrd o.st _) m _).1
      (k _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact (rowF_iff P o _ (b0_aff P hrd o.st _) m _).1
      (k _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

end Claims

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.stack_pull
