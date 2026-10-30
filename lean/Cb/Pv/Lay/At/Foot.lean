-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Foot.lean: the records of the two product layers of the gated products of a layers'
sub-proof, at the library's description of a feed-forward segment.

Cb/Pv/Lay/Prod.lean and Cb/Pv/Lay/Routed.lean state the two stretches at letters. This file fills
the letters from Inst/Model/FF/Objects.lean: the first layer's two maps are slV and upV, the
second's slV' and upV'. The claims from which the stretches start are rows on end values of the
sumcheck before them: the extension of a vector of gated products at a point, plus a mask entry
times a factor, is a value that was shown.

Main names.
  FootPar0: what stays free: the sizes, the entries and how they are read as cells, the orders in
    which the variables are bound, the places of the mask entries.
  St5, St6: what the two stretches read of the statement before them: the coordinates of the earlier
    sumcheck's output point that belong to the vector, a token point, the factor of the masks, and
    what was shown.
  FootPar0.gp, FootPar0.rt: the two records.
  FootPar0.gp_sg: the first layer's input claim says: the extension of Hh1t at the point, plus the
    mask entry times the factor, is what was shown.
  FootPar0.rt_val: the value of claim i of the second stretch is the extension of the gated products
    of the routed hidden units of layer 2 i + 1, plus the mask entry times the factor.

Limits. That the programs' maps, points and masks are these is not said. Nothing on an honest
prover, on completeness or on hiding.


-/
import Cb.Pv.Lay.Routed
import Cb.Pv.Lay.End.GatedCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole
open Inst.Model.FFSeg (Dim Cell hh hhU Hh1t slV upV slV' upV' lF lFe)
open Cb.Pv.Lay.End (div_mod_at)
open Cb.Pv.Lay.End.Gated (first_sum ext_nest)

noncomputable section

/-! ### Small tools -/

section Tools
variable {E : Type} [Field E]

/-- The extension reads the first g coordinates of its point alone. -/
theorem ext_pt {g : ℕ} {z z' : ℕ → E} (h : ∀ j, j < g → z j = z' j) (f : ℕ → E) :
    Blocks.ext g f z = Blocks.ext g f z' := by
  unfold Blocks.ext
  exact sum_congr rfl fun X _ => by
    rw [eqN_congr' (off := 0) (off' := 0) (a := z) (a' := z')
      (fun t ht => by rw [Nat.zero_add]; exact h t ht) X]

/-- One routed layer's block of the second layer's summand: its extension is the extension of the
layer's gated products. -/
theorem routed_block (D : Dim) (t : Cell → E) (i : ℕ) (p : ℕ → E) :
    Blocks.ext (lFe D + D.lT)
        (fun x => slV' D t (i * 2 ^ (lFe D + D.lT) + x) * upV' D t (i * 2 ^ (lFe D + D.lT) + x)) p =
      Blocks.ext (lFe D) (fun j => hhU D t (2 * i + 1) (D.fe + j) fun a => p (lFe D + a)) p := by
  have hT : D.T = 2 ^ D.lT := rfl
  rw [ext_nest]
  refine Blocks.ext_congr (fun j hj => ?_) _
  unfold Inst.Model.FFSeg.hhU
  refine Blocks.ext_congr (fun y hy => ?_) _
  have e0 : i * 2 ^ (lFe D + D.lT) + (j * 2 ^ D.lT + y) = (i * 2 ^ lFe D + j) * 2 ^ D.lT + y := by
    rw [pow_add]
    ring
  obtain ⟨e1, e2⟩ := div_mod_at (i * 2 ^ lFe D + j) y (2 ^ D.lT) hy
  obtain ⟨e3, e4⟩ := div_mod_at i j (2 ^ lFe D) hj
  unfold Inst.Model.FFSeg.slV' Inst.Model.FFSeg.upV' Inst.Model.FFSeg.hh
  rw [e0, hT, e1, e2, e3, e4]
  ring

end Tools

/-! ### What stays free -/

/-- The letters of the two stretches that stay free. -/
structure FootPar0 (E : Type) [Field E] [Fintype E] where
  /-- the sizes -/
  D : Dim
  /-- the entries; how they are read as cells -/
  J : Type
  [finJ : Fintype J]
  rd : (J → E) → Cell → E
  /-- the orders in which the variables are bound -/
  e5 : Fin (D.lL + lF D + D.lT) ≃ Fin (D.lL + lF D + D.lT)
  e6 : Fin (D.lL - 1 + (lFe D + D.lT)) ≃ Fin (D.lL - 1 + (lFe D + D.lT))
  /-- the mask entries of the values from which the stretches start -/
  nH1 : J
  nH2 : Fin D.ne → J
  /-- the two sumchecks' own masks -/
  w5 : PIdx (ldPartFmt E (D.lL + lF D + D.lT) (fun _ => 2) ++ [pDummy E 2]) → J
  c5 : Bool → J
  w6 : PIdx (ldPartFmt E (D.lL - 1 + (lFe D + D.lT)) (fun _ => 2) ++ [pDummy E 2]) → J
  c6 : Bool → J

attribute [instance] FootPar0.finJ

/-- What the first stretch reads of the statement before it. -/
structure St5 (E : Type) (D : Dim) where
  /-- the coordinates of the layers and hidden units; the token point -/
  pt : Fin (D.lL + lF D) → E
  zt : Fin D.lT → E
  /-- the factor of the mask; what was shown -/
  be : E
  v : E

/-- What the second stretch reads of the statement before it. -/
structure St6 (E : Type) (D : Dim) where
  /-- the coordinates of an expert's hidden units; the token point -/
  pt : Fin (lFe D) → E
  rt : Fin D.lT → E
  /-- the factor of the masks; what was shown -/
  be : E
  v : Fin D.ne → E

variable {E : Type} [Field E] [Fintype E]

namespace FootPar0
variable (P : FootPar0 E)

/-! ### The gated products -/

open Classical in
/-- The first product layer, at the value. -/
def gp : ProdL E where
  J := P.J
  k := P.D.lL + lF P.D + P.D.lT
  e := P.e5
  St := St5 E P.D
  vm := fun _ m b => bif b then upV P.D (P.rd m) else slV P.D (P.rd m)
  pnt := fun st => Fin.append st.pt st.zt
  inc := fun st j => if j = P.nH1 then st.be else 0
  tg := fun st => st.v
  wAt := P.w5
  cAt := P.c5
  Rd := fun _ _ => True

/-- What the first layer's input claim says. -/
theorem gp_sg (st : St5 E P.D) (m : P.J → E) :
    P.gp.Sg st m ↔
      Blocks.ext (P.D.lL + lF P.D) (Hh1t P.D (P.rd m) (Blocks.nat st.zt)) (Blocks.nat st.pt) +
        m P.nH1 * st.be = st.v := by
  classical
  have hs : ∑ j, P.gp.inc st j * m j = m P.nH1 * st.be := by
    show ∑ j, (if j = P.nH1 then st.be else 0) * m j = _
    rw [Finset.sum_eq_single P.nH1]
    · rw [if_pos rfl]
      ring
    · intro j _ hj
      rw [if_neg hj, zero_mul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  have he : Blocks.ext P.gp.k (fun X => P.gp.vm st m false X * P.gp.vm st m true X)
      (Blocks.nat (P.gp.pnt st)) =
      Blocks.ext (P.D.lL + lF P.D) (Hh1t P.D (P.rd m) (Blocks.nat st.zt)) (Blocks.nat st.pt) := by
    show Blocks.ext (P.D.lL + lF P.D + P.D.lT)
      (fun X => slV P.D (P.rd m) X * upV P.D (P.rd m) X)
      (Blocks.nat (Fin.append st.pt st.zt)) = _
    rw [first_sum, ext_pt (fun j hj => nat_append_left _ _ st.pt st.zt j hj)]
    refine Blocks.ext_congr (fun Y _ => ?_) _
    unfold Inst.Model.FFSeg.Hh1t Inst.Model.FFSeg.hhU
    exact ext_pt (fun j hj => nat_append_right _ _ st.pt st.zt j hj) _
  unfold ProdL.Sg
  rw [hs, he]
  rfl

/-! ### The routed experts' gated products -/

open Classical in
/-- The second stretch, at the value. -/
def rt : RoutedL E where
  J := P.J
  g := P.D.lL - 1
  k' := lFe P.D + P.D.lT
  n := P.D.ne
  hn := by
    show 2 ^ P.D.lL / 2 ≤ 2 ^ (P.D.lL - 1)
    refine Nat.div_le_of_le_mul ?_
    calc 2 ^ P.D.lL ≤ 2 ^ (P.D.lL - 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ (P.D.lL - 1) := by rw [pow_succ, Nat.mul_comm]
  e := P.e6
  St := St6 E P.D
  vm := fun _ m b => bif b then upV' P.D (P.rd m) else slV' P.D (P.rd m)
  pnt := fun st => Fin.append st.pt st.rt
  inci := fun i st j => if j = P.nH2 i then st.be else 0
  sh := fun i st => st.v i
  wAt := P.w6
  cAt := P.c6
  Rd := fun _ _ => True

/-- The value of claim i of the second stretch. -/
theorem rt_val (st : St6 E P.D) (m : P.J → E) (i : Fin P.D.ne) :
    P.rt.val st m i =
      Blocks.ext (lFe P.D)
          (fun j => hhU P.D (P.rd m) (2 * i.val + 1) (P.D.fe + j) (Blocks.nat st.rt))
          (Blocks.nat st.pt) + m (P.nH2 i) * st.be := by
  classical
  have hs : ∑ j, P.rt.inci i st j * m j = m (P.nH2 i) * st.be := by
    show ∑ j, (if j = P.nH2 i then st.be else 0) * m j = _
    rw [Finset.sum_eq_single (P.nH2 i)]
    · rw [if_pos rfl]
      ring
    · intro j _ hj
      rw [if_neg hj, zero_mul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  unfold RoutedL.val
  rw [hs]
  congr 1
  show Blocks.ext (lFe P.D + P.D.lT)
    (fun x => slV' P.D (P.rd m) (i.val * 2 ^ (lFe P.D + P.D.lT) + x) *
      upV' P.D (P.rd m) (i.val * 2 ^ (lFe P.D + P.D.lT) + x))
    (Blocks.nat (Fin.append st.pt st.rt)) = _
  rw [routed_block, ext_pt (fun j hj => nat_append_left _ _ st.pt st.rt j hj)]
  refine Blocks.ext_congr (fun j _ => ?_) _
  unfold Inst.Model.FFSeg.hhU
  exact ext_pt (fun a ha => nat_append_right _ _ st.pt st.rt a ha) _

end FootPar0

end

end Cb.Pv.Lay.At
