-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/BitsSc3.lean: the sumcheck for the bits of the index, with any number of variables that
number a bit, as parameters of the sumcheck of products.

Cb/Pv/Att/Steps.lean fills the record Sc3 (Cb/Pv/Att/Sc3.lean) with the seven steps of the library's
description of an attention segment. The last of them, step s21, has as many variables for the
number of a bit as the number of bits of a position needs. The programs bind 4 variables at every
size. This file fills the record with the same sumcheck for a free number kap of such variables
(Cb/Pv/Att/Bits.lean), so that the statements of Cb/Pv/Att/Sc3.lean hold of the sumcheck that the
programs run.

Main names:
  bitsSc3 kap D rd inc wAt cAt: the parameters. The public states are the challenges (AttSeg.Pub);
  rd says how the cells' content is read off the entries; the maps are the multilinear extensions of
    bitCube and of bitCube minus 1; the weight is the multilinear extension of bitWt's values on the
    hypercube; the incoming form and the entries that serve as masks stay parameters.
  bitsSc3_lK: with the library's number of variables the parameters are those of step s21.
  bits_sum: the sum claim says: bitSum plus the incoming form is the target.
  bits_knowAt: the block with n further scalars in its first message has knowledge soundness
    (KnowAt), for all sizes.
  bits_nums: its errors: 1, then 3 for each of the variables, then 2, then 0.

Limits. The limits of Cb/Pv/Att/Sc3.lean hold here too. The weight is replaced by the extension of
its values on the hypercube; on the hypercube, where the sum is taken, the two agree; off the
hypercube nothing is said of the two here. Nothing is said on an honest prover or on hiding.


-/
import Cb.Pv.Att.Steps
import Cb.Pv.Att.Bits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole
open Inst.Model.AttSeg (Dim Pub Raw)

variable {E : Type} [Field E] [Fintype E] (kap : ℕ) (D : Dim) {J : Type} [Fintype J]
  (rd : (J → E) → Raw → E) (inc : Pub E → J → E)
  (wAt : PIdx (ldPartFmt E (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy E 2]) → J)
  (cAt : Fin D.nb × Bool → J)

/-- The parameters of the sumcheck for the bits, with kap variables for the number of a bit. -/
noncomputable def bitsSc3 : Sc3 E where
  nv := D.lT + D.lg + kap
  nb := D.nb
  St := Pub E
  J := J
  W := fun p b z =>
    Blocks.ext (D.lT + D.lg + kap)
      (fun X => bitWt kap D p b.val (Blocks.cubePt (D.lT + D.lg + kap) X)) (Blocks.nat z)
  map := fun _ m a z =>
    if a.2 then
      Blocks.ext (D.lT + D.lg + kap) (fun X => bitCube kap D (rd m) a.1.val X - 1) (Blocks.nat z)
    else Blocks.ext (D.lT + D.lg + kap) (bitCube kap D (rd m) a.1.val) (Blocks.nat z)
  inc := inc
  wAt := wAt
  cAt := cAt
  degW := fun _ _ => ldPart_ext_deg _ _
  degM := fun _ m a => by
    show Alg.DegLE (fun _ => 1) fun z : Fin (D.lT + D.lg + kap) → E =>
      if a.2 then
        Blocks.ext (D.lT + D.lg + kap) (fun X => bitCube kap D (rd m) a.1.val X - 1)
          (Blocks.nat z)
      else Blocks.ext (D.lT + D.lg + kap) (bitCube kap D (rd m) a.1.val) (Blocks.nat z)
    cases a.2
    · exact ldPart_ext_deg _ _
    · exact ldPart_ext_deg _ _

/-- With the library's number of variables for the number of a bit, the parameters are those of the
library's step s21. -/
theorem bitsSc3_lK (C : Inst.Model.AttSeg.Calls)
    (wAt' : PIdx (ldPartFmt E (D.lT + D.lg + D.lK) (fun _ => 3) ++ [pDummy E 2]) → J) :
    bitsSc3 D.lK D rd inc wAt' cAt = stepSc3 D C rd .s21 inc wAt' cAt := rfl

/-- What the sum claim says. -/
theorem bits_sum (x : E × Pub E) (m : J → E) :
    (bitsSc3 kap D rd inc wAt cAt).plain.our.par.SumHolds x m ↔
      bitSum kap D x.2 (rd m) + ∑ j, inc x.2 j * m j = x.1 := by
  rw [sc3_sum]
  have e : ∑ c : Fin (D.lT + D.lg + kap) → Bool, ∑ b : Fin D.nb,
        (bitsSc3 kap D rd inc wAt cAt).W x.2 b (Alg.corner c) *
          (bitsSc3 kap D rd inc wAt cAt).map x.2 m (b, false) (Alg.corner c) *
          (bitsSc3 kap D rd inc wAt cAt).map x.2 m (b, true) (Alg.corner c) =
      bitSum kap D x.2 (rd m) := by
    unfold bitSum
    rw [← Alg.sum_num fun X => ∑ b ∈ Finset.range D.nb,
      bitWt kap D x.2 b (Blocks.cubePt (D.lT + D.lg + kap) X) * bitCube kap D (rd m) b X *
        (bitCube kap D (rd m) b X - 1)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hc : Blocks.nat (Alg.corner c : Fin (D.lT + D.lg + kap) → E) =
        Blocks.cubePt (D.lT + D.lg + kap) (Alg.num c) := by
      unfold Blocks.cubePt
      rw [Alg.bits_num]
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    show Blocks.ext (D.lT + D.lg + kap)
          (fun X => bitWt kap D x.2 b.val (Blocks.cubePt (D.lT + D.lg + kap) X))
          (Blocks.nat (Alg.corner c)) *
        Blocks.ext (D.lT + D.lg + kap) (bitCube kap D (rd m) b.val) (Blocks.nat (Alg.corner c)) *
        Blocks.ext (D.lT + D.lg + kap) (fun X => bitCube kap D (rd m) b.val X - 1)
          (Blocks.nat (Alg.corner c)) = _
    rw [hc, Blocks.ext_cubePt _ _ (Alg.num_lt c), Blocks.ext_cubePt _ _ (Alg.num_lt c),
      Blocks.ext_cubePt _ _ (Alg.num_lt c)]
  exact Iff.of_eq (congrArg (fun t => t + ∑ j, inc x.2 j * m j = x.1) e)

section Block
variable (F : ∀ st, HFixs ((bitsSc3 kap D rd inc wAt cAt).plain.our.par.vars st)) (n : ℕ)
  {X : Type} (cl : X → (Fin n → E) → E × Pub E) (Ex : ExtSpec) {M Wp Kc : Type}
  (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → J → E) (Θ : X → (Fin n → E) → (J → E) → Prop)

/-- Knowledge soundness of the block. -/
theorem bits_knowAt :
    KnowAt (rideNR (bitsSc3 kap D rd inc wAt cAt).plain.our.par n F cl Ex)
      (rideNIn (bitsSc3 kap D rd inc wAt cAt).plain.our.par n cl Ex A0 msg Θ)
      (rideNOut (bitsSc3 kap D rd inc wAt cAt).plain.our.par n Ex A0 msg Θ) (fun _ _ _ wp => wp)
      (rideNE (bitsSc3 kap D rd inc wAt cAt).plain.our.par n Ex) :=
  sc3_knowAt (bitsSc3 kap D rd inc wAt cAt) F n cl Ex A0 msg Θ

/-- Its errors. -/
theorem bits_nums :
    errList (rideNE (bitsSc3 kap D rd inc wAt cAt).plain.our.par n Ex) =
      1 :: (List.replicate (D.lT + D.lg + kap) 3 ++ [2] ++ [0]) :=
  sc3_nums (bitsSc3 kap D rd inc wAt cAt) n Ex

end Block

end Cb.Pv.Att

#print axioms Cb.Pv.Att.bitsSc3_lK
#print axioms Cb.Pv.Att.bits_sum
#print axioms Cb.Pv.Att.bits_knowAt
#print axioms Cb.Pv.Att.bits_nums
