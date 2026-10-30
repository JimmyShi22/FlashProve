-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/Steps.lean: the seven batched sumchecks of an attention segment, as the library's own
description has them (Inst/Model/Att/Sums.lean), as parameters of the sumcheck of products.

Inst/Model/Att/Sums.lean defines, for each of seven steps s, a number of variables s.g D, vectors
A_b and B_b on the hypercube (functions of the cells' content and of the challenges), and a public
weight W_b; the summand is the sum over b of W_b times the extensions of A_b and B_b. This file
fills the record Sc3 (Cb/Pv/Att/Sc3.lean) with them, so that the statements of that file hold of
each step.

Main names:
  stepSc3 D C rd s inc wAt cAt: the parameters of step s. The public states are the challenges
    (AttSeg.Pub); rd says how the cells' content is read off the entries; the maps are the
    multilinear extensions of A_b and B_b; the weight is the multilinear extension of W_b's values
    on the hypercube; the incoming form and the entries that serve as masks stay parameters.
  step_sum: the sum claim of step s says: the description's own sum (AttSeg.sumPhi) plus the
    incoming form is the target.
  step_knowAt: the block with n further scalars in its first message has knowledge soundness
    (KnowAt), at every step, for all sizes.
  step_nums: its errors: 1, then 3 for each of the s.g D variables, then 2, then 0.

Limits. The limits of Cb/Pv/Att/Sc3.lean hold here too. That the programs' sumchecks are these
seven steps is not stated: the description's steps are taken as they are defined. The weight is
replaced by the extension of its values on the hypercube; on the hypercube, where the sum is
taken, the two agree (used in step_sum); off the hypercube nothing is said of the two. The eighth
sumcheck of the description (its step 18) is not treated here. Nothing is said on an honest prover
or on hiding.
-/
import Cb.Pv.Att.Sc3
import Inst.Model.Att.Sums
import Cb.Part.LdPartPscFamProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Inst.Model

variable {E : Type} [Field E] [Fintype E] (D : AttSeg.Dim) (C : AttSeg.Calls) {J : Type} [Fintype J]
  (rd : (J → E) → AttSeg.Raw → E) (s : AttSeg.Step) (inc : AttSeg.Pub E → J → E)
  (wAt : PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J) (cAt : Fin D.nb × Bool → J)

/-- The parameters of step s. -/
noncomputable def stepSc3 : Sc3 E where
  nv := s.g D
  nb := D.nb
  St := AttSeg.Pub E
  J := J
  W := fun p b z =>
    Blocks.ext (s.g D) (fun X => AttSeg.Wb D C p s b.val (Blocks.cubePt (s.g D) X)) (Blocks.nat z)
  map := fun p m a z =>
    if a.2 then Blocks.ext (s.g D) (AttSeg.Bcube D C p (rd m) s a.1.val) (Blocks.nat z)
    else Blocks.ext (s.g D) (AttSeg.Acube D C p (rd m) s a.1.val) (Blocks.nat z)
  inc := inc
  wAt := wAt
  cAt := cAt
  degW := fun _ _ => ldPart_ext_deg _ _
  degM := fun p m a => by
    show Alg.DegLE (fun _ => 1) fun z : Fin (s.g D) → E =>
      if a.2 then Blocks.ext (s.g D) (AttSeg.Bcube D C p (rd m) s a.1.val) (Blocks.nat z)
      else Blocks.ext (s.g D) (AttSeg.Acube D C p (rd m) s a.1.val) (Blocks.nat z)
    cases a.2
    · exact ldPart_ext_deg _ _
    · exact ldPart_ext_deg _ _

/-- The summand at a corner of the cube is the description's summand at that vertex. -/
theorem step_corner (p : AttSeg.Pub E) (m : J → E) (c : Fin (s.g D) → Bool) :
    ∑ b : Fin D.nb, (stepSc3 D C rd s inc wAt cAt).W p b (Alg.corner c) *
        (stepSc3 D C rd s inc wAt cAt).map p m (b, false) (Alg.corner c) *
        (stepSc3 D C rd s inc wAt cAt).map p m (b, true) (Alg.corner c) =
      AttSeg.Phi D C p (rd m) s (Blocks.cubePt (s.g D) (Alg.num c)) := by
  have hc : Blocks.nat (Alg.corner c : Fin (s.g D) → E) = Blocks.cubePt (s.g D) (Alg.num c) := by
    unfold Blocks.cubePt
    rw [Alg.bits_num]
  unfold AttSeg.Phi
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  show Blocks.ext (s.g D) (fun X => AttSeg.Wb D C p s b.val (Blocks.cubePt (s.g D) X))
        (Blocks.nat (Alg.corner c)) *
      Blocks.ext (s.g D) (AttSeg.Acube D C p (rd m) s b.val) (Blocks.nat (Alg.corner c)) *
      Blocks.ext (s.g D) (AttSeg.Bcube D C p (rd m) s b.val) (Blocks.nat (Alg.corner c)) = _
  rw [hc, Blocks.ext_cubePt _ _ (Alg.num_lt c)]
  rfl

/-- What the sum claim of step s says. -/
theorem step_sum (x : E × AttSeg.Pub E) (m : J → E) :
    (stepSc3 D C rd s inc wAt cAt).plain.our.par.SumHolds x m ↔
      AttSeg.sumPhi D C x.2 (rd m) s + ∑ j, inc x.2 j * m j = x.1 := by
  rw [sc3_sum]
  have e : ∑ c : Fin (s.g D) → Bool, ∑ b : Fin D.nb,
        (stepSc3 D C rd s inc wAt cAt).W x.2 b (Alg.corner c) *
          (stepSc3 D C rd s inc wAt cAt).map x.2 m (b, false) (Alg.corner c) *
          (stepSc3 D C rd s inc wAt cAt).map x.2 m (b, true) (Alg.corner c) =
      AttSeg.sumPhi D C x.2 (rd m) s := by
    rw [Finset.sum_congr rfl fun c _ => step_corner D C rd s inc wAt cAt x.2 m c]
    exact Alg.sum_num fun X => AttSeg.Phi D C x.2 (rd m) s (Blocks.cubePt (s.g D) X)
  exact Iff.of_eq (congrArg (fun t => t + ∑ j, inc x.2 j * m j = x.1) e)

section Block
variable (F : ∀ st, HFixs ((stepSc3 D C rd s inc wAt cAt).plain.our.par.vars st)) (n : ℕ) {X : Type}
  (cl : X → (Fin n → E) → E × AttSeg.Pub E) (Ex : ExtSpec) {M Wp Kc : Type}
  (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → J → E) (Θ : X → (Fin n → E) → (J → E) → Prop)

/-- Knowledge soundness of the block of step s. -/
theorem step_knowAt :
    KnowAt (rideNR (stepSc3 D C rd s inc wAt cAt).plain.our.par n F cl Ex)
      (rideNIn (stepSc3 D C rd s inc wAt cAt).plain.our.par n cl Ex A0 msg Θ)
      (rideNOut (stepSc3 D C rd s inc wAt cAt).plain.our.par n Ex A0 msg Θ) (fun _ _ _ wp => wp)
      (rideNE (stepSc3 D C rd s inc wAt cAt).plain.our.par n Ex) :=
  sc3_knowAt (stepSc3 D C rd s inc wAt cAt) F n cl Ex A0 msg Θ

/-- Its errors. -/
theorem step_nums :
    errList (rideNE (stepSc3 D C rd s inc wAt cAt).plain.our.par n Ex) =
      1 :: (List.replicate (s.g D) 3 ++ [2] ++ [0]) :=
  sc3_nums (stepSc3 D C rd s inc wAt cAt) n Ex

end Block

end Cb.Pv.Att

#print axioms Cb.Pv.Att.step_sum
#print axioms Cb.Pv.Att.step_knowAt
#print axioms Cb.Pv.Att.step_nums
