-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Weights4.lean: the law of kind K5 at the library's letters: the weights of
the value
product below the diagonal (Att/K5LeftAll.lean: wBelow, through the tiles' sums), read as the
library's weight
polynomial Wb … .s11 at the output's point, where the kind's record of numbers is geoOf S and the
description's sizes are L5.dimOf S, S a shape with the library's equations Sizes S; under LookPts.

Main names:
  `tileSums_geo`, `overTileRows_geo`: the kind's two functions, at geoOf S, are the library's over
    S, by
    unfolding.
  `below_weight`, `below_hW`.

Sources: OnBytes/Model/AttentionHeard.lean (tileSums); AttentionDivide.lean (overTileRows);
Johnson/Road/Rows/AttRows14.lean (weightBelow); AttReadLong.lean (Sizes); AttWb14.lean (wbExt11);
Johnson/Road/Lane5AttDef.lean (L5.dimOf).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GeoOf
import Johnson.Desc.First.Att.K05Weights2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH)
open OnBytes.Attention (PW timesW)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

theorem tileSums_geo (S : Attention.Shape) (eP es : Array E) : tileSums (geoOf S) eP es = Attention.tileSums S eP es := rfl

theorem overTileRows_geo (S : Attention.Shape) (wI eI : Array E) :
    overTileRows (geoOf S) wI eI = Attention.overTileRows S wI eI := rfl

omit [Fintype K] in
/-- K5's weights of the value product below the diagonal read as the library's weight. -/
theorem below_weight (S : Attention.Shape) (Z : OnBytes.Road.Rows.Sizes S) (C : AttSeg.Calls) (p : AttSeg.Pub K) (h : Heard)
    {pw zW : Array E} (lp : LookPts ρ (OnBytes.Road.L5.dimOf S) C p.z pw zW)
    (hlt : S.cf.lt = (OnBytes.Road.L5.dimOf S).lT) (hr : S.cf.lgk + (S.lnT - 1) + S.lnT ≤ (chal h.below).size) {b : ℕ} (hb : b < (OnBytes.Road.L5.dimOf S).nb) :
    ρ.val ((wBelow (geoOf S) pw zW h).getD b zeroE) =
      AttSeg.Wb (OnBytes.Road.L5.dimOf S) C p .s11 b fun j => ρ.val ((chal h.below).getD j zeroE) := by
  have hbs : b < (asPW pw).size := by
    unfold asPW
    rw [Array.size_map, lp.nPw]
    exact hb
  have hn : 1 + S.cf.lgk + (OnBytes.Road.L5.dimOf S).lT ≤ zW.size := lp.nZ
  have hl := Z.lnT
  have hT : (OnBytes.Road.L5.dimOf S).lT = S.lnT - 1 + 1 + S.cf.lB := rfl
  have := OnBytes.Road.Rows.weightBelow ρ C p Z (pwW := asPW pw) (zgW := zW.extract 1 (1 + S.cf.lgk))
    (zihi := (zW.extract (1 + S.cf.lgk) (1 + S.cf.lgk + S.cf.lt)).extract 0 S.lnT) (r := chal h.below) hbs
    (by simp only [Array.size_extract]; omega) ?_ hr
    (by rw [asPW_wp pw b (by rw [lp.nPw]; exact hb)]; exact lp.hw b hb)
    (fun k hk => by
      show ρ.val ((zW.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact lp.hg k hk)
    (fun k hk => ?_)
  · rw [timesW_asPW] at this
    exact this
  · simp only [Array.size_extract]
    omega
  · show ρ.val (((zW.extract _ _).extract _ _).getD k zeroE) = _
    rw [extract_getD _ _ _ _ (by omega), extract_getD _ _ _ _ (by omega), Nat.zero_add]
    exact lp.hI k (by show k < S.lnT - 1 + 1; omega)

/-- **The value product below the diagonal: the typed weight at the output's point is the reading of
K5's weight.** D: the
description's sizes, which are L5.dimOf S. -/
theorem below_hW {X J : Type} [Fintype J] (D : AttSeg.Dim) (S : Attention.Shape) (hDS : D = OnBytes.Road.L5.dimOf S)
    (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = D.lT) (Cc : AttSeg.Calls)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (AttSeg.Step.s11.g D) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (stepSc3 D Cc rdc .s11 inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {Gf : Fork} (h : Heard) {pw zW : Array E}
    (hs : SizeP (SumL.of3 (stepSc3 D Cc rdc .s11 inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H h.below)
    (hsum : SumAt C st riders H h.below Gf) (lp : LookPts ρ D Cc Dd.st.z pw zW) (b : Fin D.nb) :
    (stepSc3 D Cc rdc .s11 inc wAt cAt).W Dd.st b
      (ldPartIni (AttSeg.Step.s11.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt) =
        ρ.val ((wBelow (geoOf S) pw zW h).getD b.1 zeroE) := by
  subst hDS
  have hsz : (chal h.below).size = AttSeg.Step.s11.g (OnBytes.Road.L5.dimOf S) := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  have hl := Z.lnT
  show Blocks.ext (AttSeg.Step.s11.g (OnBytes.Road.L5.dimOf S))
    (fun Y => AttSeg.Wb (OnBytes.Road.L5.dimOf S) Cc Dd.st .s11 b.1
      (Blocks.cubePt (AttSeg.Step.s11.g (OnBytes.Road.L5.dimOf S)) Y))
    (Blocks.nat (ldPartIni (AttSeg.Step.s11.g (OnBytes.Road.L5.dimOf S)) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [OnBytes.Road.Rows.wbExt11, below_weight S Z Cc Dd.st h lp hlt (by
    rw [hsz]
    show S.cf.lgk + (S.lnT - 1) + S.lnT ≤ S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB
    omega) b.2]
  exact congrArg _ hn

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.below_weight
#print axioms VerifiableInference.Desc.First.Att.P.below_hW
