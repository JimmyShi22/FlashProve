-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/GatedOf.lean: CONDITIONAL.

What is here. Two hypotheses of JoinPub.lean's `joinWorth_pub` on the honest tables of the gated
products, paid from the laws of Johnson/Road/K4/C/StackEnds.lean. The never-sent vector number 0,
read off the honest table under the lookup's token point (`hvOfD`, PanelTiesOf.lean), is the
library's vector of the gated products at that point (the hypothesis hH). The honest table at one
token (`hhAt`, TokFitsOf.lean) is the library's vector of the routed gated products at the token's
corner (the second clause of `TokLeft`).

  `hhU_pt`   the library's vector reads the first coordinates of its point alone
  `hv0_gated`   **the never-sent vector number 0**
  `hhAt_gated`   **the table at a token**

Limits. At the reading `Reading.gl`. HYPOTHESES, as in that file: the honest input's two tensors
read as the library's values (`TensorIs`); twelve public numbers (`GatedNums`): the sizes are powers
of two; the two tensors are found in the layout; the function that makes the job's data returns.
Johnson/Road/K4/C/ has payers for these under a plan's hypotheses (`gatedNums_of_plan`,
`gated_tensors`): they are not called here. Beside them: fe is at most f; the layers and the routed
layers lie in the library's ranges (nl at most two to lL; ne at most two to lL less one); the token
point has the bits of a token and reads as the library's. No example of the hypotheses together is
known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokFitsOf
import Johnson.Road.K4.C.StackIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading)
open OnBytes.Model.Layer (Ten)
open OnBytes.Road (pt)
open OnBytes.Road.K4.C (TensorIs GatedNums StackIs stackIs_of gatedUnder_read hh_read slup_at
  ext_corner)
open Inst.Model.FFSeg (Dim Cell lF lFe hhU zpos fSh)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData} {D : Dim}
  {t : Cell → Cb.Gl.E} {ts tu : Ten}

/-- The library's vector of the gated products reads the first lT coordinates of its point alone. -/
theorem hhU_pt (l j : ℕ) {u u' : ℕ → Cb.Gl.E} (h : ∀ k, k < D.lT → u k = u' k) :
    hhU D t l j u = hhU D t l j u' :=
  OnBytes.Road.ext_congr_pt D.lT _ h

/-- **THE NEVER-SENT VECTOR NUMBER 0 IS THE LIBRARY's VECTOR OF THE GATED PRODUCTS AT THE LOOKUP's
TOKEN POINT.** CONDITIONAL: on every hypothesis named. -/
theorem hv0_gated (h : stackData Q w p shownT = some SD) (hts : Q.P.y.T_ "s" = some ts)
    (htu : Q.P.y.T_ "u" = some tu) (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu)
    (N : GatedNums Q D) (hzs : SD.S.zt.size = D.lT) (z : ℕ → Cb.Gl.E)
    (hzp : ∀ j, j < D.lT → zpos D z j = pt Reading.gl SD.S.zt j) (hnl : D.nl ≤ 2 ^ D.lL)
    (hfe : D.fe ≤ D.f) :
    ∀ l, l < D.nl → ∀ j, j < fSh D l →
      hvOfD SD (ceilLog2 SD.S.v.y.h.f) 0 (l * 2 ^ ceilLog2 SD.S.v.y.h.f + j) =
        hhU D t l j (zpos D z) := by
  intro l hl j hj
  obtain ⟨_, tb, I⟩ := stackIs_of h
  have cf : ceilLog2 SD.S.v.y.h.f = lF D := by
    rw [I.y, N.f, OnBytes.Road.ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide)]
  have hDf : D.f ≤ 2 ^ lF D := Nat.le_pow_clog (by decide) D.f
  have hj' : j < 2 ^ lF D := by
    have : fSh D l ≤ D.f := by
      unfold fSh
      split_ifs
      · exact hfe
      · exact Nat.le_refl _
    omega
  unfold hvOfD
  rw [if_pos rfl, cf, div_grid l (2 ^ lF D) j hj', mod_grid l (2 ^ lF D) j hj', I.y, N.Pf, I.hZ,
    gatedUnder_read hts htu Ss Su N I SD.S.zt hzs (lt_of_lt_of_le hl hnl) hj']
  exact hhU_pt l j fun k hk => (hzp k hk).symm

/-- **THE HONEST TABLE AT A TOKEN IS THE LIBRARY's VECTOR OF THE ROUTED GATED PRODUCTS AT THE
TOKEN's CORNER.** CONDITIONAL: on every hypothesis named. -/
theorem hhAt_gated (h : stackData Q w p shownT = some SD) (hts : Q.P.y.T_ "s" = some ts)
    (htu : Q.P.y.T_ "u" = some tu) (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu)
    (N : GatedNums Q D) (hlt : D.lT = SD.S.v.y.h.lt) (hne : 2 * D.ne ≤ 2 ^ D.lL) {i : ℕ}
    (hi : i < 2 ^ D.lT) :
    ∀ l', l' < D.ne → ∀ j, j < D.fe →
      Reading.gl.val (hhAt SD.S i l' j) = hhU D t (2 * l' + 1) (D.fe + j) (zhAt SD.S i) := by
  intro l' hl' j hj
  obtain ⟨_, tb, I⟩ := stackIs_of h
  have hF : 2 ^ lF D = 2 * 2 ^ lFe D := by rw [N.ffe, Nat.pow_succ, Nat.mul_comm]
  have hj' : D.fe + j < 2 ^ lF D := by
    rw [hF, ← N.Dfe]
    omega
  have hT : D.T = 2 ^ D.lT := rfl
  have hX : ((2 * l' + 1) * 2 ^ lF D + (D.fe + j)) * D.T + i < 2 ^ (D.lL + lF D + D.lT) := by
    rw [Nat.pow_add, Nat.pow_add, hT]
    exact grid_lt (grid_lt (show 2 * l' + 1 < 2 ^ D.lL by omega) hj') hi
  have e : hhAt SD.S i l' j =
      SD.S.hh.getD (((2 * l' + 1) * 2 ^ lF D + (D.fe + j)) * D.T + i) zeroE := by
    unfold hhAt OnBytes.Desc.First.K4.Honest.Sides.routedAt
    rw [I.y, N.Pf, N.fe, N.T, ← N.Dfe, Nat.add_assoc]
    rfl
  rw [e, hh_read hts htu Ss Su N I hX, slup_at (2 * l' + 1) hj' hi]
  unfold hhU zhAt
  rw [← hlt]
  exact (ext_corner D.lT _ hi).symm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.hhU_pt
#print axioms ProofFile.Honest.K4.hv0_gated
#print axioms ProofFile.Honest.K4.hhAt_gated
