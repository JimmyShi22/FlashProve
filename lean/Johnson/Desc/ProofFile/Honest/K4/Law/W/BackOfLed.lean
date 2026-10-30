-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/BackOfLed.lean: CONDITIONAL.

Not shown here. That the hypotheses hold anywhere: no example is known. THE HEARING's LEDGERS AND
TAPES (LedG) AND THAT THE CHALLENGES ARE THE TAPE's (DrawnIs), reach the first gated level (hl),
and have as many in front of them as the public data say (hh); THREE TIES TO THE LOOKUP (hzx, he;
hv stands on a third, the calls' points); THAT THE HONEST SIDE's MAKER OF THE BATCHED SUMCHECK's
DATA RETURNS, AND ITS END VALUES (data, ends); THAT WHAT THE LEDGER SHOWS UNDER THE SECOND TOKEN
SUMCHECK's END VALUES IS WHAT THE HONEST SIDE TOOK FOR THEM (hsh); K4Ground, which holds at shapes
with routed experts and the library's eleven switches alone; CellsAre; that the plan's list of
matrices is the verifier's (hmats); that the world's entries are the true ones (hW). By a walk over
the files' imports the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass,
CmsGlue, CmsBcs, Cms, Bcs); none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none
of the names Honest…, Both…, PassH…. No property is claimed.

The layers' own rounds (sub-protocol K4), the prover's side: THE TWO FIELDS sideA, sideB OF THE
RIGHT HALF FROM THE HEARING's RETURN: right_back_ground (Law/W/RightTermsOf.lean) with three of its
premises paid: StackAt (stackAt_of_led, Law/W/AtOfLed.lean), the nine equations on the named points
(NamedTie) and the verifier's call of stackEnd at the honest side's panels (hfin).

  `namedTie_led`   NamedTie at the batched sumcheck's prefix: six ties by Law/PtsAt.lean's laws; the
      embedding's point outside the first group and the two gated levels' points are empty there
      (Law/PtsFront.lean), so nothing is asked of them.
  `hfin_led`       hfin at some shown values: hfin_hear (Johnson/Road/K4/C/StackFin.lean) at LedG's
      own clause on the batched sumcheck.
  **`right_back_led`**   OpenedRightBack.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightTermsOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.AtOfLed
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsFront
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsPow
import Johnson.Road.K4.C.StackFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E)
open OnBytes.Model (World Fork Level Tsc HTailF2 Forest.Heard)
open OnBytes.Model.Layer (Own stackEnd TableAsk TableAt nEndT)
open OnBytes.K.Kc (Tape)
open OnBytes.Road (Mats matsR)
open OnBytes.Road.K4 (LedG entryTrue)
open OnBytes.Road.K4.W (K4Ground)
open OnBytes.Road.K4.C (NamedTie CellsAre hfin_hear stack_open sides_fields envOf_y envOf_g)
open OnBytes.Desc.First.K4.RtPub (EnvKeys)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {w : K4In} {h ds : List Fmt.Drawn}

/-- **The nine equations on the named points, at the batched sumcheck's prefix.** CONDITIONAL: on
every hypothesis named. -/
theorem namedTie_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length) (hh : h.length = Q.r0)
    (hzx : (w.look h).zx = fo.zx) : NamedTie Q (pts4 Q w h ds) o.H o.hd o.hd2 := by
  obtain ⟨_, _, _, e3, _, _, _⟩ := k4StartAt_eq Q
  unfold pts4
  rw [← e3]
  have l1 : k4StartAt Q 1 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have l2 : k4StartAt Q 2 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have l0 : 3 ≤ ds.length := by
    simp only [k4StartAt] at hl
    omega
  exact
    { zx := by rw [at_look w h ds hh, hzx, led_fo L]
      zt := fun _ _ => at_zt w h L ds hh hzx _
      r6 := fun _ => at_r6 w h L ds hD l1 hh _ (by simp only [k4StartAt]; omega)
      PV := fun _ _ => at_PV w h L ds hD l1 hh _ (by simp only [k4StartAt]; omega)
      ZE := fun hs h0 => by
        cases hg : (Q.g == 0) with
        | true => exact at_ZE w h L ds hD l0 hg hh _ (by simp only [k4StartAt]; omega)
        | false =>
          rw [at_ZE_else w hg] at hs
          exact absurd hs.symm h0
      rtV := fun _ _ => at_rtV w h L ds hD l2 hh _ (by simp only [k4StartAt]; omega)
      r12 := fun he => by
        rw [at_r12_front w h ds hh _ (by simp only [k4StartAt]; omega)] at he
        cases he
      rt := fun _ => ⟨_, L.kTT, at_rt w h L ds hD l3 hh _ (by simp only [k4StartAt]; omega)⟩
      r14 := fun he => by
        rw [at_r14_front w h ds hh _ (by simp only [k4StartAt]; omega)] at he
        cases he }

/-- **The verifier's call of stackEnd stands at the honest side's panels**, at some shown values.
CONDITIONAL: on every hypothesis named. -/
theorem hfin_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length) (hh : h.length = Q.r0)
    (hzx : (w.look h).zx = fo.zx) (he : (w.look h).e = fo.e)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q (pts4 Q w h ds) = some o.v) {seen : Seen}
    {SD : StackData}
    (data : stackData Q w (pts4 Q w h ds) (k4SentAt seen.rounds (k4TermsEnds Q)) = some SD)
    (hsh : ∀ tT' a, o.H.tT = some tT' →
      ((Array.range (nEndT Q.P.y)).mapM fun i => G2.shown (tT'.sEnd + i)) = some a →
      a = k4SentAt seen.rounds (k4TermsEnds Q)) :
    ∃ (H1' V : Array E) (a b : E),
      stackEnd SD.S.v.y SD.bl o.K.rs SD.S.Q.hp.lamS SD.om H1' V a b = some o.K.fin := by
  obtain ⟨_, _, _, e3, _, _, _⟩ := k4StartAt_eq Q
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  refine hfin_hear data L.c4 rfl rfl hv ?_ ?_ rfl ?_ hsh
  · unfold pts4
    rw [at_look w h ds hh, he, led_fo L]
  · exact at_zt w h L ds hh hzx _
  · have s3 : k4StartAt Q 2 + (Q.P.y.h.lt + 3) = k4StartAt Q 3 - 1 := by
      simp only [k4StartAt]
      omega
    unfold pts4
    rw [at_b3, s3, ← e3]
    exact at_stackPow w h L ds hD l3 hh _ (Nat.le_refl _)

/-- **THE FIELDS sideA, sideB FROM THE HEARING's RETURN.** CONDITIONAL: on every hypothesis named.
-/
theorem right_back_led {shp : OnBytes.Model.Layer.Shape} {pc : List (List String)} {D : Dim}
    {r : List TableAt × List (TableAsk × List (Nat × Nat)) × Nat} {tl : HTailF2}
    {pts : List (String × Array E)} {Mm : Mats Cb.Gl.E} {Wd : World Cb.Gl.E}
    (Gd : K4Ground shp pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D)
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length) (hh : h.length = Q.r0)
    (hzx : (w.look h).zx = fo.zx) (he : (w.look h).e = fo.e)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q (pts4 Q w h ds) = some o.v) {seen : Seen}
    {SD : StackData} {e : List E}
    (data : stackData Q w (pts4 Q w h ds) (k4SentAt seen.rounds (k4TermsEnds Q)) = some SD)
    (ends : SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = some e)
    (hmats : matsOf Q = matsR o.v.y o.v.g) (C : CellsAre Q w Mm)
    (hsh : ∀ tT' a, o.H.tT = some tT' →
      ((Array.range (nEndT Q.P.y)).mapM fun i => G2.shown (tT'.sEnd + i)) = some a →
      a = k4SentAt seen.rounds (k4TermsEnds Q))
    (hW : Wd.entry = entryTrue tl o Mm) : OpenedRightBack Wd Q o w h ds seen := by
  have hy : Q.P.y = o.v.y := (envOf_y hv).symm
  have hg : Q.g = o.v.g := (envOf_g hv).symm
  have A := stackAt_of_led L hD hl hh hzx data ends hy.symm
  obtain ⟨H1', V, a, b, hfin⟩ := hfin_led L hD hl hh hzx he hv data hsh
  obtain ⟨hS, -, -⟩ := stack_open data
  obtain ⟨-, -, -, hv0, -⟩ := sides_fields hS
  have ev : SD.S.v = o.v := Option.some.inj (hv0.symm.trans hv)
  have K : EnvKeys SD.S.v o.v := by
    rw [ev]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact right_back_ground Gd A hy hg hmats K (namedTie_led L hD hl hh hzx) C hfin hW

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.namedTie_led
#print axioms ProofFile.Honest.K4.W.hfin_led
#print axioms ProofFile.Honest.K4.W.right_back_led
