-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/AtOfLed.lean: CONDITIONAL.

Not shown here. THAT THE VERIFIER's HEARING HAS RETURNED (the library's LedG,
Johnson/Road/K4/OwnLedgersG.lean) AND THAT ITS TAPE HAS SAMPLED WHAT THE CHALLENGES HOLD (DrawnIs,
Law/PtsNorms.lean): hypotheses. That the honest side's functions return and that the cubes' sizes
fit: hypotheses. That the layouts and the groups agree; that the key point in the honest side's look
is the one that the verifier was handed (one field, zx): hypotheses. That they can hold together: no
example is known. By a walk of import lines the closure holds seven modules under
Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's
imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none of the names
Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The clauses of `GatedAt`, `EmbAt` (Law/W/RightGated.lean) and `StackAt` (Law/W/RightStack.lean) that
tie the honest side's challenges and points to what the verifier holds, from the hearing's return:
by the laws of Law/PtsHear.lean and Law/PtsAt.lean, `pointOf_levelR` (Law/SumPoints.lean) and the
rounds' numbers (Law/Starts.lean). What is left of the three structures: the honest side's returns
and the cubes' fits.

  `gatedAt_of_led`   GatedAt.
  `embAt_of_led`   EmbAt.
  `stackAt_of_led`   StackAt.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightGated
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightStack
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPoints
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (Fork Level Tsc WsClaim Forest.Heard orderRange)
open OnBytes.Model.Layer (Own ClaimEnv downFrom)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.K4 (k0)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {w : K4In} {h ds : List Fmt.Drawn}

/-- **GatedAt from the hearing's return.** CONDITIONAL: on every hypothesis named. -/
theorem gatedAt_of_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length) {tb1 tb2 : Tab × Tab}
    (t1 : gatedTabs Q w = some tb1) (t2 : gatedTabs2 Q w = some tb2)
    (fit1 : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (pts5 Q w h ds).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (pts5 Q w h ds))
      tb1).cube.fits = true)
    (fit2 : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((pts6 Q w h ds).rhoM ++ downFrom (pts6 Q w h ds).rs Q.P.y.lfe ++ (pts6 Q w h ds).rt)
      tb2).cube.fits = true) :
    GatedAt Q w h ds o tb1 tb2 := by
  obtain ⟨_, _, _, _, e4, e5, e6⟩ := k4StartAt_eq Q
  have l6 : rE Q.P Q.hp Q.g + 1 ≤ ds.length := by rw [← e6]; exact hl
  have l5 : k4StartAt Q 5 ≤ ds.length := by
    rw [e5]
    unfold rE at l6
    omega
  have a1 := led_r12 L ds hD l5
  have a2 := led_r14 L ds hD hl
  rw [e4] at a1
  rw [e5] at a2
  exact
    { t1 := t1
      t2 := t2
      len1 := ownE_length ds _ _ (by rw [e5] at l5; unfold rJ6 at l5; omega)
      len2 := ownE_length ds _ _ (by unfold rE at l6; omega)
      fit1 := fit1
      fit2 := fit2
      r1 := by rw [pointOf_levelR]; exact a1
      r2 := fun o2 h2 => by
        obtain rfl : hd2 = o2 := Option.some.inj (L.eHd2.symm.trans h2)
        rw [pointOf_levelR]
        exact a2 }

/-- **EmbAt from the hearing's return.** CONDITIONAL: on every hypothesis named. -/
theorem embAt_of_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : 3 ≤ ds.length) (hg : (Q.g == 0) = true) (hh : h.length = Q.r0)
    {ce : ClaimEnv} {cl : WsClaim} (env : claimEnvOf Q (ptsE Q w h ds) = some ce)
    (claim : ce.claimE (ptsE Q w h ds).ZE (ptsE Q w h ds).tkh Q.P.V w.tokv = some cl)
    (eg : o.v.g = Q.g) (ey : ce.v.y = o.v.y) : EmbAt Q w h ds o ce cl := by
  have hn : 2 < rE Q.P Q.hp Q.g := by
    unfold rE rJ6 rJ5 rJ4 rJ3 rJ2 rowsRound
    omega
  exact
    { env := env
      claim := claim
      g := eg
      y := ey
      ZE := at_ZE w h L ds hD hl hg hh _ (by omega)
      tkh := at_tkh w h L ds hD hl hg hh _ hn }

/-- **StackAt from the hearing's return.** CONDITIONAL: on every hypothesis named. -/
theorem stackAt_of_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length) (hh : h.length = Q.r0)
    (hzx : (w.look h).zx = fo.zx) {seen : Seen} {SD : StackData} {e : List E}
    (data : stackData Q w (pts4 Q w h ds) (k4SentAt seen.rounds (k4TermsEnds Q)) = some SD)
    (ends : SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = some e)
    (ey : o.v.y = Q.P.y) : StackAt Q w h ds seen o SD e := by
  obtain ⟨_, _, e2, e3, e4, _, _⟩ := k4StartAt_eq Q
  have a := led_rs L ds hD hl
  rw [e3] at a
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    rw [e3]
    rw [e4] at hl
    unfold rJ5 at hl
    omega
  exact
    { data := data
      ends := ends
      rs := a.symm
      zt := at_zt w h L ds hh hzx _
      rt := fun tT' hT => by
        obtain rfl := Option.some.inj (L.kTT.symm.trans hT)
        exact at_rt w h L ds hD l3 hh _ (by rw [e2]; unfold rJ4; omega)
      y := ey }

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.gatedAt_of_led
#print axioms ProofFile.Honest.K4.W.embAt_of_led
#print axioms ProofFile.Honest.K4.W.stackAt_of_led
