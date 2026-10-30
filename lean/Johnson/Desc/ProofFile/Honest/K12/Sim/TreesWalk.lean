-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesWalk.lean: the shift of TreesShift.lean is the same
whether it is computed along the first run or along the other, and it is 0 outside the places that a
finite type of random values fills: each under premises. The nine equations ask `AtSwitchT`
(TreesStep.lean: how the two runs stand to each other at the switch); `walkSame_trees` asks
`AtStageT` (there) and `FitsBody` (Johnson/LinkSim/AtText/SpecShift.lean: public sizes, and how many
positions are sampled); `inBody_sh_trees` asks `FitsBody`; `inSwitch_sh_trees` asks `CsFit` and two
bounds on the next stage's positions. Statements and proofs on variables.

  `walk_dMu_trees` ... `walk_dNext_trees`   nine equations, one for each piece of the shift at the
                 switch
  `walkSame_trees`   so `shT` along the other run is `shT` along the first, at the same letter t₃
  `inSwitch_sh_trees`, `inBody_sh_trees`   the switch's part of the shift, and `shT`, are 0 outside
                 the places (`InSwitch`, `InBody`, Johnson/LinkSim/AtText/Places.lean)

By what. The proofs are those of Johnson/LinkSim/AtText/Walk.lean, of `walkSame` (Induct.lean) and
of `inSwitch_sh` and `inBody_sh` (PlacesProof.lean) in the arm "not the last". From the next stage
on `walkSame` itself is called, over `atStage_second` (TreesStep.lean), and `inBody_sh` itself.

Limits. t₃ is one variable for both runs: that both reach it is shown in Sim/TreesText.lean for the
text's own state. `InBody` speaks from the switch in hand on: "0 outside the places" says nothing of
earlier switches. Equations on variables: no finite type of random values, no law. Nothing on
completeness, soundness or hiding.

Sources. The four definitions and the proofs of the step follow, line by line,
Johnson/LinkSim/AtText/ShiftDefs.lean, Step.lean, Walk.lean, Induct.lean and PlacesProof.lean; the
note on sources in the head of ShiftDefs.lean holds here too.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText

/-! ## 1 Each piece is the same along both runs -/

section
variable {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {ρ : GroupRow} {D : ℕ → Fmt.Drawn}

theorem walk_dMu_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    dMu Ks j cur o t Ps D d = dMu Kr j cur o t Pr D d := by
  unfold dMu
  rw [sGam_same_trees h]

theorem walk_dTl_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    dTl Ks j cur o t Ps D d = dTl Kr j cur o t Pr D d := by
  unfold dTl
  rw [sGam_same_trees h]

theorem walk_sBits_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sBits p Ks j cur next l o t Ps D = sBits p Kr j cur next l o t Pr D := by
  unfold sBits
  rw [sT1_same_trees h]

theorem walk_shFr_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    shFr p Ks j cur next l o t Ps D d = shFr p Kr j cur next l o t Pr D d := by
  unfold shFr
  rw [walk_dMu_trees h, walk_dTl_trees h, walk_sBits_trees h]

theorem walk_dTab_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    dTab p Ks j cur next l o t Ps D d = dTab p Kr j cur next l o t Pr D d := by
  unfold dTab
  rw [walk_shFr_trees h, sGam_same_trees h]

theorem walk_shW_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) (σ : Sg) :
    shWT p Ks j cur next l o t Ps ρ D d σ = shWT p Kr j cur next l o t Pr ρ D d σ := by
  unfold shWT
  rw [walk_dTab_trees h]

theorem walk_dFresh_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    dFreshT p Ks j cur next l o t Ps ρ D d = dFreshT p Kr j cur next l o t Pr ρ D d := by
  funext b i
  unfold dFreshT
  rw [walk_shW_trees h]

theorem walk_shNew_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    shNewT p Ks j cur next l o t Ps ρ D d = shNewT p Kr j cur next l o t Pr ρ D d := by
  unfold shNewT
  rw [walk_dTab_trees h, walk_dFresh_trees h]

theorem walk_dNext_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    dNextT p Ks j cur next l o t Ps ρ D d = dNextT p Kr j cur next l o t Pr ρ D d := by
  unfold dNextT
  rw [walk_shNew_trees h, walk_dTab_trees h, walk_dFresh_trees h]

end

/-! ## 2 Along the stages -/

/-- **Computed along the other run, at the same t₃, the shift is the same**: under `FitsBody` and
`AtStageT`. -/
theorem walkSame_trees {p : P12} {D : ℕ → Fmt.Drawn} {nx : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t t₃ : T12}
    {Kr Ks : BCoins} {Pr Ps d : PS} (hF : FitsBody D (next :: nx :: rest) cur o)
    (hA : AtStageT p D nx rest j cur next l o t t₃ Kr Ks Pr Ps d) :
    shT p Ks D nx rest j cur next l o t Ps t₃ d = shT p Kr D nx rest j cur next l o t Pr t₃ d := by
  have hS := atSwitch_of_trees hF hA
  have hi := walkSame p D (nx :: rest) (j + 1) next (l.drop (cur.k + 3)) (oNext cur o) t₃ Kr Ks _ _
    _ _ _ hF.2.2.2.2 (atStage_second hF hA)
  unfold shT
  rw [walk_dNext_trees hS, hi, walk_shNew_trees hS, walk_shFr_trees hS]
  simp only [walk_shW_trees hS]

/-! ## 3 The shift is 0 outside the places -/

theorem inSwitch_sh_trees (p : P12) (K : BCoins) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (P : PS) (ρ : GroupRow) (D : ℕ → Fmt.Drawn) (d : PS)
    (hf : CsFit (sgOf cur) (sgOf next))
    (hC : (qNext false cur next o D).length ≤ (sgOf next).C.r)
    (hZ : (qNext false cur next o D).length ≤ (sgOf next).Z.r) :
    InSwitch (sgOf cur) (sgOf next) false (shFr p K j cur next l o t P D d)
      (shNewT p K j cur next l o t P ρ D d) (fun σ => shWT p K j cur next l o t P ρ D d σ) := by
  have hp := padIx_in hf
  refine ⟨fun i hi => ?_, fun _ => rfl, fun _ => rfl, fun b q hb => ?_, fun b q hb => ?_,
    fun b q hb => ?_, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun σ hσ => ?_⟩
  · unfold shFr
    rw [Pi.single_apply, if_neg fun e : i = padIx (sgOf next) => hi (by rw [e]; exact hp)]
  · show (if b < 2 ^ ((sgOf next).h + (sgOf next).g) then _ else (0 : ℕ → GE)) q = 0
    split_ifs with h1
    · exact tailAt_high _ _ _ hC _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩)
    · rfl
  · show (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = 0
    split_ifs with h1
    · exact tailAt_high _ _ _ hZ _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩)
    · rfl
  · show (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = 0
    split_ifs with h1
    · exact tailAt_high _ _ _ hZ _ (not_lt.mp fun h2 => hb ⟨h1, h2⟩)
    · rfl
  · show shWT p K j cur next l o t P ρ D d σ = 0
    unfold shWT
    rw [if_neg fun e => hσ ⟨rfl, e⟩]

/-- **The shift is 0 outside the places**, at every t₃: under `FitsBody`. -/
theorem inBody_sh_trees (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (nx : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12)
    (P : PS) (t₃ : T12) (d : PS) (hF : FitsBody D (next :: nx :: rest) cur o) :
    InBody cur (next :: nx :: rest) j (shT p K D nx rest j cur next l o t P t₃ d) := by
  have hq := qNext_le (cur := cur) (o := o) hF.2.2.2.2
  have hs := inSwitch_sh_trees p K j cur next l o t P (rowOf t₃) D d hF.2.2.2.1 hq.1 hq.2
  have hi := inBody_sh p K D (nx :: rest) (j + 1) next (l.drop (cur.k + 3)) (oNext cur o) t₃
    (sNext K false j cur next o P (rowOf t) D) (sCol K false j cur next o P (rowOf t) D)
    (dNextT p K j cur next l o t P (rowOf t₃) D d) hF.2.2.2.2
  refine ⟨?_, inBody_congr (nx :: rest) next (j + 1) _ _ (fun i hi' => ⟨?_, ?_⟩)
    (fun σ i hi' => ?_) hi⟩
  · have e1 : (shT p K D nx rest j cur next l o t P t₃ d).fr j =
        shFr p K j cur next l o t P D d := if_pos rfl
    have e2 : (shT p K D nx rest j cur next l o t P t₃ d).new j =
        shNewT p K j cur next l o t P (rowOf t₃) D d := if_pos rfl
    have e3 : (fun σ => (shT p K D nx rest j cur next l o t P t₃ d).W σ (j + 1)) =
        fun σ => shWT p K j cur next l o t P (rowOf t₃) D d σ :=
      funext fun σ => if_pos rfl
    rw [e1, e2, e3]
    exact hs
  · exact (if_neg (by omega : ¬ i = j)).symm
  · exact (if_neg (by omega : ¬ i = j)).symm
  · exact (if_neg (by omega : ¬ i = j + 1)).symm

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.walk_dMu_trees
#print axioms ProofFile.Honest.K12.walk_dTl_trees
#print axioms ProofFile.Honest.K12.walk_sBits_trees
#print axioms ProofFile.Honest.K12.walk_shFr_trees
#print axioms ProofFile.Honest.K12.walk_dTab_trees
#print axioms ProofFile.Honest.K12.walk_shW_trees
#print axioms ProofFile.Honest.K12.walk_dFresh_trees
#print axioms ProofFile.Honest.K12.walk_shNew_trees
#print axioms ProofFile.Honest.K12.walk_dNext_trees
#print axioms ProofFile.Honest.K12.walkSame_trees
#print axioms ProofFile.Honest.K12.inSwitch_sh_trees
#print axioms ProofFile.Honest.K12.inBody_sh_trees
