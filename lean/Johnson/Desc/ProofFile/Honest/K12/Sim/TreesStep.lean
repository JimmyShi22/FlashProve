-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesStep.lean: at one switch of a proximity test that is not
the last, two runs side by side whose random values differ by the shift of TreesShift.lean show the
same rounds, and in front of the next stage the library's `AtStage`
(Johnson/LinkSim/AtText/SpecStage.lean) holds, at whatever state of the verifier the shift was
computed with. Statements and proofs on letters.

Why. The library's step (`atStage_next`, Johnson/LinkSim/AtText/Induct.lean) is stated at the state
that one tree's column leaves. `AtStage` itself has the verifier's state as a free letter. So where
the first round of positions opens several trees, the library's induction along the stages can be
entered in front of the SECOND stage, once this one step is shown at a letter.

  `AtSwitchT`, `AtStageT`   `AtSwitch` and `AtStage` with the letters ρ and t₃; their clause on the
                 tree in hand is left out: no statement here reads that tree
  `sRF_same_trees`, `sGam_same_trees`, `sT1_same_trees`, `sAns_same_trees`, `sRS_same_trees`   the
                 fold's rounds, its point, the verifier's state behind the fold, the answer and the
                 switch's two rounds are the same in both runs
  `sNext_add_trees`, `muOf_dNext_trees`, `sCol_same_trees`   the next states differ by `dNextT`,
                 whose message is that of the table's difference; the next trees' columns agree
                 where they are opened
  `atSwitch_of_trees`, `atStage_second`   from `AtStageT`: `AtSwitchT`; and `AtStage` in front of
                 the next stage, at t₃

By what. The proofs are those of Johnson/LinkSim/AtText/Step.lean and Induct.lean in the arm "not
the last": these never unfold the state behind the switch. `stage_col_eq`, the laws of adding and
`qNext_le` are called.

Limits. That the two runs reach one state t₃ behind the switch is not shown here: t₃ is a variable
(Sim/TreesText.lean has it for the text's own state). Equations on variables, also at such as no run
reaches: no finite type of random values, no law. Of `FitsBody` the last clause alone is used; its
first four (two on the tree in hand, the packing's room, `CsFit`) are not. Nothing on completeness,
soundness or hiding.

Sources. The four definitions and the proofs of the step follow, line by line,
Johnson/LinkSim/AtText/ShiftDefs.lean, Step.lean, Walk.lean, Induct.lean and PlacesProof.lean; the
note on sources in the head of ShiftDefs.lean holds here too.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText

/-! ## 1 What is asked at the switch -/

/-- `AtSwitch` (Johnson/LinkSim/AtText/Step.lean) at a switch that is not the last, with the letter
ρ in the place of the row behind the switch; its clause on the tree in hand is left out. -/
structure AtSwitchT (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12)
    (Kr Ks : BCoins) (Pr Ps d : PS) (ρ : GroupRow) (D : ℕ → Fmt.Drawn) : Prop where
  st : Pr = addPS Ps d
  foldW : Ks.W (sgOf cur) j = Kr.W (sgOf cur) j +
    foldShift (sgOf cur) (vecG (sgOf cur) (rowOf t)) (μOf (sgOf cur) d) fun n => D (o + n)
  fr : Ks.fr j = Kr.fr j + shFr p Kr j cur next l o t Pr D d
  new : Ks.new j = addPS (Kr.new j) (shNewT p Kr j cur next l o t Pr ρ D d)
  nextW : Ks.W (sgOf next) (j + 1) = Kr.W (sgOf next) (j + 1) +
    shWT p Kr j cur next l o t Pr ρ D d (sgOf next)
  qC : (qNext false cur next o D).length ≤ (sgOf next).C.r
  qZ : (qNext false cur next o D).length ≤ (sgOf next).Z.r

section
variable {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {ρ : GroupRow} {D : ℕ → Fmt.Drawn}

/-! ## 2 The fold, the answer, the switch's rounds -/

theorem sRF_same_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sRF Kr j cur o Pr (rowOf t) D = sRF Ks j cur o Ps (rowOf t) D := by
  unfold sRF
  rw [h.st, muOf_add, foldRV_shift, ← h.foldW]

theorem sGam_same_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sGam Kr j cur o Pr (rowOf t) D = sGam Ks j cur o Ps (rowOf t) D := by
  unfold sGam
  rw [sRF_same_trees h]

theorem sT1_same_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sT1 p Kr j cur l o t Pr (rowOf t) D = sT1 p Ks j cur l o t Ps (rowOf t) D := by
  unfold sT1
  rw [sRF_same_trees h]

theorem sAns_same_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sAns p Kr j cur next l o t Pr (rowOf t) D = sAns p Ks j cur next l o t Ps (rowOf t) D := by
  have e : sAns p Kr j cur next l o t Pr (rowOf t) D =
      ansAt (sgOf cur) (sgOf next)
        (foldMsg (sgOf cur) (μOf (sgOf cur) Ps) (φOf (sgOf cur) Ps)
            (sGam Kr j cur o Pr (rowOf t) D) + dMu Kr j cur o t Pr D d)
        (foldTl (sgOf cur) (ρOf (sgOf cur) Ps) (ψOf (sgOf cur) Ps)
            (sGam Kr j cur o Pr (rowOf t) D) + dTl Kr j cur o t Pr D d)
        (Kr.fr j) (sEls cur o D) (sBits p Kr j cur next l o t Pr D) := by
    unfold dMu dTl
    rw [← foldMsg_add, ← foldTl_add, ← muOf_add, ← phiOf_add, ← rhoOf_add, ← psiOf_add, ← h.st]
    rfl
  rw [e, ansAt_shift]
  have f : Kr.fr j + Pi.single (padIx (sgOf next))
      (ansShift (sgOf cur) (sgOf next) (dMu Kr j cur o t Pr D d) (dTl Kr j cur o t Pr D d)
        (sEls cur o D) (sBits p Kr j cur next l o t Pr D)) = Ks.fr j := h.fr.symm
  rw [f, sGam_same_trees h]
  unfold sBits
  rw [sT1_same_trees h]
  rfl

theorem sRS_same_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sRS p Kr j cur next l o t Pr (rowOf t) D = sRS p Ks j cur next l o t Ps (rowOf t) D := by
  unfold sRS
  rw [sAns_same_trees h]

/-! ## 3 The next state -/

/-- The first run's next state is the other run's next state plus `dNextT`. -/
theorem sNext_add_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) :
    sNext Kr false j cur next o Pr (rowOf t) D =
      addPS (sNext Ks false j cur next o Ps (rowOf t) D)
        (dNextT p Kr j cur next l o t Pr ρ D d) := by
  have hγ := sGam_same_trees h
  have hfr : Kr.fr j = Ks.fr j + -shFr p Kr j cur next l o t Pr D d := by
    rw [h.fr]
    exact (add_neg_cancel_right _ _).symm
  have hμ : μOf (sgOf cur) Pr = μOf (sgOf cur) Ps + μOf (sgOf cur) d :=
    (congrArg _ h.st).trans (muOf_add _ _ _)
  have hφ : φOf (sgOf cur) Pr = φOf (sgOf cur) Ps + φOf (sgOf cur) d :=
    (congrArg _ h.st).trans (phiOf_add _ _ _)
  have hρ : ρOf (sgOf cur) Pr = ρOf (sgOf cur) Ps + ρOf (sgOf cur) d :=
    (congrArg _ h.st).trans (rhoOf_add _ _ _)
  have hψ : ψOf (sgOf cur) Pr = ψOf (sgOf cur) Ps + ψOf (sgOf cur) d :=
    (congrArg _ h.st).trans (psiOf_add _ _ _)
  refine ps_ext (funext fun i => ?_) (funext fun i => ?_) (funext fun b => funext fun q => ?_)
    (funext fun b => funext fun q => ?_) (funext fun b => funext fun i => ?_)
    (funext fun b => funext fun q => ?_) (funext fun i => ?_) (funext fun q => ?_)
  · show (sNext Kr false j cur next o Pr (rowOf t) D).tabM i =
      (sNext Ks false j cur next o Ps (rowOf t) D).tabM i +
        gMain (sgOf cur) (foldMsg (sgOf cur) (μOf (sgOf cur) d) (φOf (sgOf cur) d)
          (sGam Kr j cur o Pr (rowOf t) D)) i
    rw [sNext_tabM, sNext_tabM, hμ, hφ, foldMsg_add, gMain_add, hγ]
  · show (sNext Kr false j cur next o Pr (rowOf t) D).tabZ i =
      (sNext Ks false j cur next o Ps (rowOf t) D).tabZ i +
        gMask (sgOf cur) (foldMsg (sgOf cur) (μOf (sgOf cur) d) (φOf (sgOf cur) d)
            (sGam Kr j cur o Pr (rowOf t) D))
          (foldTl (sgOf cur) (ρOf (sgOf cur) d) (ψOf (sgOf cur) d)
            (sGam Kr j cur o Pr (rowOf t) D)) (-shFr p Kr j cur next l o t Pr D d) i
    rw [sNext_tabZ, sNext_tabZ, hμ, hφ, hρ, hψ, foldMsg_add, foldTl_add]
    conv_lhs => rw [hfr]
    rw [gMask_add, hγ]
  · show (sNext Kr false j cur next o Pr (rowOf t) D).tM b q =
      (sNext Ks false j cur next o Ps (rowOf t) D).tM b q +
        -(shNewT p Kr j cur next l o t Pr ρ D d).tM b q
    rw [sNext_tM, sNext_tM, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr false j cur next o Pr (rowOf t) D).tZ b q =
      (sNext Ks false j cur next o Ps (rowOf t) D).tZ b q +
        -(shNewT p Kr j cur next l o t Pr ρ D d).tZ b q
    rw [sNext_tZ, sNext_tZ, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show packedN (sgOf next) (Kr.W (sgOf next) (j + 1)) b i =
      packedN (sgOf next) (Ks.W (sgOf next) (j + 1)) b i +
        -packedN (sgOf next) (shWT p Kr j cur next l o t Pr ρ D d (sgOf next)) b i
    rw [h.nextW, packedN_add]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr false j cur next o Pr (rowOf t) D).fT b q =
      (sNext Ks false j cur next o Ps (rowOf t) D).fT b q +
        -(shNewT p Kr j cur next l o t Pr ρ D d).fT b q
    rw [sNext_fT, sNext_fT, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr false j cur next o Pr (rowOf t) D).sM i =
      (sNext Ks false j cur next o Ps (rowOf t) D).sM i +
        -(shNewT p Kr j cur next l o t Pr ρ D d).sM i
    rw [sNext_sM, sNext_sM, h.new]
    exact (add_neg_cancel_right _ _).symm
  · show (sNext Kr false j cur next o Pr (rowOf t) D).sT q =
      (sNext Ks false j cur next o Ps (rowOf t) D).sT q +
        -(shNewT p Kr j cur next l o t Pr ρ D d).sT q
    rw [sNext_sT, sNext_sT, h.new]
    exact (add_neg_cancel_right _ _).symm

end

theorem muOf_dNext_trees (p : P12) (K : BCoins) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (P : PS) (ρ : GroupRow) (D : ℕ → Fmt.Drawn) (d : PS) (σ : Sg) :
    μOf σ (dNextT p K j cur next l o t P ρ D d) = μOf σ (dTab p K j cur next l o t P D d) := by
  funext x
  cases x <;> rfl

/-! ## 4 The next tree's columns -/

section
variable {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {ρ : GroupRow} {D : ℕ → Fmt.Drawn}

/-- The next trees have equal columns at the positions at which they are opened. -/
theorem sCol_same_trees (h : AtSwitchT p j cur next l o t Kr Ks Pr Ps d ρ D) {x : ℕ}
    (hx : x ∈ Fmt.listOf (qNext false cur next o D)) :
    sCol Kr false j cur next o Pr (rowOf t) D x = sCol Ks false j cur next o Ps (rowOf t) D x := by
  have hxQ : x ∈ qNext false cur next o D := (Fmt.listOf_mem _ _).mp hx
  have hN := sNext_add_trees h
  have htM : (sNext Ks false j cur next o Ps (rowOf t) D).tM =
      fun b q => (sNext Kr false j cur next o Pr (rowOf t) D).tM b q +
        (shNewT p Kr j cur next l o t Pr ρ D d).tM b q := by
    rw [sNext_tM, sNext_tM, h.new]
    rfl
  have htZ : (sNext Ks false j cur next o Ps (rowOf t) D).tZ =
      fun b q => (sNext Kr false j cur next o Pr (rowOf t) D).tZ b q +
        (shNewT p Kr j cur next l o t Pr ρ D d).tZ b q := by
    rw [sNext_tZ, sNext_tZ, h.new]
    rfl
  have hfT : (sNext Ks false j cur next o Ps (rowOf t) D).fT =
      fun b q => (sNext Kr false j cur next o Pr (rowOf t) D).fT b q +
        (shNewT p Kr j cur next l o t Pr ρ D d).fT b q := by
    rw [sNext_fT, sNext_fT, h.new]
    rfl
  refine stage_col_eq (sgOf next) _ h.qC h.qZ _ _ (dTab p Kr j cur next l o t Pr D d)
    (dFreshT p Kr j cur next l o t Pr ρ D d)
    (fun i => congrFun (congrArg PS.tabM hN) i) (fun i => congrFun (congrArg PS.tabZ hN) i)
    (fun b i => congrFun (congrFun (congrArg PS.fM hN) b) i) (fun b hb => ?_) (fun b hb => ?_)
    (fun b hb => ?_) hxQ
  · rw [htM]
    funext q
    show _ + (if b < 2 ^ ((sgOf next).h + (sgOf next).g) then _ else (0 : ℕ → GE)) q = _
    rw [if_pos hb]
    rfl
  · rw [htZ]
    funext q
    show _ + (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = _
    rw [if_pos hb]
    rfl
  · rw [hfT]
    funext q
    show _ + (if b < 2 ^ (sgOf next).h then _ else (0 : ℕ → GE)) q = _
    rw [if_pos hb]
    rfl

end

/-! ## 5 In front of the stage, and in front of the next -/

/-- `AtStage` (Johnson/LinkSim/AtText/SpecStage.lean) in front of a stage that is followed by two
stages or more, with `shT` at t₃ in the place of `shB`. Two clauses are left out: that on the tree
in hand, and that on the last stage's word, which asks nothing where stages follow; the clause
`foldW` has lost its premise "stages follow", which is met. -/
structure AtStageT (p : P12) (D : ℕ → Fmt.Drawn) (nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t t₃ : T12) (Kr Ks : BCoins)
    (Pr Ps d : PS) : Prop where
  st : Pr = addPS Ps d
  foldW : Ks.W (sgOf cur) j = Kr.W (sgOf cur) j +
    foldShift (sgOf cur) (vecG (sgOf cur) (rowOf t)) (μOf (sgOf cur) d) fun n => D (o + n)
  fr : ∀ i, j ≤ i → Ks.fr i = Kr.fr i + (shT p Kr D nx rest j cur next l o t Pr t₃ d).fr i
  new : ∀ i, j ≤ i →
    Ks.new i = addPS (Kr.new i) ((shT p Kr D nx rest j cur next l o t Pr t₃ d).new i)
  W : ∀ σ i, j < i → Ks.W σ i = Kr.W σ i + (shT p Kr D nx rest j cur next l o t Pr t₃ d).W σ i

section
variable {p : P12} {D : ℕ → Fmt.Drawn} {nx : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {j : ℕ}
  {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t t₃ : T12} {Kr Ks : BCoins} {Pr Ps d : PS}

theorem atSwitch_of_trees (hF : FitsBody D (next :: nx :: rest) cur o)
    (hA : AtStageT p D nx rest j cur next l o t t₃ Kr Ks Pr Ps d) :
    AtSwitchT p j cur next l o t Kr Ks Pr Ps d (rowOf t₃) D where
  st := hA.st
  foldW := hA.foldW
  fr := by
    have h := hA.fr j le_rfl
    have e : (shT p Kr D nx rest j cur next l o t Pr t₃ d).fr j =
        shFr p Kr j cur next l o t Pr D d := if_pos rfl
    rw [e] at h
    exact h
  new := by
    have h := hA.new j le_rfl
    have e : (shT p Kr D nx rest j cur next l o t Pr t₃ d).new j =
        shNewT p Kr j cur next l o t Pr (rowOf t₃) D d := if_pos rfl
    rw [e] at h
    exact h
  nextW := by
    have h := hA.W (sgOf next) (j + 1) (Nat.lt_succ_self j)
    have e : (shT p Kr D nx rest j cur next l o t Pr t₃ d).W (sgOf next) (j + 1) =
        shWT p Kr j cur next l o t Pr (rowOf t₃) D d (sgOf next) := if_pos rfl
    rw [e] at h
    exact h
  qC := (qNext_le hF.2.2.2.2).1
  qZ := (qNext_le hF.2.2.2.2).2

/-- **The library's `AtStage` holds in front of the next stage, at the letter t₃.** -/
theorem atStage_second (hF : FitsBody D (next :: nx :: rest) cur o)
    (hA : AtStageT p D nx rest j cur next l o t t₃ Kr Ks Pr Ps d) :
    AtStage p D (nx :: rest) (j + 1) next (l.drop (cur.k + 3)) (oNext cur o) t₃ Kr Ks
      (sNext Kr false j cur next o Pr (rowOf t) D) (sNext Ks false j cur next o Ps (rowOf t) D)
      (dNextT p Kr j cur next l o t Pr (rowOf t₃) D d)
      (sCol Kr false j cur next o Pr (rowOf t) D) (sCol Ks false j cur next o Ps (rowOf t) D) := by
  have hS := atSwitch_of_trees hF hA
  refine ⟨sNext_add_trees hS, fun x hx => sCol_same_trees hS hx, fun _ => ?_,
    fun hnil => absurd hnil (List.cons_ne_nil _ _), fun i hi => ?_, fun i hi => ?_,
    fun σ i hi => ?_⟩
  · rw [hS.nextW, muOf_dNext_trees]
    congr 1
    unfold shWT
    rw [if_pos rfl]
  · have h := hA.fr i (by omega)
    have e : (shT p Kr D nx rest j cur next l o t Pr t₃ d).fr i = _ :=
      if_neg (by omega : ¬ i = j)
    rw [e] at h
    exact h
  · have h := hA.new i (by omega)
    have e : (shT p Kr D nx rest j cur next l o t Pr t₃ d).new i = _ :=
      if_neg (by omega : ¬ i = j)
    rw [e] at h
    exact h
  · have h := hA.W σ i (by omega)
    have e : (shT p Kr D nx rest j cur next l o t Pr t₃ d).W σ i = _ :=
      if_neg (by omega : ¬ i = j + 1)
    rw [e] at h
    exact h

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.AtSwitchT
#print axioms ProofFile.Honest.K12.sRF_same_trees
#print axioms ProofFile.Honest.K12.sGam_same_trees
#print axioms ProofFile.Honest.K12.sT1_same_trees
#print axioms ProofFile.Honest.K12.sAns_same_trees
#print axioms ProofFile.Honest.K12.sRS_same_trees
#print axioms ProofFile.Honest.K12.sNext_add_trees
#print axioms ProofFile.Honest.K12.muOf_dNext_trees
#print axioms ProofFile.Honest.K12.sCol_same_trees
#print axioms ProofFile.Honest.K12.AtStageT
#print axioms ProofFile.Honest.K12.atSwitch_of_trees
#print axioms ProofFile.Honest.K12.atStage_second
