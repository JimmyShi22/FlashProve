-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Induct.lean: under premises on sizes and on the two runs, two runs of the
link prover's algorithm agree stage after stage, except one element; proved by induction.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Fix the parameters p and the verifier challenges D. Take two runs of the link
prover's algorithm from the same stage of its proximity test onwards (bodyAll,
Johnson/Prover/Link/BodyAll.lean). The honest run has coins Kr and prover state Pr; the other run
has coins Ks and state Ps. AtStage (Johnson/LinkSim/AtText/SpecStage.lean, whose head lists its
fields) says how they relate in front of the stage: among other things, both runs have one verifier
state, their prover states differ by d, and every later coin differs by the shift shB
(Johnson/LinkSim/AtText/ShiftDefs.lean). In LinkShift.lean the other run is the run at data 0
(zeroIn X) with the shifted coins, from which the simulator's output is made.
  bodyShiftOr   proves Spec.bodyShiftOr (Johnson/LinkSim/AtText/SpecShiftIn.lean). Assume the sizes
      fit (FitsBody) and AtStage holds. Assume also that the element sampled in the first round of
      the base case is 0 (LamZero), or that the claim left at the base case is true at the honest
      run's last message (ClaimTrue). Then the two runs have the same groups of opened columns.
      Their lists of rounds are equal except at one entry: where the other run has its own
      first-round element of the base case, the honest run has tauStar, computed from the other
      run (Johnson/LinkSim/AtText/Defs.lean).
  bodyShift     proves Spec.bodyShift (SpecStage.lean): the same with the premise ClaimTrue alone.
      It is the second case of bodyShiftOr.
  walkSame      proves Spec.walkSame (SpecStage.lean). Under FitsBody and AtStage alone, the shift
      shB computed along the other run equals the shift computed along the honest run. This is
      what lets the shift be recovered from the shifted coins.
All three hold for all parameters, all challenges D and every list of stages.

How it fits. The step from one stage to the next is Step.lean (the runs) and Walk.lean (the shift);
the last stage is LastStep.lean and LastStepOr.lean. LinkShift.lean uses bodyShiftOr, walkSame and
bodyEnd_o to prove Spec.linkShiftIn and Spec.linkShift; linkShiftIn is used in the proof of
homeExact (Johnson/LinkSim/AtHome/Home.lean). Under Johnson/LinkSim/ no file uses bodyShift.

Other names.
  atSwitch_of    under FitsBody, if AtStage holds in front of a stage that is not the last, the
                 premises of one switch (AtSwitch, Step.lean) hold there.
  atStage_next   under the same premises, AtStage holds in front of the next stage, with the next
                 states, difference, columns and verifier state.
  bodyEnd_o      the last stage's first round has a round number no smaller than o, the stage in
                 hand's.

Limits. Those of Spec.bodyShiftOr, Spec.bodyShift and Spec.walkSame stand once, in the heads of
SpecStage.lean and SpecShiftIn.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Walk
import Johnson.LinkSim.AtText.LastStepOr
import Johnson.LinkSim.AtText.PlacesProof

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link

variable {p : P12} {D : ℕ → Fmt.Drawn} {rest : List Fmt.M1.Stage} {j : ℕ}
  {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12} {Kr Ks : BCoins} {Pr Ps d : PS}
  {colr cols : ℕ → List UInt64}

/-- Under FitsBody, if AtStage holds in front of a stage that is not the last, AtSwitch holds at
its switch. -/
theorem atSwitch_of (hF : FitsBody D (next :: rest) cur o)
    (hA : AtStage p D (next :: rest) j cur l o t Kr Ks Pr Ps d colr cols) :
    AtSwitch p rest.isEmpty j cur next l o t Kr Ks Pr Ps d colr cols D where
  st := hA.st
  col := hA.col
  foldW := hA.foldW (List.cons_ne_nil _ _)
  fr := by
    have h := hA.fr j le_rfl
    have e : (shB p Kr D (next :: rest) j cur l o t Pr colr d).fr j =
        shFr p Kr j cur next l o t Pr D d := if_pos rfl
    rw [e] at h
    exact h
  new := by
    have h := hA.new j le_rfl
    have e : (shB p Kr D (next :: rest) j cur l o t Pr colr d).new j =
        shNew p Kr rest.isEmpty j cur next l o t Pr colr D d := if_pos rfl
    rw [e] at h
    exact h
  nextW := fun hl => by
    have h := hA.W (sgOf next) (j + 1) (Nat.lt_succ_self j)
    have e : (shB p Kr D (next :: rest) j cur l o t Pr colr d).W (sgOf next) (j + 1) =
        shWAt p Kr rest.isEmpty j cur next l o t Pr colr D d (sgOf next) := by
      show (if j + 1 = j + 1 then
        (if rest.isEmpty then 0
          else shWAt p Kr rest.isEmpty j cur next l o t Pr colr D d (sgOf next))
        else _) = _
      rw [if_pos rfl, hl]
      rfl
    rw [e] at h
    exact h
  qC := (qNext_le hF.2.2.2.2).1
  qZ := (qNext_le hF.2.2.2.2).2

/-- Under FitsBody, if AtStage holds in front of a stage that is not the last, it holds in front
of the next stage. -/
theorem atStage_next (hF : FitsBody D (next :: rest) cur o)
    (hA : AtStage p D (next :: rest) j cur l o t Kr Ks Pr Ps d colr cols) :
    AtStage p D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
      (tNext p Kr rest.isEmpty j cur next l o t Pr colr D) Kr Ks
      (sNext Kr rest.isEmpty j cur next o Pr (rowOf t) D)
      (sNext Ks rest.isEmpty j cur next o Ps (rowOf t) D)
      (dNext p Kr rest.isEmpty j cur next l o t Pr colr D d)
      (sCol Kr rest.isEmpty j cur next o Pr (rowOf t) D)
      (sCol Ks rest.isEmpty j cur next o Ps (rowOf t) D) := by
  have hS := atSwitch_of hF hA
  refine ⟨sNext_add hS, fun x hx => sCol_same hS hx, fun hne => ?_, fun hnil => ?_,
    fun i hi => ?_, fun i hi => ?_, fun σ i hi => ?_⟩
  · have hl : rest.isEmpty = false := by
      cases rest with
      | nil => exact absurd rfl hne
      | cons _ _ => rfl
    rw [hS.nextW hl, muOf_dNext]
    congr 1
    unfold shWAt
    rw [if_pos rfl]
  · subst hnil
    refine ⟨fun i => ?_, fun q => ?_, fun i => ?_, fun q => ?_⟩
    · rw [muOf_dNext]
      rfl
    · rfl
    · rw [muOf_dNext]
      rfl
    · rfl
  · have h := hA.fr i (by omega)
    have e : (shB p Kr D (next :: rest) j cur l o t Pr colr d).fr i = _ :=
      if_neg (by omega : ¬ i = j)
    rw [e] at h
    exact h
  · have h := hA.new i (by omega)
    have e : (shB p Kr D (next :: rest) j cur l o t Pr colr d).new i = _ :=
      if_neg (by omega : ¬ i = j)
    rw [e] at h
    exact h
  · have h := hA.W σ i (by omega)
    have e : (shB p Kr D (next :: rest) j cur l o t Pr colr d).W σ i = _ :=
      if_neg (by omega : ¬ i = j + 1)
    rw [e] at h
    exact h

/-- The round number at which the last stage begins is at least o. -/
theorem bodyEnd_o (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64),
    o ≤ (bodyEnd p K D rest j cur l o t P col).o
  | [], _, _, _, _, _, _, _ => le_rfl
  | _ :: rest, _, _, _, _, _, _, _ =>
    le_trans (by omega) (bodyEnd_o p K D rest _ _ _ _ _ _ _)

/-- Proves Spec.bodyShiftOr: from this stage on, the two runs have the same groups of opened
columns, and the same rounds except the base case's first-round element, which is tauStar. -/
theorem bodyShiftOr : Spec.bodyShiftOr := by
  intro p D rest
  induction rest with
  | nil =>
    intro j cur l o t Kr Ks Pr Ps d colr cols _ hA hcl
    have h := lastOut_same_or (p := p) (j := j) (l := l) (t := t) hA.st (hA.word rfl) hA.col hcl
    refine ⟨h.1, ?_⟩
    show (lastOut p j cur o t Pr colr (rowOf t) D).rs =
      (lastOut p j cur o t Ps cols (rowOf t) D).rs.set (o - o) _
    rw [Nat.sub_self]
    exact h.2
  | cons next rest ih =>
    intro j cur l o t Kr Ks Pr Ps d colr cols hF hA hcl
    have hS := atSwitch_of hF hA
    have hi := ih (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
      (tNext p Kr rest.isEmpty j cur next l o t Pr colr D) Kr Ks _ _ _ _ _ hF.2.2.2.2
      (atStage_next hF hA) hcl
    have hT : sT3 p Ks rest.isEmpty j cur next l o t Ps cols (rowOf t) D =
        tNext p Kr rest.isEmpty j cur next l o t Pr colr D := (sT3_same hS).symm
    have hge : o + ((sgOf cur).h + (sgOf cur).g) + 3 ≤
        (bodyEnd p Ks D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
          (tNext p Kr rest.isEmpty j cur next l o t Pr colr D)
          (sNext Ks rest.isEmpty j cur next o Ps (rowOf t) D)
          (sCol Ks rest.isEmpty j cur next o Ps (rowOf t) D)).o :=
      bodyEnd_o p Ks D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
        (tNext p Kr rest.isEmpty j cur next l o t Pr colr D)
        (sNext Ks rest.isEmpty j cur next o Ps (rowOf t) D)
        (sCol Ks rest.isEmpty j cur next o Ps (rowOf t) D)
    have hE : bodyEnd p Ks D (next :: rest) j cur l o t Ps cols =
        bodyEnd p Ks D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
          (tNext p Kr rest.isEmpty j cur next l o t Pr colr D)
          (sNext Ks rest.isEmpty j cur next o Ps (rowOf t) D)
          (sCol Ks rest.isEmpty j cur next o Ps (rowOf t) D) := by
      show bodyEnd p Ks D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
        (sT3 p Ks rest.isEmpty j cur next l o t Ps cols (rowOf t) D) _ _ = _
      rw [hT]
    constructor
    · show sGS cur o colr D ++ _ = sGS cur o cols D ++
        (bodyAll p Ks rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
          (sT3 p Ks rest.isEmpty j cur next l o t Ps cols (rowOf t) D) _ _ D).gs
      rw [sGS_same hS, hT]
      exact congrArg _ hi.1
    · rw [hE]
      show sRF Kr j cur o Pr (rowOf t) D ++ sRS p Kr j cur next l o t Pr (rowOf t) D ++ _ =
        (sRF Ks j cur o Ps (rowOf t) D ++ sRS p Ks j cur next l o t Ps (rowOf t) D ++
          (bodyAll p Ks rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
            (sT3 p Ks rest.isEmpty j cur next l o t Ps cols (rowOf t) D) _ _ D).rs).set _ _
      rw [sRF_same hS, sRS_same hS, hT]
      have hlen : (sRF Ks j cur o Ps (rowOf t) D ++
          sRS p Ks j cur next l o t Ps (rowOf t) D).length =
          (sgOf cur).h + (sgOf cur).g + 3 := by
        rw [List.length_append]
        unfold sRF
        rw [length_foldRV]
        show _ + 2 = _
        omega
      rw [List.set_append_right _ _ (by rw [hlen]; omega), hlen]
      refine congrArg _ ?_
      have e : ∀ n : ℕ, n - o - ((sgOf cur).h + (sgOf cur).g + 3) = n - oNext cur o := fun n => by
        show _ = n - (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        omega
      rw [e]
      exact hi.2

/-- Proves Spec.bodyShift, as the case ClaimTrue of bodyShiftOr. -/
theorem bodyShift : Spec.bodyShift :=
  fun p D rest j cur l o t Kr Ks Pr Ps d colr cols hF hA hcl =>
    bodyShiftOr p D rest j cur l o t Kr Ks Pr Ps d colr cols hF hA (Or.inr hcl)

/-- Proves Spec.walkSame: the shift shB computed along the other run equals the one computed
along the honest run. -/
theorem walkSame : Spec.walkSame := by
  intro p D rest
  induction rest with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | cons next rest ih =>
    intro j cur l o t Kr Ks Pr Ps d colr cols hF hA
    have hS := atSwitch_of hF hA
    have hi := ih (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
      (tNext p Kr rest.isEmpty j cur next l o t Pr colr D) Kr Ks _ _ _ _ _ hF.2.2.2.2
      (atStage_next hF hA)
    unfold shB
    rw [walk_tNext hS, walk_dNext hS, hi, walk_shNew hS, walk_shFr hS]
    simp only [walk_shWAt hS]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.bodyShiftOr
#print axioms OnBytes.LinkSim.AtText.bodyShift
#print axioms OnBytes.LinkSim.AtText.walkSame
