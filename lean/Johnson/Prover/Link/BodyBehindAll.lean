-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyBehindAll.lean: behind a proximity test's first stage, whatever trees its
group's members stand in, the invariant of the induction over the stages (`BodyInv`,
Johnson/Prover/Link/BodyInv.lean) holds at the next stage: ONE STATEMENT, at a list of further
stages that is a letter.

Main names (namespace `Johnson.Prover.Link`).
  `FirstSwitchPlan`   what is public at the first switch: `LastSwitchPlan`
      (Johnson/Prover/Link/LastBehindAny.lean) where no further stage follows the next one,
      `SwitchPlan` (Johnson/Prover/Link/FormBehindAny.lean) else
  `bodyInv_first_all`   by cases: `bodyInv_first_last` (Johnson/Prover/Link/LastBehindFirst.lean),
      `bodyInv_first` (Johnson/Prover/Link/BodyBehindFirst.lean)

Limits. Those of the two statements that it calls: every premise is asked; AT A FIRST STAGE WHOSE
MEMBERS STAND IN SEVERAL TREES NOTHING HERE MEETS THEM. Nothing on soundness; nothing on what a
shown value shows or does not show.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyBehindFirst
import Johnson.Prover.Link.LastBehindFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- What is public at the first switch, by whether a further stage follows the next one. -/
def FirstSwitchPlan (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (n : IoppStage) :
    List Fmt.M1.Stage → Prop
  | [] => LastSwitchPlan p K j cur next n
  | _ :: _ => SwitchPlan p K j cur next n

/-- **The joint, at every list of further stages.** -/
theorem bodyInv_first_all (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (a next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (trees : List ProofFile.Honest.K12.Tree) (D : ℕ → Fmt.Drawn) (n : IoppStage) (gp : ℕ)
    (rows : SingleRows) (Y : FirstYes p K rest j a next l o t P trees D)
    (Pl : FirstSwitchPlan p (t1At p K j a l o t P D).st.codes j a next n rest)
    (In : SwitchIn p j a next n gp (t1At p K j a l o t P D) rows
      (noDigest ⟨[.answer (ofE (aAns p j a next o D (t1At p K j a l o t P D)
        (qAt K rest j a next o P D)))], D (o + 2 + ((sgOf a).h + (sgOf a).g))⟩))
    (hPlan : PlanAll p rest (j + 1) next (l.drop (a.k + 3)) (t1At p K j a l o t P D).st.codes)
    (hF : FitFrom D (l.drop (a.k + 3)) (o + ((sgOf a).h + (sgOf a).g) + 3)) :
    ClaimTrue (sgOf next) (t3At p K rest j a next l o t P trees D) (qAt K rest j a next o P D) →
      BodyInv p K (PlanAll p) D rest (j + 1) next (l.drop (a.k + 3))
        (o + ((sgOf a).h + (sgOf a).g) + 3) (t3At p K rest j a next l o t P trees D)
        (qAt K rest j a next o P D) (aCol rest.isEmpty next (qAt K rest j a next o P D)) := by
  cases rest with
  | nil => exact bodyInv_first_last p K j a next l o t P trees D n gp rows Y Pl In hPlan hF
  | cons nx rest' =>
    exact bodyInv_first p K nx rest' j a next l o t P trees D n gp rows Y Pl In hPlan hF

end Johnson.Prover.Link
