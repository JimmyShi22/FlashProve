-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormCuts.lean: THE FORM's HALF: THE FRAME's CUTS FOR THE BATCHING AND FOR EVERY
FOLD PASS batCut AND foldCut (Johnson/Prover/Link/FormBat.lean, FormFold.lean): from the proximity
test's block's own test on the plan; stage by stage, in the frame's letters; at the typed parameters
frP.

Main names.
  foldCuts_step   one stage of foldCuts: the fold's cut; behind the stage's rounds foldCuts again.
  cuts_top        the top, at any place.
  cuts_of_desc    general in the link's parameters, from the description's tests on the plan.
  own_full, cuts_full   at frP.
  samples_full    the setting's number «samples» is 1 at frP.

How. foldCuts_of_nums (FormFoldPlan.lean), batCut_of_nums (FormBatLaws.lean); K12.k12_rounds
(Johnson/Desc/K12/FrameLaws.lean) and H2K.Sw.k12_rounds (Johnson/Desc/K12/Law/StepGroups.lean);
open_top (Johnson/Desc/K12/OpenLaws.lean), test_planOk (Johnson/Desc/K15/HsemOf.lean), descV_planOk
(Johnson/Desc/K15/SendOwnLaw.lean), planOk_full (Johnson/Desc/Link/LinkWrittenMade.lean). ONE RUN OF
THE KERNEL's decide: own_full.

Limits. Where the masks come early alone (ownMask = false).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFoldPlan
import Johnson.Prover.Link.FormBatLaws
import Johnson.Desc.K15.HsemOf
import Johnson.Desc.K12.OpenLaws
import Johnson.Desc.K15.SendOwnLaw
import Johnson.Desc.Link.LinkWrittenMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK (laidOf laidS)
open Desc.K15 (P15 frP p12Of linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)

/-- **One stage of foldCuts, in the frame's letters.** -/
theorem foldCuts_step (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (h : foldCuts cur (next :: rest) (l.map (·.1)) = true) :
    foldCut cur.k ((l.take (1 + cur.k)).map (·.1)) = true ∧
      foldCuts next rest ((l.drop (cur.k + 3)).map (·.1)) = true := by
  unfold foldCuts at h
  rw [Bool.and_eq_true] at h
  rw [List.map_take, List.map_drop]
  exact h

/-- **The top, at any place.** -/
theorem cuts_top (p : P12) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (ho : p.nums.ownMask = false)
    (hs : p.nums.stages = first :: rest) :
    batCut (((laidOf p).take 1).map (·.1)) = true ∧
      (∀ d ∈ ((laidOf p).take 1).map (·.1), d.entry.rows = p.nums.rows) ∧
      foldCuts first rest ((laidS p).map (·.1)) = true := by
  have h1 := K12.k12_rounds guardedProximityTestParts p hp
  rw [H2K.Sw.k12_rounds guardedProximityTestParts p hp] at h1
  cases hl : (laidOf p).map (·.1) with
  | nil =>
    rw [hl] at h1
    cases rest with
    | nil => simp [H2U.roundsOfNums, hs] at h1
    | cons next rest =>
      have := entries_of_nums p.nums first next rest [] ho hs h1
      simp at this
  | cons d0 ds =>
    rw [hl] at h1
    obtain ⟨b1, b2⟩ := batCut_of_nums p.nums d0 ds h1
    have e1 : ((laidOf p).take 1).map (·.1) = [d0] := by rw [List.map_take, hl]; rfl
    have e2 : (laidS p).map (·.1) = ds := by
      unfold laidS
      rw [List.map_drop, hl]
      rfl
    rw [e1, e2]
    exact ⟨b1, fun d hd => by rw [List.mem_singleton.1 hd]; exact b2,
      foldCuts_of_nums p.nums first rest d0 ds ho hs h1⟩

/-- General in the link's parameters. -/
theorem cuts_of_desc (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (first : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (h : (linkDescriptionAt P plan ok).planOk = true)
    (ho : (p12Of P).nums.ownMask = false) (hs : (p12Of P).nums.stages = first :: rest) :
    batCut (((laidOf (p12Of P)).take 1).map (·.1)) = true ∧
      (∀ d ∈ ((laidOf (p12Of P)).take 1).map (·.1), d.entry.rows = (p12Of P).nums.rows) ∧
      foldCuts first rest ((laidS (p12Of P)).map (·.1)) = true :=
  cuts_top (p12Of P) first rest
    (Desc.K15.test_planOk P plan ok (Desc.K15.descV_planOk P plan ok h)) ho hs

/-- At the typed parameters the masks come early. -/
theorem own_full : (p12Of frP).nums.ownMask = false := by decide +kernel

/-- **AT THE COPY's FILE's OWN PLAN.** -/
theorem cuts_full : (p12Of frP).nums.ownMask = false ∧
    ∃ first rest, (p12Of frP).nums.stages = first :: rest ∧
      batCut (((laidOf (p12Of frP)).take 1).map (·.1)) = true ∧
      (∀ d ∈ ((laidOf (p12Of frP)).take 1).map (·.1), d.entry.rows = (p12Of frP).nums.rows) ∧
      foldCuts first rest ((laidS (p12Of frP)).map (·.1)) = true := by
  refine ⟨own_full, ?_⟩
  obtain ⟨first, rest, _, hs, _⟩ := open_top guardedProximityTestParts (p12Of frP)
    (Desc.K15.test_planOk frP _ _ (Desc.K15.descV_planOk frP _ _ Desc.K15.planOk_full))
  exact ⟨first, rest, hs, cuts_of_desc frP _ _ first rest Desc.K15.planOk_full own_full hs⟩

/-- The setting's number «samples» is 1 at the typed parameters. -/
theorem samples_full : frP.set.samples = 1 := rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.foldCuts_step
#print axioms Johnson.Prover.Link.cuts_top
#print axioms Johnson.Prover.Link.cuts_of_desc
#print axioms Johnson.Prover.Link.own_full
#print axioms Johnson.Prover.Link.cuts_full
#print axioms Johnson.Prover.Link.samples_full
