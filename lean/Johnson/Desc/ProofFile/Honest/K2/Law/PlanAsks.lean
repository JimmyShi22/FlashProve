-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlanAsks.lean: the kind "the code switch" (K2): THE PUBLIC
PREMISES OF THE KIND's LAWS ON THE SENDER, AS NAMED TESTS WITH CODE, PLACE BY PLACE OVER THE KIND's
LOT: the switch's own sending passes the shared sending's public test (`K1.sendFits`,
Honest/K1/Coins.lean); its fresh mask has one row; every message of it with a main row is sampled
(`noWord`, Honest/K2/Law/Counts.lean). Definitions; statements with their proofs.

  `placeFits`, `placeOneRow`   the first two tests at one place
  `placeAsks`    the three tests at one place, each under a name that tells the group into which the
                 switch leads; the second's name tells the fresh mask's number of rows too
  `switchPlanAsks`   for whoever evaluates at a policy file: ONE TERM: "the lot has a place", then
                 `placeAsks` at each place of the lot (`switchPlaces`, Honest/K2/Half.lean), of the
                 public part and the segments' records
  `placeOneRow_yes`   a yes of the second test gives `ExactAsks.oneRow` (Honest/K2/Exact.lean) in
                 its very words. (`placeFits p = true` IS `ExactAsks.fits`, as it stands.)
  `switchPlanAsks_facts`   where every named test says yes: the lot has a place, and at each place
                 the three premises hold

Limits. The tests are evaluated nowhere here. No theorem here draws the first two from the request's
own public tests; the third is a theorem wherever the proof file's description is returned
(Honest/K2/Law/SampledOpen.lean): here it is asked again, as a test. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2

/-- At one place: the switch's own sending passes the shared sending's public test. -/
def placeFits (p : SwitchPlace) : Bool :=
  K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others))
    (rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars))

/-- At one place: the fresh mask that rides has one mask row. -/
def placeOneRow (p : SwitchPlace) : Bool :=
  (switchFresh p.sizes p.others p.foldVars).all fun x =>
    ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows == 1

/-- The three tests at one place, by name. -/
def placeAsks (p : SwitchPlace) : List (String × Bool) :=
  [("K2, into group " ++ toString p.link ++ ": the sending passes the shared sending's test",
      placeFits p),
    ("K2, into group " ++ toString p.link ++ ": the fresh mask has one row (it has " ++
      toString ((switchFresh p.sizes p.others p.foldVars).map fun x =>
        ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows).toList ++ ")",
      placeOneRow p),
    ("K2, into group " ++ toString p.link ++ ": every message with a main row is sampled",
      noWord (switchSent p.sizes p.others))]

/-- **All named tests of the kind's lot.** -/
def switchPlanAsks (Z : Pub) (G : Ground) : List (String × Bool) :=
  ("K2: the lot has a place (it has " ++ toString (switchPlaces Z G).length ++ ")",
    decide (0 < (switchPlaces Z G).length)) :: (switchPlaces Z G).flatMap placeAsks

theorem placeOneRow_yes {p : SwitchPlace} (h : placeOneRow p = true) :
    ∀ x ∈ switchFresh p.sizes p.others p.foldVars,
      ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows = 1 := by
  intro x hx
  unfold placeOneRow at h
  rw [Option.mem_def.1 hx] at h
  exact beq_iff_eq.1 h

/-- **Where every named test says yes.** -/
theorem switchPlanAsks_facts {Z : Pub} {G : Ground}
    (h : ∀ t ∈ switchPlanAsks Z G, t.2 = true) :
    0 < (switchPlaces Z G).length ∧ ∀ p ∈ switchPlaces Z G,
      K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others))
          (rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) = true ∧
        (∀ x ∈ switchFresh p.sizes p.others p.foldVars,
          ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows = 1) ∧
        NoWord (switchSent p.sizes p.others) := by
  refine ⟨of_decide_eq_true (h _ List.mem_cons_self), fun p hp => ?_⟩
  have hm : ∀ t ∈ placeAsks p, t.2 = true := fun t ht =>
    h t (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨p, hp, ht⟩))
  exact ⟨hm _ List.mem_cons_self,
    placeOneRow_yes (hm _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    noWord_yes (hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.placeOneRow_yes
#print axioms ProofFile.Honest.K2.switchPlanAsks_facts
#print axioms ProofFile.Honest.K2.placeFits
#print axioms ProofFile.Honest.K2.placeOneRow
#print axioms ProofFile.Honest.K2.placeAsks
#print axioms ProofFile.Honest.K2.switchPlanAsks
