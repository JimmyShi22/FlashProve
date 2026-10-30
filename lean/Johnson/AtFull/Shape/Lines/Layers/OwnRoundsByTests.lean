-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/OwnRoundsByTests.lean: the cell of the layers' own rounds in the
table of steps on shapes (TabL.k4, Johnson/AtFull/Shape/TabLetters.lean) returns, and what it
returns is a written value but for the layers' parts (LayersPartsAside.lean in this folder). This
follows from thirteen tests, none of which is the cell's own step. General in the public
record, the group and the two shapes; nothing is evaluated.

Why. Lean's kernel is to show, Bool by Bool, that the run on shapes returns. The hearing inside this
cell is long. The laws of this folder give the shape after the cell in closed form; what is left to
evaluate are tests on the plan and comparisons of closed forms with a written value.

Main names.
* atPlan, atTables: a test at the group's plan; at the plan's array of the reads and its tables.
* planCovers to planJoin: ten tests that read no shape. PlanTests: all ten accept.
  planTest_of_tests: together they give the cell's own test on the plan (k4PlanB).
* ownRoundsGuardsTest: the cell's three guards that read the shape before it.
* mergeRecordsBorderTest: the list of what is left of each weight claim, made from the plan, agrees
  with the list that the written value holds.
* shapeAfterOwnRounds, afterOwnRoundsTest: the shape after the cell in closed form is the written
  value but for the layers' parts.
* ownRounds_given: where the thirteen accept, the cell returns some y, and y without the layers'
  parts is the written value.

Limits. Implications: no test is shown to accept. Of the parts that are set aside nothing is said
but that the cell returns a shape which has them. afterOwnRoundsTest takes the list of what is left
of each weight claim from the written value itself, so at that list it compares the value with
itself: mergeRecordsBorderTest alone speaks for the list. planCovers reads the layers' record and
not the group's plan: at each group it is one and the same test, with "a plan of group g is there".
planClaimEmbedding is the constant true after group 0, which alone has such a claim: there it says
only that a plan is there. Only at the layout yFull (premise hy). Nothing on soundness, completeness
or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.SecondTexts
import Johnson.AtFull.Shape.Lines.Layers.LayersPartsAside
import Johnson.AtFull.Shape.ShapeDecEqL

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Layers
open OnBytes OnBytes.Model OnBytes.Model.Layer
open Johnson.AtFull.Shape Johnson.AtFull.Shape.LayersPartsAside
open OnBytes.Road.K4.Trial.Values (yFull)
open OnBytes.Desc.First.K4 OnBytes.Desc.First.K4.Rt OnBytes.Desc.First.K4.RtPub
open VerifiableInference.Desc.First.Shape

/-- A test at the plan of group g; false where the record has no such plan. -/
def atPlan (X : Verify.Public) (g : Nat) (f : Par → Bool) : Bool :=
  (X.G[g]?).any fun hp => f (k4Par X hp g)

/-- Where the record has the plan hp at group g, a test at the plan is the test at hp. -/
theorem atPlan_at {X : Verify.Public} {g : Nat} {hp : HPlan2} {f : Par → Bool}
    (hG : X.G[g]? = some hp) (h : atPlan X g f = true) : f (k4Par X hp g) = true := by
  unfold atPlan at h
  rw [hG] at h
  exact h

/-- Where a test at the plan accepts, a plan is there. -/
theorem atPlan_plan {X : Verify.Public} {g : Nat} {f : Par → Bool} (h : atPlan X g f = true) :
    ∃ hp, X.G[g]? = some hp := by
  obtain ⟨hp, e, -⟩ := any_some h
  exact ⟨hp, e⟩

/-- A test at the plan's array of the reads and at the places of its tables. -/
def atTables (p : Par)
    (f : Nat → List TableAt × List (TableAsk × List (Nat × Nat)) × Nat → Bool) : Bool :=
  (p.hp.tl.ix.U.getD 2 none).any fun iU3 => (tablesAt p.P p.g).any fun r => f iU3 r

/-! ## The tests on the plan alone -/

/-- The record has a plan of group g, and the layers' record is of the kind for which the layers'
own rounds are written. The second clause does not read g. -/
def planCovers (g : Nat) (X : Verify.Public) : Bool := atPlan X g fun p => covers p.P

/-- The test on the plan's numbers. -/
def planNumbers (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => planNumsB p.P p.hp p.g

/-- The test on the points, at the families of tables that the plan places. -/
def planPoints (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => (tablesAt p.P p.g).any fun r => pointsB p.P p.g r.2.1

/-- The plan's list of tables is open, the tables end at the plan's length of the reads, and the
vocabulary is not empty. -/
def planSmall (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => p.hp.tl.funOpen && tablesB p.P p.hp p.g && decide (0 < p.P.V)

/-- The panels' test, in its second text. -/
def planPanels (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => atTables p fun iU3 r =>
    panelsTestSecondText.1 p.P (blankEnv p.P p.hp p.g iU3 r.1) p.hp.lamS (nclpOf p.hp p.g)

/-- The weight claims, counted with the embedding's claim in group 0, are as many as the plan's
number of claims, and that number is above 0 and at most 4096. -/
def planClaimsCount (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => atWeightClaimsSecondText p.P p.hp p.g fun cp =>
    cp.length + (if (p.g == 0) = true then 1 else 0) == p.hp.NCL && decide (0 < p.hp.NCL) &&
      decide (p.hp.NCL ≤ 4096)

/-- The tests on a weight claim, at the first half of the claims. -/
def planClaimsFirstHalf (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => atWeightClaimsSecondText p.P p.hp p.g fun cp =>
    (cp.take (p.hp.NCL / 2)).all (claimPassesMerge p.P.wsLay)

/-- The tests on a weight claim, at the other claims. -/
def planClaimsSecondHalf (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => atWeightClaimsSecondText p.P p.hp p.g fun cp =>
    (cp.drop (p.hp.NCL / 2)).all (claimPassesMerge p.P.wsLay)

/-- The test on the embedding's claim. Group 0 alone has such a claim: after it the test is the
constant true. -/
def planClaimEmbedding (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => embeddingClaimTest p.P p.hp p.g

/-- The join's test. -/
def planJoin (g : Nat) (X : Verify.Public) : Bool :=
  atPlan X g fun p => atTables p fun iU3 r => joinB p.P p.hp p.g iU3 r.1

/-- The ten tests on the plan accept at X. -/
structure PlanTests (g : Nat) (X : Verify.Public) : Prop where
  covers : planCovers g X = true
  numbers : planNumbers g X = true
  points : planPoints g X = true
  small : planSmall g X = true
  panels : planPanels g X = true
  claimsCount : planClaimsCount g X = true
  claimsFirstHalf : planClaimsFirstHalf g X = true
  claimsSecondHalf : planClaimsSecondHalf g X = true
  claimEmbedding : planClaimEmbedding g X = true
  join : planJoin g X = true

/-- **The ten give the cell's own test on the plan**, and that the vocabulary is not empty. -/
theorem planTest_of_tests {g : Nat} {X : Verify.Public} {hp : HPlan2} (hG : X.G[g]? = some hp)
    (T : PlanTests g X) : k4PlanB (k4Par X hp g) = true ∧ 0 < X.layers.V := by
  have h1 := atPlan_at hG T.covers
  have h2 := atPlan_at hG T.numbers
  have h3 := atPlan_at hG T.points
  have h4 := atPlan_at hG T.small
  have h5 := atPlan_at hG T.panels
  have h7 := atPlan_at hG T.join
  have h6 : claimsB (k4Par X hp g).P (k4Par X hp g).hp (k4Par X hp g).g = true :=
    claimsTest_ofSecondTextTests _ _ _ _ (atPlan_at hG T.claimsCount) (atPlan_at hG
        T.claimsFirstHalf)
      (atPlan_at hG T.claimsSecondHalf) (atPlan_at hG T.claimEmbedding)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
  obtain ⟨iU3, hu, h5'⟩ := any_some h5
  obtain ⟨⟨tab, laid, n⟩, ht, h5''⟩ := any_some h5'
  have hB : hearB (k4Par X hp g).P (k4Par X hp g).hp (k4Par X hp g).g = true :=
    hearB_of_parts hu h4.1.1 ht h4.1.2 (panelsTest_ofSecondText h5'') h6
  refine ⟨?_, h4.2⟩
  unfold k4PlanB hearPB
  rw [h1, h2, hB, h3]
  exact h7

/-! ## The tests that read the shape before the cell, and the written value after it -/

/-- The cell's three guards that read the shape before it. -/
def ownRoundsGuardsTest (g : Nat) (X : Verify.Public) (x : ShA) : Bool :=
  atPlan X g fun p =>
    Johnson.AtFull.Shape.noneWaitsSh x.1 && !x.1.marked && k4FrontB p 0 x.1

/-- The list of what is left of each weight claim, as a written value holds it; the empty list where
the value has no component own. -/
def writtenMergeRecords (c : ShA) : List RecSh := (c.1.own.map fun o => o.wo.recs).getD []

/-- The list of what is left of each weight claim, made from the plan, agrees with the list that the
written value holds. -/
def mergeRecordsBorderTest (g : Nat) (X : Verify.Public) (c : ShA) : Bool :=
  atPlan X g fun p => mergeRecordsTest p.P p.hp p.g (writtenMergeRecords c)

/-- The chain's shape after the cell, in closed form, with what stays of the component own. -/
def shapeAfterOwnRounds (p : Par) (a : ChainSh) (h : HeardAll) (L : LedSh) (iU3 : Nat)
    (tab : List TableAt) (laid : List (TableAsk × List (Nat × Nat))) (recs : List RecSh) :
    ChainSh :=
  (((a.setLed (hearLedU p.P p.hp p.g L)).layOwn (some (ownRecordClosedForm p.P p.hp p.g iU3 tab h
      L.next
    (L.next + k4Takes p.P p.hp p.g) recs))).layTables (some (tableShapesClosedForm p.P.y h
        laid))).setRowsOwed
      none

/-- That shape, without the layers' parts, is the written value. The list of what is left of each
weight claim is taken from the written value itself. -/
noncomputable def afterOwnRoundsTest (g : Nat) (X : Verify.Public) (x c : ShA) : Bool :=
  atPlan X g fun p => atTables p fun iU3 r =>
    match x.1.look, x.1.led with
    | some h, some L =>
      @decide
        (lessLayersParts
          (shapeAfterOwnRounds p x.1 h L iU3 r.1 r.2.1 (writtenMergeRecords c), x.2) = c)
        (ByLists.decShAL _ _)
    | _, _ => false

/-- Taking the parts out of the component own a second time changes nothing. -/
theorem ownRecordLessParts_twice (ow : OwnSh) : ownRecordLessParts (ownRecordLessParts ow) =
    ownRecordLessParts ow := by
  obtain ⟨g, iU3, K3, tab, zk, H, K, hd, hd2, sVE, wo⟩ := ow
  obtain ⟨fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV, tT, KT⟩ := H
  cases tT <;> rfl

/-- The shape after the cell without the layers' parts, field by field, against a tuple that is
written out. -/
theorem chainWithLayersParts_afterOwnRounds (a0 : Bool) (a1 : Nat) (a2 : Option TailSh)
    (a3 : Option LedSh) (a4 : Option (List FunSh)) (a5 : Option Nat)
    (a6 : VerifiableInference.Desc.Ground.Sh.CoreSh) (a7 : Bool) (a8 : Nat)
    (a9 : List VerifiableInference.Desc.K13.Honest.RowSh) (a10 : Option EndSh) (a11 : CheckSh)
    (a12 : Option LinkSh) (a13 a14 : Option HeardAll) (a15 : Option OwnSh) (a16 : Option HeadSh)
    (a17 : Option AttOwnSh) (a18 : Option FinSh) (l : LedSh) (o : OwnSh)
    (t : Option (List FunSh)) :
    chainWithLayersParts ((((ChainSh.setLed (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18) l).layOwn (some o)).layTables t).setRowsOwed none)
      noLayersParts =
      (a0, a1, a2, a3.map fun _ => l, t, none, a6, a7, a8, a9, a10, a11, a12,
        a13.map fun h => lookupRecordWithParts h (noLayersParts.1.getD (#[], [])),
        a14.map fun h => lookupRecordWithCalls h (noLayersParts.2.1.getD #[]),
        some (ownRecordLessParts o), a16, a17, a18) := rfl

/-- Without the layers' parts it does not matter whether the component own or what stays of it is
laid. -/
theorem lessLayersParts_layOwn (a : ChainSh) (l : LedSh) (ow : OwnSh) (t : Option (List FunSh))
    (F : FormsSh) :
    lessLayersParts ((((a.setLed l).layOwn (some ow)).layTables t).setRowsOwed none, F) =
      lessLayersParts
        ((((a.setLed l).layOwn (some (ownRecordLessParts ow))).layTables t).setRowsOwed none,
          F) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := a
  show (chainWithLayersParts _ noLayersParts, F) = (chainWithLayersParts _ noLayersParts, F)
  rw [chainWithLayersParts_afterOwnRounds, chainWithLayersParts_afterOwnRounds,
    ownRecordLessParts_twice]

/-- **The cell returns, and what it returns is the written value but for the layers' parts.** -/
theorem ownRounds_given {X : Verify.Public} (hy : X.layers.y = yFull) {g : Nat}
    (T : PlanTests g X) {x c : ShA} (hF : ownRoundsGuardsTest g X x = true)
    (hR : mergeRecordsBorderTest g X c = true) (hB : afterOwnRoundsTest g X x c = true) :
    ∃ y, (TabL.k4 (LWn X) g).1 x = .ok y ∧ lessLayersParts y = c := by
  obtain ⟨hp, hG⟩ := atPlan_plan hF
  obtain ⟨hP, hV⟩ := planTest_of_tests hG T
  have hF' := atPlan_at hG hF
  have hR' := atPlan_at hG hR
  have hB' := atPlan_at hG hB
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hF'
  obtain ⟨⟨f1, f2⟩, f3⟩ := hF'
  obtain ⟨iU3, hu, hB1⟩ := any_some hB'
  obtain ⟨⟨tab, laid, n⟩, ht, hB2⟩ := any_some hB1
  have hL : VerifiableInference.Desc.First.Look.laidLayers (k4Par X hp g).P =
      some (k4Par X hp g).P.y.fo.pub := eq_of_beq (laidLayersTest_atFullLayout hy)
  split at hB2
  · rename_i h L hlook hled
    obtain ⟨iU3', tab', laid', n', ow, recs, hu', ht', hr', hk, hs⟩ :=
      ownRoundsStep_closedForm (k4Par X hp g) hlook hled hP hL f3 hV
    obtain rfl : iU3 = iU3' := Option.some.inj (hu.symm.trans hu')
    obtain ⟨rfl, rfl, rfl⟩ : tab = tab' ∧ laid = laid' ∧ n = n' := by
      have e := Option.some.inj (ht.symm.trans ht')
      exact ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
    obtain rfl : writtenMergeRecords c = recs :=
      Option.some.inj ((mergeRecords_ofTest hR').symm.trans hr')
    refine ⟨((((x.1.setLed (hearLedU (k4Par X hp g).P (k4Par X hp g).hp (k4Par X hp g).g L)).layOwn
      (some ow)).layTables (some (tableShapesClosedForm (k4Par X hp g).P.y h laid))).setRowsOwed
          none, x.2),
      ?_, ?_⟩
    · have hG' : (LWn X).XG.G[g]? = some hp := hG
      unfold TabL.k4
      rw [hG']
      refine liftO_ok.2 ⟨_, ?_, rfl⟩
      have hpub : (LWn X).k4pub g = true := by
        show k4pubX X g = true
        unfold k4pubX
        rw [hG]
        show k4PubB (k4Par X hp g) = true
        unfold k4PubB
        rw [hP, Bool.true_and]
        exact laidLayersTest_atFullLayout hy
      show k4StepL ((LWn X).k4pub g) ((LWn X).k4own g) (k4Par X hp g) x.1 = _
      unfold k4StepL
      rw [if_pos f1, f2, hpub, f3, ownRoundsLetter_atNumerals X g hG, ← k4G_eq]
      exact hk
    · rw [lessLayersParts_layOwn, hs]
      exact @of_decide_eq_true _ (ByLists.decShAL _ _) hB2
  · cases hB2

end Johnson.AtFull.Shape.Layers

#print axioms Johnson.AtFull.Shape.Layers.atPlan_at
#print axioms Johnson.AtFull.Shape.Layers.atPlan_plan
#print axioms Johnson.AtFull.Shape.Layers.planTest_of_tests
#print axioms Johnson.AtFull.Shape.Layers.ownRecordLessParts_twice
#print axioms Johnson.AtFull.Shape.Layers.chainWithLayersParts_afterOwnRounds
#print axioms Johnson.AtFull.Shape.Layers.lessLayersParts_layOwn
#print axioms Johnson.AtFull.Shape.Layers.ownRounds_given
