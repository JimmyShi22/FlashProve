-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/SecondTexts.lean: second texts of four of the library's
definitions, each with the proof that the two are equal at all arguments, made by delta and simp
and closed by rfl; then what a closed Bool says of a second text, carried to what a law's premise
says of the library's text. General; nothing is evaluated.

Why. Some terms are hard for Lean's kernel as the library writes them: List.mergeSort does not
reduce there (Johnson/Unfolds/MergeSort.lean), and whether an entry of an equality table is there
need not make the table. A second text says the same without these.

  panelsTestSecondText, factorAtBitsSecondText, factorOfSegmentSecondText, weightClaimsSecondText
                          pairs of a second text and its tie to pansB, ClaimEnv.facRs,
                          ClaimEnv.facEw and ClaimEnv.weightClaims.
  equalityTable_getOption   an entry of the equality table, asked with «?».
  atWeightClaimsSecondText, mergeRecordsShapesSecondText   atWeightClaims
                          (WeightClaimsTests.lean) and mergeRecordsShapes
                          (MergeRecordsClosedForm.lean) with the weight claims in their second text.
  panelsTest_ofSecondText, **claimsTest_ofSecondTextTests**   the library's tests from closed Bools
                          on the second texts.
  mergeRecordsTest, **mergeRecords_ofTest**   the list of what the merge leaves of each weight
                          claim, from one closed Bool against a written list.

Limits. Equations of terms. The second texts can be read nowhere here: `#print` shows them. What
either text costs is not said. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.YesAtZFullN
import Johnson.Unfolds.MergeSort
import OnBytes.Flat.PendingSizes
import Johnson.AtFull.Shape.TabLight
import Johnson.AtFull.Shape.Lines.Layers.OwnRoundsStepClosedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Layers
open OnBytes OnBytes.Model OnBytes.Model.Layer
open Johnson.AtFull.Shape
open OnBytes.Desc.First.K4 OnBytes.Desc.First.K4.Rt OnBytes.Desc.First.K4.RtPub
open VerifiableInference.Desc.First.Shape

/-- The panels' test pansB in a second text, with its tie. -/
def panelsTestSecondText :
    { f : Pub → Env → Nat → Nat → Bool // ∀ P v l n, pansB P v l n = f P v l n } :=
  ⟨_, fun P v l n => by
    delta pansB panelsT panelT placePanels
    simp -zeta only [Johnson.Unfolds.mergeSort_eq, Array.mapM_eq_mapM_toList, Array.toList_range]
    rfl⟩

/-- An entry of the equality table, asked with «?»: whether it is there is said by the library's law
on the table's size: the table need not be made to know. -/
theorem equalityTable_getOption (z : Array E) (i : Nat) :
    (eqTab z)[i]? = if i < 2 ^ z.size then some ((eqTab z).getD i zeroE) else none := by
  by_cases h : i < 2 ^ z.size
  · have h' : i < (eqTab z).size := by rw [OnBytes.Flat.size_eqTab]; exact h
    rw [if_pos h, Array.getElem?_eq_getElem h', Array.getD, dif_pos h']
    rfl
  · have h' : (eqTab z).size ≤ i := by rw [OnBytes.Flat.size_eqTab]; exact Nat.le_of_not_lt h
    rw [if_neg h, Array.getElem?_eq_none h']

/-- ClaimEnv.facRs in a second text, with its tie. -/
def factorAtBitsSecondText :
    { f : ClaimEnv → WsGrp → Nat → Nat → Option WsFac // ∀ c G a b, ClaimEnv.facRs c G a b =
    f c G a b } :=
  ⟨_, fun c G a b => by
    delta ClaimEnv.facRs eqLow
    simp only [equalityTable_getOption, Array.mapM_eq_mapM_toList, Array.toList_range]
    rfl⟩

/-- ClaimEnv.facEw in a second text, with its tie. -/
def factorOfSegmentSecondText :
    { f : ClaimEnv → WsGrp → String → Nat → Option WsFac // ∀ c G s x, ClaimEnv.facEw c G s x =
    f c G s x } :=
  ⟨_, fun c G s x => by
    delta ClaimEnv.facEw
    simp only [equalityTable_getOption, Array.mapM_eq_mapM_toList, Array.toList_range]
    rfl⟩

/-- ClaimEnv.weightClaims in a second text, with its tie. -/
def weightClaimsSecondText :
    { f : ClaimEnv → List Nat → Option (List WsClaim) // ∀ c TS, ClaimEnv.weightClaims c TS =
    f c TS } :=
  ⟨_, fun c TS => by
    delta ClaimEnv.weightClaims ClaimEnv.claimsA ClaimEnv.claimsT
    simp -zeta only [factorAtBitsSecondText.2, factorOfSegmentSecondText.2]
    rfl⟩

/-- **The panels' test on the plan, from a closed Bool on its second text.** -/
theorem panelsTest_ofSecondText {P : Pub} {v : Env} {l n : Nat} (h : panelsTestSecondText.1 P v l n
    = true) :
    pansB P v l n = true := (panelsTestSecondText.2 P v l n).trans h

/-- atWeightClaims (WeightClaimsTests.lean) with the weight claims in their second text. -/
def atWeightClaimsSecondText (P : Pub) (hp : HPlan2) (g : Nat) (f : List WsClaim → Bool) : Bool :=
  (callsTS P).any fun TS => (weightClaimsSecondText.1 (blankClaims P hp g) TS).any f

/-- The two texts of the test at the weight claims are equal. -/
theorem atWeightClaims_eqSecondText (P : Pub) (hp : HPlan2) (g : Nat) (f : List WsClaim → Bool) :
    atWeightClaims P hp g f = atWeightClaimsSecondText P hp g f := by
  unfold RtPub.atWeightClaims atWeightClaimsSecondText
  refine congrArg (fun q => Option.any q (callsTS P)) (funext fun TS => ?_)
  show Option.any f ((blankClaims P hp g).weightClaims TS) =
    Option.any f (weightClaimsSecondText.1 (blankClaims P hp g) TS)
  rw [weightClaimsSecondText.2]

/-- **claimsB from the four closed Bools**: on the count, on the first k weight claims, on the rest,
and on the embedding's claim. -/
theorem claimsTest_ofSecondTextTests (P : Pub) (hp : HPlan2) (g k : Nat)
    (hN : (atWeightClaimsSecondText P hp g fun cp =>
      cp.length + (if (g == 0) = true then 1 else 0) == hp.NCL && decide (0 < hp.NCL) &&
        decide (hp.NCL ≤ 4096)) = true)
    (hA : (atWeightClaimsSecondText P hp g fun cp => (cp.take k).all (claimPassesMerge P.wsLay)) =
        true)
    (hB : (atWeightClaimsSecondText P hp g fun cp => (cp.drop k).all (claimPassesMerge P.wsLay)) =
        true)
    (hE : embeddingClaimTest P hp g = true) : claimsB P hp g = true :=
  claimsTest_ofFourTests P hp g k
      (by unfold weightClaimsCountTest; rw [atWeightClaims_eqSecondText]; exact hN)
    (by rw [atWeightClaims_eqSecondText]; exact hA) (by rw [atWeightClaims_eqSecondText]; exact hB)
        hE

/-- The term mergeRecordsShapes (MergeRecordsClosedForm.lean) with the weight claims in their
second text. -/
def mergeRecordsShapesSecondText (P : Pub) (hp : HPlan2) (g n : Nat) : Option (List RecSh) :=
  (callsTS P).bind fun TS => (weightClaimsSecondText.1 (blankClaims P hp g) TS).bind fun cp =>
    (if (g == 0) = true then
      (embeddingClaimZeros (blankClaims P hp g) (Array.replicate (P.y.ls + P.y.h.lt) zeroE)
        (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0)).map ([·])
    else some []).map fun ce =>
      (((cp ++ ce).zip (List.replicate n zeroE)).map fun y => wsRowPart P.wsLay y.1 zeroE).map recSh

/-- The two texts of mergeRecordsShapes are equal. -/
theorem mergeRecordsShapes_eqSecondText (P : Pub) (hp : HPlan2) (g n : Nat) :
    mergeRecordsShapes P hp g n = mergeRecordsShapesSecondText P hp g n := by
  unfold mergeRecordsShapes mergeRecordsShapesSecondText
  refine congrArg (fun q => Option.bind (callsTS P) q) (funext fun TS => ?_)
  show Option.bind ((blankClaims P hp g).weightClaims TS) _ =
    Option.bind (weightClaimsSecondText.1 (blankClaims P hp g) TS) _
  rw [weightClaimsSecondText.2]

/-- Two lists of what is left of the weight claims are one list where their two fields agree. -/
theorem mergeRecords_ofFields : ∀ {a b : List RecSh},
    (a.map fun r => (r.ui, r.f)) = (b.map fun r => (r.ui, r.f)) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | ⟨u, f⟩ :: a, ⟨u', f'⟩ :: b, h => by
    rw [List.map_cons, List.map_cons] at h
    injection h with h1 h2
    injection h1 with h3 h4
    have h3' : u = u' := h3
    have h4' : f = f' := h4
    subst h3' h4'
    rw [mergeRecords_ofFields h2]

/-- **What the merge leaves, tested in one closed Bool**: the list in its second text against a
written list, by its two fields. -/
def mergeRecordsTest (P : Pub) (hp : HPlan2) (g : Nat) (w : List RecSh) : Bool :=
  (mergeRecordsShapesSecondText P hp g (mergeSlotsCount hp g)).any fun recs =>
    decide ((recs.map fun r => (r.ui, r.f)) = w.map fun r => (r.ui, r.f))

/-- Where that Bool is true, mergeRecordsShapes is the written list. -/
theorem mergeRecords_ofTest {P : Pub} {hp : HPlan2} {g : Nat} {w : List RecSh}
    (h : mergeRecordsTest P hp g w = true) : mergeRecordsShapes P hp g (mergeSlotsCount hp g) =
        some w := by
  rw [mergeRecordsShapes_eqSecondText]
  unfold mergeRecordsTest at h
  cases hr : mergeRecordsShapesSecondText P hp g (mergeSlotsCount hp g) with
  | none =>
    rw [hr] at h
    cases h
  | some recs =>
    rw [hr] at h
    have h' : decide ((recs.map fun r => (r.ui, r.f)) = w.map fun r => (r.ui, r.f)) = true := h
    rw [mergeRecords_ofFields (of_decide_eq_true h')]

end Johnson.AtFull.Shape.Layers

#print axioms Johnson.AtFull.Shape.Layers.panelsTestSecondText
#print axioms Johnson.AtFull.Shape.Layers.equalityTable_getOption
#print axioms Johnson.AtFull.Shape.Layers.factorAtBitsSecondText
#print axioms Johnson.AtFull.Shape.Layers.factorOfSegmentSecondText
#print axioms Johnson.AtFull.Shape.Layers.weightClaimsSecondText
#print axioms Johnson.AtFull.Shape.Layers.panelsTest_ofSecondText
#print axioms Johnson.AtFull.Shape.Layers.atWeightClaimsSecondText
#print axioms Johnson.AtFull.Shape.Layers.atWeightClaims_eqSecondText
#print axioms Johnson.AtFull.Shape.Layers.claimsTest_ofSecondTextTests
#print axioms Johnson.AtFull.Shape.Layers.mergeRecordsShapesSecondText
#print axioms Johnson.AtFull.Shape.Layers.mergeRecordsShapes_eqSecondText
#print axioms Johnson.AtFull.Shape.Layers.mergeRecords_ofFields
#print axioms Johnson.AtFull.Shape.Layers.mergeRecordsTest
#print axioms Johnson.AtFull.Shape.Layers.mergeRecords_ofTest
