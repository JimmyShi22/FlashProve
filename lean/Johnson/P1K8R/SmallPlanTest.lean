-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SmallPlanTest.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
CLOSED SENTENCES `SmallPlan` AS TESTS WITH CODE, EACH TIED TO ITS SENTENCE.
NO SOUNDNESS.

  `matPlanB`: a Bool for `MatPlan` at one array; `matPlan_of_test`: its yes gives the sentence.
  `namesAtB`: a Bool: the built link's list names the array of matrix μ's label at the plan's number
    of that matrix's array.
  `smallPlanB Zp cF L₀ l Xl`: the programs' own test on the layout, and at each matrix of link l's
    plan: `namesAtB`, and `matPlanB` at the layout's array of the label (where the layout has none
    the matrix asks nothing: `SmallPlan.mats` asks nothing there either).
  `smallPlan_of_test`: **`smallPlanB Zp cF L₀ l Xl = true` gives `SmallPlan Zp cF L₀ l Xl`.**
Limits. NO TEST HAS RUN HERE. Nothing on soundness.

-/
import Johnson.P1K8R.SmallAtHead

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S FoldData flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.LinkJoin (whereD)
open ProofFile (Cl)

/-- A Bool for `MatPlan`. -/
def matPlanB (d : FoldData) (own : List (ℕ × ℕ)) (arr num : ℕ → ℕ → ℕ) (l t n born : ℕ)
    (A : ReqArray) : Bool :=
  match whereD d l t born A.message, _root_.Meaning.messageAt d.sent.shape born A.message with
  | some o, some msg =>
    decide (o < n) && decide (d.M[o]? = some msg.shape) &&
      match d.L.places[o]? with
      | some q => own.contains q && decide (arr q.1 q.2 = num born A.message)
      | none => false
  | _, _ => false

/-- **Its yes gives the sentence.** -/
theorem matPlan_of_test {d : FoldData} {own : List (ℕ × ℕ)} {arr num : ℕ → ℕ → ℕ}
    {l t n born : ℕ} {A : ReqArray} (h : matPlanB d own arr num l t n born A = true) :
    MatPlan d own arr num l t n born A := by
  unfold matPlanB at h
  split at h
  · rename_i o msg ho hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    split at h3
    · rename_i q hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
      exact ⟨o, q, msg, ho, h1, hm, h2, hq, List.contains_iff_mem.1 h3.1, h3.2⟩
    · cases h3
  · cases h

/-- A Bool: the built link's list names the array of matrix μ's label. -/
def namesAtB (X : Verify.Public) (l : ℕ) (Xl : LinkH) (μ : ℕ) : Bool :=
  decide (Xl.arrayOf[(Meaning.tlAt X l).gtTree.getD μ 0]? =
    some (Meaning.ownerK (Meaning.labAt X l μ),
      Meaning.nameOf (Meaning.ownerA (Meaning.labAt X l μ))))

/-- **THE TEST AT LINK l.** -/
def smallPlanB (Zp : ProofFile.Pub) (cF : Chain S Cl) (L₀ : VerifiableInference.Desc.K12.Door.Laid)
    (l : ℕ) (Xl : LinkH) : Bool :=
  reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) &&
    (List.range (Meaning.tlAt (P5J.At.X Zp) l).NM).all fun μ =>
      namesAtB (P5J.At.X Zp) l Xl μ &&
        match VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
          (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) with
        | some A =>
          matPlanB (P5J.At.foldD Zp cF L₀) ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp)
            (P5J.At.num Zp) l 2 ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
            (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A
        | none => true

/-- **THE TEST's YES GIVES THE CLOSED SENTENCES.** -/
theorem smallPlan_of_test {Zp : ProofFile.Pub} {cF : Chain S Cl}
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} {l : ℕ} {Xl : LinkH}
    (h : smallPlanB Zp cF L₀ l Xl = true) : SmallPlan Zp cF L₀ l Xl := by
  unfold smallPlanB at h
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  have h3 := fun μ (hμ : μ < (Meaning.tlAt (P5J.At.X Zp) l).NM) =>
    Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h2 μ (List.mem_range.2 hμ))
  refine ⟨fun μ hμ => ?_, h1, fun μ hμ A hA => ?_⟩
  · exact of_decide_eq_true (h3 μ hμ).1
  · have h4 := (h3 μ hμ).2
    rw [hA] at h4
    exact matPlan_of_test h4

end P1K8T

#print axioms P1K8T.matPlan_of_test
#print axioms P1K8T.smallPlan_of_test
