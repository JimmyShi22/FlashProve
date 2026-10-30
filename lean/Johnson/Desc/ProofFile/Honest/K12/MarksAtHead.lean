-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/MarksAtHead.lean

What it proves. Under the head P5J.AtMg, at the proof file's shared chain and the test on G_u: the
premises on the plan and on the fall-back that DoorsByShape.lean's theorems ask are met. So at the
state of doorUF, at every input and whatever precedes the test, whatever the readers of the key and
of the columns are: the three tests stTidyB, stPlainB and claimsB hold; the shape is the term
Shape.doorU (endOf …); and layFits is true at jobAtU with that state function.

Names.
  planOk_head_eight   under the head each of the eight blocks passes its test on the plan: off the
      description's own test on the plan.
  fallU_plan   fallU does not read the plan's list of messages that must be fixed before the point.
  marks_real, marks_at   at the typed sizes the three tests hold at fallU, and the part that layFits
      reads of it is the plan's: by the kernel's evaluation.
  three_fallU_head, near_fallU_head   the same under the head.
  three_head_UF, shape_head_UF, layFits_head_UF   the theorems.

By what. planOk_blocks (Johnson/Desc/PlanPasses.lean); descN_shared
(Johnson/Loose/H2K12/DescN.lean); k12_sits_row (Johnson/Loose/H2K12/SitsRow.lean); the membership in
sharedPre as in blocks_pass_of_pre (Johnson/Loose/H2K12/TiesAtSeats.lean). In this folder:
written_at_head, qAt_written (FitAtHead.lean); facts_at_head, layFitsNear_head_U, pubBehind_plan
(NearAtHead.lean); three_doorUF, shape_doorUF, near_doorUF (DoorsByShape.lean).

Limits.
- The test on G_u alone. At the test on G_omega the fall-back is made with the parameters of the
  test in front, (fourOf Np).U. The five clauses of FrontAsks on the shape (frontFiveB,
  FrontAtShape.lean) read these parameters too. Neither is treated here: both are in
  FrontAtHead.lean.
- The theorems are also true of the fall-back: they do not tell a fold that failed from one that
  returned, and they are no statement that the state on entry is the verifier's.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Loose.H2K12.TiesAtSeats
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleNotice TableKey)
open OnBytes.Params (LinShape)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (qAt realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks blocksOr first withU)
open H2K.JointK (descN p14N sharedPre descN_shared)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.Sh (claimsB testSh)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head each of the eight blocks passes its test on the plan.** -/
theorem planOk_head_eight (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (qAt Zp Np) = some bs) : ∀ b ∈ bs, b.planOk = true := by
  obtain ⟨Z', N', c', hZ', hN', e, -⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hp : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := by
    rw [← e]
    exact h.laid.planOk
  obtain ⟨-, h2, -⟩ := VerifiableInference.Desc.Keeps.planOk_blocks _ hp
  intro b hbm
  have hb' : blocks (p14N Z' N') = some bs := hb
  have hbo : b ∈ blocksOr (p14N Z' N') := by
    unfold blocksOr
    rw [hb']
    exact hbm
  have m : (b.retype (Cl' := ProofFile.Cl)).asBare ∈ sharedPre ProofFile.Cl Z'.p.chains (p14N Z' N') N' :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem hbo)
  have k : ((b.planOk && b.claims.isEmpty) && (b.retype (Cl' := ProofFile.Cl)).hasNoClaimsAndNothingAfter) = true :=
    h2 _ ((descN_shared o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') ▸ List.mem_append_left _ m)
  simp only [Bool.and_eq_true] at k
  exact k.1.1

/-- fallU does not read the list of messages that must be fixed before the point. -/
theorem fallU_plan (set : OnBytes.Params.Setting) (sc : OnBytes.Params.Scope) (codes : Codes)
    (S : LinShape) (item : ℕ) (l l' : List (ℕ × ℕ)) (s : Array OracleNotice) :
    fallU ⟨set, sc, codes, S, item, l⟩ s = fallU ⟨set, sc, codes, S, item, l'⟩ s := rfl

/-- At the typed sizes: the three tests at fallU, and the part that layFits reads of it. -/
theorem marks_real : (realSized.all fun q =>
    stTidyB (fallU (planOf q.2 q.1.shape).P (sentOf q.1.shape)).st &&
      stPlainB (fallU (planOf q.2 q.1.shape).P (sentOf q.1.shape)).st &&
      claimsB (fallU (planOf q.2 q.1.shape).P (sentOf q.1.shape)) &&
      decide (pubNear (fallU (planOf q.2 q.1.shape).P (sentOf q.1.shape)) =
        nearOf (pubBehind (planOf q.2 q.1.shape).P (sentOf q.1.shape)) 0)) = true := by
  decide +kernel

/-- What marks_real says at the size that realSized returns. -/
theorem marks_at {x : OnBytes.Params.LinSized} (hx : realSized = some (x, codesFull2)) :
    Three (fallU (planOf codesFull2 x.shape).P (sentOf x.shape)) ∧
      pubNear (fallU (planOf codesFull2 x.shape).P (sentOf x.shape)) =
        nearOf (pubBehind (planOf codesFull2 x.shape).P (sentOf x.shape)) 0 := by
  have k := marks_real
  rw [hx] at k
  simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at k
  exact ⟨⟨k.1.1.1, k.1.1.2, k.1.2⟩, k.2⟩

/-- Under the head the three tests hold at the fall-back. -/
theorem three_fallU_head (h : P5J.AtMg o Z D r Zp Np cF) :
    Three (fallU (qAt Zp Np) (sentOf (qAt Zp Np).S)) := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  rw [qAt_written Wr Np, fallU_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) []]
  exact (marks_at hx).1

/-- Under the head the part that layFits reads of the fall-back is the plan's. -/
theorem near_fallU_head (h : P5J.AtMg o Z D r Zp Np cF) :
    pubNear (fallU (qAt Zp Np) (sentOf (qAt Zp Np).S)) =
      nearOf (pubBehind (qAt Zp Np) (sentOf (qAt Zp Np).S)) 0 := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  rw [qAt_written Wr Np, fallU_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) [], pubBehind_plan]
  exact (marks_at hx).2

/-- **The three tests at doorUF's state, under the head.** -/
theorem three_head_UF (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (w : W) (fr : Front X) :
    Three (doorUF (qAt Zp Np) (sentOf (qAt Zp Np).S) bs key cols w fr) := by
  obtain ⟨hS, -, hw⟩ := facts_at_head h
  exact three_doorUF (qAt Zp Np) bs hb (planOk_head_eight h bs hb) hS _ hw (three_fallU_head h) key
    cols w fr

/-- **The shape of doorUF's state is one term, under the head.** -/
theorem shape_head_UF (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (w : W) (fr : Front X) :
    testSh (doorUF (qAt Zp Np) (sentOf (qAt Zp Np).S) bs key cols w fr) =
      Desc.K14.Shape.doorU (endOf (qAt Zp Np) (sentOf (qAt Zp Np).S)) := by
  obtain ⟨hS, -, hw⟩ := facts_at_head h
  exact shape_doorUF (qAt Zp Np) bs hb hS _ hw key cols w fr

/-- **layFits at jobAtU with doorUF, under the head.** -/
theorem layFits_head_UF (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) :
    (jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U
      (doorUF (qAt Zp Np) (sentOf (qAt Zp Np).S) bs key cols) weights rand u?).layFits
      (doorUF (qAt Zp Np) (sentOf (qAt Zp Np).S) bs key cols w fr) = true := by
  obtain ⟨hS, hM, hw⟩ := facts_at_head h
  rw [layFits_near, near_doorUF (qAt Zp Np) bs hb hS hM _ hw (near_fallU_head h) key cols w fr]
  exact layFitsNear_head_U h _ weights rand u?

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.planOk_head_eight
#print axioms ProofFile.Honest.K12.Light.fallU_plan
#print axioms ProofFile.Honest.K12.Light.marks_real
#print axioms ProofFile.Honest.K12.Light.marks_at
#print axioms ProofFile.Honest.K12.Light.three_fallU_head
#print axioms ProofFile.Honest.K12.Light.near_fallU_head
#print axioms ProofFile.Honest.K12.Light.three_head_UF
#print axioms ProofFile.Honest.K12.Light.shape_head_UF
#print axioms ProofFile.Honest.K12.Light.layFits_head_UF
