-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/NearAtHead.lean: `ManyJob.layFits` (RunMany.lean) at the jobs of
the shared chain's two proximity tests, at the proof file's own plan and the seated places, under
the library's head (`P5J.AtMg`, Johnson/P5J/AtMg.lean). It imports Mathlib.

  `facts_at_head`   three public facts on the plan `qAt Zp Np`
                 (Johnson/Desc/K1/Law/SitsShared.lean): the shape splits, masks are sent ahead, and
                 what goes out with o_u can be said (`sentOf`)
  `layFitsNear_head_U`, `layFitsNear_head_Omega`   `layFitsNear` (PubNear.lean) is true at
                 `jobAtU` and `jobAtOmega` (JobShared.lean) at that plan and the seated places, at
                 the part of a state that is made from the plan (`nearOf`, PubNear.lean, of
                 `pubBehind`, PubAtDoor.lean), for every state function, every pair of readers and
                 every vector passed in
  `doorU`, `doorOmega`   `doorOf` (JobShared.lean) over a list bs of blocks (in the theorems: the
                 eight that `blocks` returns; at G_omega with the block of the test on G_u behind
                 them; without the chain's front block, which has no round), with the state made
                 from the plan as its fall-back
  `layFits_head_U`, `layFits_head_Omega`   so at the jobs with these state functions `layFits` is
                 true at the state on entry (the job's `rec₀`), for every input and whatever
                 precedes the test
  `blocks_head`, `planOk_head_U`   `blocks` (Johnson/Desc/K14/Blocks.lean) returns a list at the
                 plan; the block of the test on G_u passes its test on the plan
  `all_zip_congr`, `layFitsNear_congr`   `layFitsNear` reads of a job its first stage and its
                 members' shapes alone
  `shapes_plan_U`, `shapes_plan_Omega`, `pubBehind_plan`   the members' shapes at the two jobs, and
                 `pubBehind`, are made from the plan's codes and shape alone
  `emptyU`, `emptyOmega`, `near_real`   the two jobs at arguments that hold nothing; the facts and
                 the two checks at the typed sizes and the written places, evaluated by Lean's
                 kernel

By what. As in FitAtHead.lean: under the head the plan holds the written codes and the typed shape
(`qAt_written`, `written_at_head`) and the seated places have the written places' stages
(`places_at_head`); then one evaluation. The last two theorems: `nearDoor_U`, `nearDoor_Omega` and
`layFits_near` (PubNear.lean). `planOk_head_U`: the library's `k12_sits_row` and `RowK12.plans`
(Johnson/Loose/H2K12/SitsRow.lean).

Limits.
- All limits of FitAtHead.lean apply. Among them: the full size alone; the plan `qAt Zp Np` and the
  seated places; that a job which a caller builds is one of these is up to that caller; the jobs'
  members are made of `jobU` and `jobOmega` (Johnson/Desc/ProofFile/Honest/K14/Sendings.lean), a
  file of another folder, so what the theorems say changes if that file changes (Parts.lean there
  and Frame, ForKinds, Side, Sum of Johnson/Desc/ProofFile/Honest/ lie beneath as well); the number
  0 is the field `atPoint`, which `layFitsNear` does not read. No example of the head is shown here;
  the library's side has one at the full size (`headMember_zFull`,
  AtFullSide/Top/HeadMemberAtFull.lean), and `real_members` (Johnson/Desc/K1/Law/CondReal.lean) says
  that `realSized` returns a value, so `near_real` is not empty.
- `doorOf` returns its fall-back where the fold over the blocks or `enter` fails, so
  `layFits_head_U` and `layFits_head_Omega` are also true of that fall-back: they do not tell a fold
  that failed from one that returned. At the test on G_omega `doorOf` returns the fall-back at every
  honest run, as long as a part is handed no opened column. So these theorems are no statement that
  the state on entry is the verifier's.
- No definition of the prover's text asks `layFits` or `layFitsNear`, and none fails where one is
  false. That the fold returns at any input is a theorem at neither test; PubAtSmallDoor.lean
  evaluates it at the small example.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.PubNear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleNotice TableKey)
open OnBytes.Params (LinShape)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (qAt realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks first withU)
open H2K.Member (piUFull piOFull)
open H2K.JointK (descN)
open ProofFile.Honest.K14 (jobU jobOmega)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {W X : Type}

/-! ## 1 What `layFitsNear` reads of a job -/

/-- Two numbered lists whose members have the same shapes, one by one, pass the same checks on shape
and number. -/
theorem all_zip_congr {α β γ : Type} (sa : α → γ) (sb : β → γ) :
    ∀ (l : List α) (l' : List β) (k : ℕ) (P : α × ℕ → Bool) (P' : β × ℕ → Bool),
      l.map sa = l'.map sb → (∀ a b i, sa a = sb b → P (a, i) = P' (b, i)) →
      (l.zipIdx k).all P = (l'.zipIdx k).all P'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h, _ => by cases h
  | a :: l, b :: l', k, P, P', h, hP => by
    rw [List.map_cons, List.map_cons] at h
    rw [List.zipIdx_cons, List.zipIdx_cons, List.all_cons, List.all_cons,
      hP a b k (List.cons.inj h).1, all_zip_congr sa sb l l' (k + 1) P P' (List.cons.inj h).2 hP]

theorem layFitsNear_congr {W' X' : Type} (A : ManyJob W X) (B : ManyJob W' X')
    (hs : A.s₀ = B.s₀) (hm : A.mems.map (·.shape) = B.mems.map (·.shape)) (N : Near) :
    layFitsNear A N = layFitsNear B N := by
  have hl : A.mems.length = B.mems.length := by
    have e := congrArg List.length hm
    rwa [List.length_map, List.length_map] at e
  unfold layFitsNear
  cases N.2 with
  | none => rfl
  | some x =>
    show fitsBy A N.1 x.1 _ = fitsBy B N.1 x.1 _
    unfold fitsBy
    simp only [hs, hl]
    congr 1
    refine all_zip_congr (·.shape) (·.shape) _ _ 0 _ _ hm fun a b i h => ?_
    have h' : a.shape = b.shape := h
    simp only [h']

/-! ## 2 At the typed sizes and the written places -/

/-- What goes out with o_u; nothing where it cannot be said. -/
def sentOf (S : LinShape) : Array OracleNotice := (withU S).getD #[]

/-- `jobAtU` at given codes and a given shape, the written place, and arguments that hold nothing.
-/
def emptyU (codes : Codes) (S : LinShape) : ManyJob Unit Unit :=
  jobAtU (planOf codes S) piUFull (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none

/-- `jobAtOmega` alike. -/
def emptyOmega (codes : Codes) (S : LinShape) : ManyJob Unit Unit :=
  jobAtOmega (planOf codes S) piOFull (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none

theorem sentU_plan (Q : P14) (n : ℕ) :
    (jobU ⟨Q, n⟩).Q.sent = (jobU (planOf Q.codes Q.S)).Q.sent := rfl

theorem sentOmega_plan (Q : P14) (n : ℕ) :
    (jobOmega ⟨Q, n⟩).Q.sent = (jobOmega (planOf Q.codes Q.S)).Q.sent := rfl

/-- The members' shapes at `jobAtU` are made from the plan's codes and shape alone. -/
theorem shapes_plan_U (Q : P14) (n : ℕ) (p : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtU ⟨Q, n⟩ p door weights rand u?).mems.map (·.shape) =
      (emptyU Q.codes Q.S).mems.map (·.shape) := by
  simp only [jobAtU, emptyU, memOfSending, List.map_cons, List.map_nil, sentU_plan Q n,
    sentOmega_plan Q n]

theorem shapes_plan_Omega (Q : P14) (n : ℕ) (p : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtOmega ⟨Q, n⟩ p door weights rand omega?).mems.map (·.shape) =
      (emptyOmega Q.codes Q.S).mems.map (·.shape) := by
  simp only [jobAtOmega, emptyOmega, memOfSending, List.map_cons, List.map_nil,
    sentOmega_plan Q n]

theorem pubBehind_plan (Q : P14) (s : Array OracleNotice) :
    pubBehind Q s = pubBehind (planOf Q.codes Q.S).P s := rfl

theorem near_real : (realSized.all fun q =>
    q.1.shape.sharedSplitNeeded && q.1.shape.masksAhead && (withU q.1.shape).isSome &&
      layFitsNear (emptyU q.2 q.1.shape)
        (nearOf (pubBehind (planOf q.2 q.1.shape).P (sentOf q.1.shape)) 0) &&
      layFitsNear (emptyOmega q.2 q.1.shape)
        (nearOf (pubBehind (planOf q.2 q.1.shape).P (sentOf q.1.shape)) 1)) = true := by
  decide +kernel

theorem withU_sentOf {S : LinShape} (h : (withU S).isSome = true) : withU S = some (sentOf S) := by
  unfold sentOf
  cases hw : withU S with
  | none =>
    rw [hw] at h
    cases h
  | some u => rfl

/-! ## 3 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- What `near_real` says at the size that `realSized` returns. -/
theorem near_at {x : OnBytes.Params.LinSized} (hx : realSized = some (x, codesFull2)) :
    x.shape.sharedSplitNeeded = true ∧ x.shape.masksAhead = true ∧
    (withU x.shape).isSome = true ∧
    layFitsNear (emptyU codesFull2 x.shape)
      (nearOf (pubBehind (planOf codesFull2 x.shape).P (sentOf x.shape)) 0) = true ∧
    layFitsNear (emptyOmega codesFull2 x.shape)
      (nearOf (pubBehind (planOf codesFull2 x.shape).P (sentOf x.shape)) 1) = true := by
  have k := near_real
  rw [hx] at k
  have k' : (x.shape.sharedSplitNeeded && x.shape.masksAhead && (withU x.shape).isSome &&
      layFitsNear (emptyU codesFull2 x.shape)
        (nearOf (pubBehind (planOf codesFull2 x.shape).P (sentOf x.shape)) 0) &&
      layFitsNear (emptyOmega codesFull2 x.shape)
        (nearOf (pubBehind (planOf codesFull2 x.shape).P (sentOf x.shape)) 1)) = true := k
  simp only [Bool.and_eq_true] at k'
  exact ⟨k'.1.1.1.1, k'.1.1.1.2, k'.1.1.2, k'.1.2, k'.2⟩

/-- **Three public facts on the plan, under the head.** -/
theorem facts_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    (qAt Zp Np).S.sharedSplitNeeded = true ∧ (qAt Zp Np).S.masksAhead = true ∧
      withU (qAt Zp Np).S = some (sentOf (qAt Zp Np).S) := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨a, b, c, _, _⟩ := near_at hx
  rw [qAt_written Wr Np]
  exact ⟨a, b, withU_sentOf c⟩

/-- **`layFitsNear` at the job of the test on G_u, at the part made from the plan.** -/
theorem layFitsNear_head_U (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    layFitsNear (jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?)
      (nearOf (pubBehind (qAt Zp Np) (sentOf (qAt Zp Np).S)) 0) = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨_, _, _, k, _⟩ := near_at hx
  have sU := (places_at_head h).1
  have eC : (qAt Zp Np).codes = codesFull2 := by rw [qAt_written Wr Np]
  have eS : (qAt Zp Np).S = x.shape := by rw [qAt_written Wr Np]
  have hs : (jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).s₀ =
      (emptyU (qAt Zp Np).codes (qAt Zp Np).S).s₀ := by
    show stage₀ (fourOf Np).U = stage₀ piUFull
    unfold stage₀
    rw [sU]
  rw [layFitsNear_congr _ _ hs (shapes_plan_U (qAt Zp Np) 0 _ door weights rand u?),
    pubBehind_plan, eC, eS]
  exact k

/-- **The same at the job of the test on G_omega.** -/
theorem layFitsNear_head_Omega (h : P5J.AtMg o Z D r Zp Np cF) (pO : P12)
    (hO : (fourOf Np).O = some pO) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    layFitsNear (jobAtOmega ⟨qAt Zp Np, 0⟩ pO door weights rand omega?)
      (nearOf (pubBehind (qAt Zp Np) (sentOf (qAt Zp Np).S)) 1) = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨_, _, _, _, k⟩ := near_at hx
  obtain ⟨_, _, q, hq, sO, _⟩ := places_at_head h
  obtain rfl : q = pO := Option.some.inj (hq.symm.trans hO)
  have eC : (qAt Zp Np).codes = codesFull2 := by rw [qAt_written Wr Np]
  have eS : (qAt Zp Np).S = x.shape := by rw [qAt_written Wr Np]
  have hs : (jobAtOmega ⟨qAt Zp Np, 0⟩ q door weights rand omega?).s₀ =
      (emptyOmega (qAt Zp Np).codes (qAt Zp Np).S).s₀ := by
    show stage₀ q = stage₀ piOFull
    unfold stage₀
    rw [sO]
  rw [layFitsNear_congr _ _ hs (shapes_plan_Omega (qAt Zp Np) 0 _ door weights rand omega?),
    pubBehind_plan, eC, eS]
  exact k

/-! ## 4 At the state on entry -/

theorem blocks_head (h : P5J.AtMg o Z D r Zp Np cF) : ∃ bs, blocks (qAt Zp Np) = some bs := by
  obtain ⟨_, _, hw⟩ := facts_at_head h
  unfold blocks
  rw [hw]
  exact ⟨_, rfl⟩

/-- Under the head the block of the test on G_u passes its test on the plan. -/
theorem planOk_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).planOk = true := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hp : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := by
    rw [← e]
    exact h.laid.planOk
  exact (R.plans hp).2.1

/-- The state function at the test on G_u: `doorOf` over the blocks bs, from the chain's first
state; its fall-back is the state made from the plan. -/
def doorU (Q : P14) (bs : List (Block St Unit)) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) : W → Front X → T12 :=
  doorOf bs (fun w => first Q.codes (key w))
    (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask)) cols
    (stateOfPub (pubBehind Q (sentOf Q.S), 0))

/-- The state function at the test on G_omega: behind bs and the test on G_u at the parameters p;
its fall-back is the state made from the plan, at group 1. -/
def doorOmega (Q : P14) (bs : List (Block St Unit)) (p : P12) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) : W → Front X → T12 :=
  doorOf (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])
    (fun w => first Q.codes (key w))
    (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) cols
    (stateOfPub (pubBehind Q (sentOf Q.S), 1))

/-- **`layFits` at `doorU`'s state, which is the job's own state on entry, for every input and
whatever precedes the test on G_u.** The fall-back of `doorU` is made from the same term of the
plan: where the fold fails, the statement holds by that choice. No statement that this state is the
verifier's. -/
theorem layFits_head_U (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) :
    (jobAtU ⟨qAt Zp Np, 0⟩ (fourOf Np).U (doorU (qAt Zp Np) bs key cols) weights rand u?).layFits
      (doorU (qAt Zp Np) bs key cols w fr) = true := by
  obtain ⟨hS, hM, hw⟩ := facts_at_head h
  rw [layFits_near]
  unfold doorU
  rw [nearDoor_U (qAt Zp Np) bs hb hS hM _ hw key cols w fr]
  exact layFitsNear_head_U h _ weights rand u?

/-- **The same at the test on G_omega**, at `doorOmega`'s state. At every honest run this is the
fall-back, as long as a part is handed no opened column (see the head's limits). No statement that
this state is the verifier's. -/
theorem layFits_head_Omega (h : P5J.AtMg o Z D r Zp Np cF) (pO : P12)
    (hO : (fourOf Np).O = some pO) (bs : List (Block St Unit))
    (hb : blocks (qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) :
    (jobAtOmega ⟨qAt Zp Np, 0⟩ pO (doorOmega (qAt Zp Np) bs (fourOf Np).U key cols) weights rand
      omega?).layFits (doorOmega (qAt Zp Np) bs (fourOf Np).U key cols w fr) = true := by
  obtain ⟨hS, hM, hw⟩ := facts_at_head h
  rw [layFits_near]
  unfold doorOmega
  rw [nearDoor_Omega (qAt Zp Np) bs hb hS hM _ hw _ (planOk_head_U h) key cols w fr]
  exact layFitsNear_head_Omega h pO hO _ weights rand omega?

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.all_zip_congr
#print axioms ProofFile.Honest.K12.Light.layFitsNear_congr
#print axioms ProofFile.Honest.K12.Light.sentU_plan
#print axioms ProofFile.Honest.K12.Light.sentOmega_plan
#print axioms ProofFile.Honest.K12.Light.shapes_plan_U
#print axioms ProofFile.Honest.K12.Light.shapes_plan_Omega
#print axioms ProofFile.Honest.K12.Light.pubBehind_plan
#print axioms ProofFile.Honest.K12.Light.near_real
#print axioms ProofFile.Honest.K12.Light.withU_sentOf
#print axioms ProofFile.Honest.K12.Light.near_at
#print axioms ProofFile.Honest.K12.Light.facts_at_head
#print axioms ProofFile.Honest.K12.Light.layFitsNear_head_U
#print axioms ProofFile.Honest.K12.Light.layFitsNear_head_Omega
#print axioms ProofFile.Honest.K12.Light.blocks_head
#print axioms ProofFile.Honest.K12.Light.planOk_head_U
#print axioms ProofFile.Honest.K12.Light.layFits_head_U
#print axioms ProofFile.Honest.K12.Light.layFits_head_Omega
#print axioms ProofFile.Honest.K12.Light.sentOf
#print axioms ProofFile.Honest.K12.Light.emptyU
#print axioms ProofFile.Honest.K12.Light.emptyOmega
#print axioms ProofFile.Honest.K12.Light.doorU
#print axioms ProofFile.Honest.K12.Light.doorOmega
