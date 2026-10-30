-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/StartAtHead.lean: THE LAST CLOSED TEST BETWEEN "THE HEAD" AND "THE HEAD WITH THE FACTS ON EVERY REACHED STATE" IS A THEOREM UNDER THE HEAD: FillP1.startB Zp ‹the planner's first chain's oracle messages' shapes› ‹the index masks' number› = true (the field start of AtMgR, Johnson/P5J/AtMgR.lean; the one premise hs of Johnson/P5J/AtMgRAtHead.lean).
 THE ROAD: where the verifier's value is laid the two pins accept (pins_of_laid, Johnson/Goal/Skeleton/PinsOfLaid.lean): so the planner's sendings, the request's shape and what the first chain's sub-protocols tell ARE THE WRITTEN ONES; at these the test is a closed Bool: by Lean's kernel.
  P5T.seatsE · liftE · planSeatsBy_eq: the seats' maker (planSeatsBy, Johnson/P5T/PlanSeatsAt.lean) is a list that does not read the declared rounds, with the trees in front added to each seat's tree: so WHICH seat is the index masks' does not hang on the declared rounds.
  P5T.startE · index_of_startE: the table's index seat off that list.
  P5T.startE_full (BY THE KERNEL): at the written sendings and shape: tree 1, tenant 0, in a sending whose entry is 1 (no round in front: no tree in front).
  P5T.sends0_rise (BY THE KERNEL): the written sendings' entries rise: so the sort in msgsOfChain is idle (sorted_idle, Johnson/G/SendsListed.lean).
  P5T.startFullB · startFull (BY THE KERNEL): the test's text at the written values and at the number msgNoOf toldCut (1, 0) accepts · startFull_control: A NEGATIVE TEST: one number higher: it rejects.
  P5J.indexNo_at_head: (At.N Zp cF).indexNo = msgNoOf toldCut (1, 0) · **P5J.startB_at_head (h : AtMg OnBytes.secondHashFunction …): THE TEST ACCEPTS.**
  P5J.atMgR_of_head · atMgR_rch_of_head · atMgR_rchU_of_head: AtMgRAtHead's three WITHOUT hs: FROM THE HEAD ALONE, which stands over the entry tests (LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean) from thirteen rows on (GLOSSARY.md, "entry tests"): rows 9 and 10 and the field opts.laid are spent.
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. The written values rest on their files' own heads. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtMgRAtHead
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Goal.Numbers.RequestWritten
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.First.CutWritten
import Johnson.G.SendsListed
import Johnson.P5J.K03PiecesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5T
open Johnson.G

/-- planSeatsBy's text with the trees in front left out of j, and each seat's sending's entry beside. -/
def seatsE (c : ChainSends) (S : OnBytes.Params.ReqShape) : List (PSeat × ℕ) :=
  let groups := (OnBytes.reqGroups S).toList
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      let seg := segOf (groups.length + 1) 16 s.1.label
      let roles := match seg with
        | some (l, m) => rolesOf S groups l m
        | none => []
      (List.range s.1.sent.length).map fun i =>
        ({ label := s.1.label, send := s.2, seg := seg, idx := i,
           j := lay.tree.getD i 0, t := lay.part.getD i 0,
           shape := (s.1.sent.getD i default).shape, role := roles.getD i .other }, s.1.entry)

def liftE (rb : ℕ → ℕ) (x : PSeat × ℕ) : PSeat := { x.1 with j := rb (x.2 - 1) + x.1.j }

theorem planSeatsBy_eq (rb : ℕ → ℕ) (c : ChainSends) (S : OnBytes.Params.ReqShape) :
    planSeatsBy rb c S = (seatsE c S).map (liftE rb) := by
  unfold planSeatsBy seatsE
  dsimp only
  rw [List.map_flatMap]
  refine flatMap_same _ fun s _ => ?_
  cases OnBytes.layTrees c.codes s.1.sent.toArray with
  | none => rfl
  | some lay =>
    dsimp only
    rw [List.map_map]
    rfl

/-- What the table's index seat reads of these. -/
def startE (c : ChainSends) (S : OnBytes.Params.ReqShape) : Option (ℕ × ℕ × ℕ) :=
  ((seatsE c S).find? fun x => x.1.isStart).map fun x => (x.1.j, x.1.t, x.2)

theorem index_of_startE (rb : ℕ → ℕ) (c : ChainSends) (S : OnBytes.Params.ReqShape) {j t e : ℕ}
    (h : startE c S = some (j, t, e)) :
    (numbersOf (planSeatsBy rb c S)).index = (rb (e - 1) + j, t) := by
  show (((planSeatsBy rb c S).find? (·.isStart)).map (·.seat)).getD (0, 0) = _
  rw [planSeatsBy_eq, List.find?_map]
  unfold startE at h
  obtain ⟨x, hx, e1⟩ := Option.map_eq_some_iff.1 h
  have hx' : (seatsE c S).find? ((fun p : PSeat => p.isStart) ∘ liftE rb) = some x := hx
  rw [hx']
  have a1 : x.1.j = j := congrArg (·.1) e1
  have a2 : x.1.t = t := congrArg (·.2.1) e1
  have a3 : x.2 = e := congrArg (·.2.2) e1
  subst a1 a2 a3
  rfl

set_option maxRecDepth 1000000 in
/-- At the written plan: the index masks' message: tree 1, tenant 0, in a sending whose entry is 1. -/
theorem startE_full : startE proofSends0 VerifiableInference.Desc.ReqLit.shapeFull = some (1, 0, 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sends0_rise : (proofSends0.sends.map (·.entry)).Pairwise (· < ·) := by decide +kernel

/-- startB's text at the written plan, the sort left out. -/
def startFullB (ix : ℕ) : Bool :=
  match (VerifiableInference.Desc.K12.Door.msgsOf (proofSends0.sends.map (·.sent)))[ix]? with
  | some sh => VerifiableInference.Desc.ReqLit.shapeFull.atStart.map (·.shape) == [sh]
  | none => false

set_option maxRecDepth 1000000 in
theorem startFull :
    startFullB (VerifiableInference.Desc.First.msgNoOf VerifiableInference.Desc.First.toldCut (1, 0)) =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one number higher. -/
theorem startFull_control :
    startFullB (VerifiableInference.Desc.First.msgNoOf VerifiableInference.Desc.First.toldCut (1, 0) + 1) =
      false := by decide +kernel

end P5T

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (RchAt)
open VerifiableInference.PlanWritten (madeRow first_of_is proofSends_of_is request_shape_written)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the planner's first chain's sendings and the request's shape are the written ones. -/
theorem written_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    Zp.made.proof.1 = Johnson.G.proofSends0 ∧ Zp.first.shape = ReqLit.shapeFull := by
  have hy := madeRow_at_head h
  unfold madeRow at hy
  simp only [Bool.and_eq_true] at hy
  obtain ⟨⟨⟨-, hf⟩, hs⟩, -⟩ := hy
  obtain ⟨-, -, e2, -, -, -⟩ := first_of_is hf
  exact ⟨congrArg Prod.fst (proofSends_of_is hs), e2.trans request_shape_written⟩

/-- Under the head what the first chain's sub-protocols tell is the written list. -/
theorem told_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : At.told cF = toldCut :=
  (told_two cF.blocksInOrder).trans (told_at_written (pins_of_laid h.scope h.laid).2).2

/-- **The index masks' number at the head.** -/
theorem indexNo_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    (At.N Zp cF).indexNo = msgNoOf toldCut (1, 0) := by
  obtain ⟨c1, e2⟩ := written_at_head h
  have hi : (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index =
      (P5T.rootsIn (Zp.D.1.map (·.entry)) (1 - 1) + 1, 0) := by
    rw [P5T.planSeats_at]
    unfold P5T.planSeatsAt
    rw [c1, e2]
    exact P5T.index_of_startE _ _ _ P5T.startE_full
  show msgNoOf (At.told cF) (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index = _
  rw [told_at_head h, hi]
  rfl

/-- **THE TEST startB ACCEPTS UNDER THE HEAD.** -/
theorem startB_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true := by
  obtain ⟨c1, e2⟩ := written_at_head h
  have hM : K12.Door.msgsOfChain Zp.made.proof.1 =
      K12.Door.msgsOf (Johnson.G.proofSends0.sends.map (·.sent)) := by
    rw [c1]
    unfold K12.Door.msgsOfChain
    rw [Johnson.G.sorted_idle Johnson.G.proofSends0 P5T.sends0_rise]
  rw [indexNo_at_head h, hM]
  unfold FillP1.startB
  rw [e2]
  exact P5T.startFull

/-- **THE HEAD WITH THE FACTS ON EVERY REACHED STATE, FROM THE HEAD ALONE: GENERAL IN "REACHED".** -/
theorem atMgR_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Str : Type}
    (Rch : ℕ → ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Str →
      Prop)
    (hR : ∀ k a, Rch k a → RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a) :
    ∃ L, AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L :=
  atMgR_at_head h (startB_at_head h.toAtMg) Rch hR

theorem atMgR_rch_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ L, AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L :=
  atMgR_rch_at_head h (startB_at_head h.toAtMg)

theorem atMgR_rchU_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ L, AtMgR OnBytes.secondHashFunction Z D r Zp Np cF
      (fun k a => h.toAtMg.rch k a ∧ ¬ a.1.2.failed ≠ none) (fun a => a.1) L :=
  atMgR_rchU_at_head h (startB_at_head h.toAtMg)

end P5J

#print axioms P5T.planSeatsBy_eq
#print axioms P5T.index_of_startE
#print axioms P5T.startE_full
#print axioms P5T.sends0_rise
#print axioms P5T.startFull
#print axioms P5T.startFull_control
#print axioms P5J.written_at_head
#print axioms P5J.told_at_head
#print axioms P5J.indexNo_at_head
#print axioms P5J.startB_at_head
#print axioms P5J.atMgR_of_head
#print axioms P5J.atMgR_rch_of_head
#print axioms P5J.atMgR_rchU_of_head
