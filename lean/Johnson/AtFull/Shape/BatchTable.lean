-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchTable.lean: K9's 25 BATCHING MEMBERS OF THE PROOF FILE's OWN FIRST CHAIN:
THE FRAME AT PLAIN TABLES OF RUNS. It joins batch_of_slots (BatchWhole.lean) with the plain terms of
BatchTerms.lean. Nothing is evaluated.

  `SlotAt bs o run g V`: at the pair o there is a slot whose bare run IS run, whose law's run on
    shapes IS g, and whose law has a RunLawB whose Bool IS V. A definition: a premise's form.
  `ofSlots_run`: at a pair of the order the built run IS the guard around the slot's bare run.
  **`batch_of_tables`** (l < 25): Lk · p · w tied as in batch_named: for plain tables runT, gT, preT
    with SlotAt Lk.hear o (runT o) (gT o) (preT o) at each pair o of Lk.order: for every ft, G with
    G ‹number› = liftQ (batchGS p.rows w.1 gT Lk.order) and vals with
    vals ‹number› = batchVT p (fun o => guardRun ProofFile.sameReply (runT o)) preT Lk.order:
    CarriesV and Returns at that member.
  **`k8_slotAt`**, **`k4_slotAt`**, **`k5_slotAt`**, **`k6_slotAt`**, **`k11_slotAt`**: SlotAt at
    twelve of the fifteen runs by kind and name, each with its bare run, its run on shapes and its
    Bool written out.

Limits. A BRIDGE: the lookup's three runs (objects, guests, planes) have no SlotAt here (see
BatchSlotsK3.lean and BatchCellsAtt.lean; BatchCells.lean and BatchCellsAtt.lean meet the premise at
all 25 links). batch_of_tables does not say that a member stands at its number; ITS NUMBER AND ITS
STEP STILL HANG ON THE LINK Lk (Lk.hear.length, Lk.order), tied by cF.links[l]? alone: a caller wins
the order back from batch_named and the length from Numbers.lean. Where SlotAt holds at one g and
one Bool, it holds at every g with the Bool that always says no. CarriesV is the frame's CarriesU
, written out; accepted_of_shape (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) asks
Carries. That a Bool accepts at a state of a run is not shown. UNDER THE HEAD: that it has a member
is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchWhole
import Johnson.AtFull.Shape.BatchTerms
import Johnson.AtFull.Shape.BatchBools
import Johnson.AtFull.Shape.BatchSlots
import Johnson.AtFull.Shape.BatchSlotsK4
import Johnson.AtFull.Shape.BatchSlotsK5
import Johnson.AtFull.Shape.BatchSlotsK6
import Johnson.AtFull.Shape.BatchSlotsK11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere Where)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)
open ProofFile.Honest (Returns)

/-- At the pair o: a slot with that bare run, that run on shapes and that Bool. -/
def SlotAt (bs : List (Block S Claim)) (o : Nat × String)
    (run : VerifiableInference.Desc.K9.Shape.Run)
    (g : Nat → ChainSh → Except String (List ClaimSh × ChainSh)) (V : Nat → S → Bool) : Prop :=
  ∃ T : Slot ProofFile.sameReply bs o, T.bare = run ∧ T.law.runG = g ∧
    ∃ B : RunLawB T.law, B.preB = V

theorem ofSlots_run {same : S → S → Bool} {bs : List (Block S Claim)}
    {order : List (Nat × String)} (T : ∀ o, o ∈ order → Slot same bs o) (o : Nat × String)
    (h : o ∈ order) : (RunsLaw.ofSlots T).run o = guardRun same (T o h).bare := by
  show (pick T o).run = _
  unfold pick
  rw [dif_pos h]
  rfl

theorem ofSlotsB_preB {same : S → S → Bool} {bs : List (Block S Claim)}
    {order : List (Nat × String)} (T : ∀ o, o ∈ order → Slot same bs o)
    (B : ∀ o (ho : o ∈ order), RunLawB (T o ho).law) (o : Nat × String) (h : o ∈ order) :
    (ofSlotsB T B o).preB = (B o h).preB := by
  unfold ofSlotsB
  rw [dif_pos h]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem batch_of_tables (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere),
      cF.links[l]? = some Lk ∧ IM.k9At Zp l = some p ∧ testsWhere Zp.p.X l 0 = some w ∧
      ∀ (runT : Nat × String → VerifiableInference.Desc.K9.Shape.Run)
        (gT : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
        (preT : Nat × String → Nat → S → Bool),
        (∀ o ∈ Lk.order, SlotAt Lk.hear o (runT o) (gT o) (preT o)) →
        ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
          (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
          G (14 * l + Lk.hear.length + 2) = liftQ (batchGS p.rows w.1 gT Lk.order) →
          vals (14 * l + Lk.hear.length + 2) =
            batchVT p (fun o => guardRun ProofFile.sameReply (runT o)) preT Lk.order →
          CarriesV cF.blocksInOrder ft (firstZA G vals) (14 * l + Lk.hear.length + 2) ∧
            Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + Lk.hear.length + 2) := by
  obtain ⟨Lk, p, w, a1, a2, a3, hN⟩ := batch_of_slots h l hl
  refine ⟨Lk, p, w, a1, a2, a3, fun runT gT preT hS ft G vals hG hv => ?_⟩
  let T : ∀ o, o ∈ Lk.order → Slot ProofFile.sameReply Lk.hear o := fun o ho => (hS o ho).choose
  have hT : ∀ o (ho : o ∈ Lk.order), (T o ho).bare = runT o ∧ (T o ho).law.runG = gT o ∧
      ∃ B : RunLawB (T o ho).law, B.preB = preT o := fun o ho => (hS o ho).choose_spec
  let B : ∀ o (ho : o ∈ Lk.order), RunLawB (T o ho).law := fun o ho => (hT o ho).2.2.choose
  have hB : ∀ o (ho : o ∈ Lk.order), (B o ho).preB = preT o :=
    fun o ho => (hT o ho).2.2.choose_spec
  refine hN T B ft G vals ?_ ?_
  · rw [hG]
    congr 1
    exact batchGS_congr p.rows w.1 Lk.order fun o ho => by
      rw [ofSlots_runG T o ho, (hT o ho).2.1]
  · rw [hv, batchV_is]
    exact batchVT_congr p Lk.order fun o ho => by
      refine ⟨?_, ?_⟩
      · rw [ofSlots_run T o ho, (hT o ho).1]
      · show preT o = (ofSlotsB T B o).preB
        rw [ofSlotsB_preB T B o ho, hB o ho]

/-! ## The twelve -/

theorem k8_slotAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[l]? = some Lk ∧
      SlotAt Lk.hear (k8No (subAt l), "K8.equations") eqBare
        VerifiableInference.Desc.First.K8.Honest.eqRunG
        (fun _ s => VerifiableInference.Desc.First.K8.Honest.eqPreB s) := by
  obtain ⟨Bs, Xl, Lk, -, -, hL, T, -, hb, hg, hp⟩ := k8_slot h l hl
  exact ⟨Lk, hL, T, hb, hg, k8B T.law hp, rfl⟩

theorem k4_slotAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ cF.links[2 * g]? = some Lk ∧
      SlotAt Lk.hear (2, "front")
        (fun _ s => OnBytes.Desc.First.K4.Rt.seatRun "K4.claims-front"
          (OnBytes.Desc.First.K4.formsFrontNoRows Bs.G₀.W.layers g) s)
        (fun _ a => OnBytes.Desc.First.K4.Rt.k4RunG
          (OnBytes.Desc.First.K4.Rt.frontG Bs.G₀.W.layers g) a)
        (fun _ s => OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers s) ∧
      SlotAt Lk.hear (2, "back")
        (fun _ s => OnBytes.Desc.First.K4.Rt.seatRun "K4.claims-back"
          OnBytes.Desc.First.K4.formsBack s)
        (fun _ a => OnBytes.Desc.First.K4.Rt.k4RunG
          (OnBytes.Desc.First.K4.Rt.backG Bs.G₀.W.layers.y Bs.G₀.W.layers.sc) a)
        (fun _ s => OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers s) := by
  obtain ⟨Bs, Lk, hB, hL, ⟨T₁, b1, g1, p1⟩, T₂, b2, g2, p2⟩ := k4_slots h g hg
  exact ⟨Bs, Lk, hB, hL, ⟨T₁, b1, g1, k4B T₁.law _ p1, rfl⟩, T₂, b2, g2, k4B T₂.law _ p2, rfl⟩

theorem k5_slotAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (A : Attention.Plan),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.links[2 * g + 1]? = some Lk ∧ Bs.G₀.W.A[g]? = some A ∧
      SlotAt Lk.hear (2, "first")
        (K5Law.runFirst (VerifiableInference.Desc.First.Att.P.parCOf A))
        (H2K5.Honest.k5FirstG A) (fun _ s => H2K5.Honest.valsTS A s) ∧
      SlotAt Lk.hear (2, "keys")
        (K5Law.runKeys (VerifiableInference.Desc.First.Att.P.parCOf A))
        (H2K5.Honest.k5KeysG A) (fun _ s => H2K5.Honest.valsTS A s) ∧
      SlotAt Lk.hear (2, "join") (H2K5.Honest.joinRunA A)
        (H2K5.Honest.k5JoinG A) (fun _ s => H2K5.Honest.valsTS A s) ∧
      SlotAt Lk.hear (2, "second")
        (K5Law.runSecond (VerifiableInference.Desc.First.Att.P.parCOf A))
        (H2K5.Honest.k5SecondG A) (fun _ s => H2K5.Honest.valsTS A s) := by
  obtain ⟨Bs, Lk, A, hB, hL, hA, ⟨T₁, b1, g1, p1⟩, ⟨T₂, b2, g2, p2⟩, ⟨T₃, b3, g3, p3⟩,
    T₄, b4, g4, p4⟩ := k5_slots h g hg
  exact ⟨Bs, Lk, A, hB, hL, hA, ⟨T₁, b1, g1, k5B T₁.law A p1, rfl⟩,
    ⟨T₂, b2, g2, k5B T₂.law A p2, rfl⟩, ⟨T₃, b3, g3, k5B T₃.law A p3, rfl⟩,
    T₄, b4, g4, k5B T₄.law A p4, rfl⟩

theorem k6_slotAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (iU3 : Nat),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ cF.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      (∀ name ∈ ["norm", "policy", "logits"], SlotAt Lk.hear (3, name)
        (VerifiableInference.Desc.Kinds.Head.Shape.bare Bs.G₀.W.hS iU3
          (VerifiableInference.Desc.Kinds.Head.parOf Bs.G₀.W.hS
            (VerifiableInference.Desc.Kinds.Head.Law.workAtW Bs.G₀.W)) 24 4 name)
        (VerifiableInference.Desc.Kinds.Head.Shape.threeRunG Bs.G₀.W.hS iU3
          (VerifiableInference.Desc.Kinds.Head.parOf Bs.G₀.W.hS
            (VerifiableInference.Desc.Kinds.Head.Law.workAtW Bs.G₀.W)) name)
        (fun _ s => endsS (VerifiableInference.Desc.Kinds.Head.parOf Bs.G₀.W.hS
          (VerifiableInference.Desc.Kinds.Head.Law.workAtW Bs.G₀.W)) s)) ∧
      SlotAt Lk.hear (3, "join")
        (VerifiableInference.Desc.K3.joinRun
          (VerifiableInference.Desc.K3.seatCalls VerifiableInference.Desc.Kinds.Head.asClaim)
          (VerifiableInference.Desc.Kinds.Head.callerKeys
            (VerifiableInference.Desc.Kinds.Head.parOf Bs.G₀.W.hS
              (VerifiableInference.Desc.Kinds.Head.Law.workAtW Bs.G₀.W))
            (VerifiableInference.Desc.Kinds.Head.seatAt Bs.G₀.W.hS iU3)))
        (VerifiableInference.Desc.Kinds.Head.Shape.joinRunG Bs.G₀.W.hS iU3
          (VerifiableInference.Desc.Kinds.Head.parOf Bs.G₀.W.hS
            (VerifiableInference.Desc.Kinds.Head.Law.workAtW Bs.G₀.W)))
        (fun _ s => endsS (VerifiableInference.Desc.Kinds.Head.parOf Bs.G₀.W.hS
          (VerifiableInference.Desc.Kinds.Head.Law.workAtW Bs.G₀.W)) s) := by
  obtain ⟨Bs, Lk, iU3, hB, hL, hU, h3, T, b, g, p⟩ := k6_slots h
  refine ⟨Bs, Lk, iU3, hB, hL, hU, fun name hn => ?_, T, b, g, k6B T.law _ p, rfl⟩
  obtain ⟨T', b', g', p'⟩ := h3 name hn
  exact ⟨T', b', g', k6B T'.law _ p', rfl⟩

theorem k11_slotAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[24]? = some Lk ∧
      SlotAt Lk.hear (8, "the merge") Johnson.Desc.First.ForkMerge.headMergeClaim
        Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunG (fun _ _ => true) := by
  obtain ⟨Bs, Lk, -, hL, T, hb, hg, hp⟩ := k11_slot h
  exact ⟨Lk, hL, T, hb, hg, k11B T.law hp, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.ofSlots_run
#print axioms Johnson.AtFull.Shape.ofSlotsB_preB
#print axioms Johnson.AtFull.Shape.batch_of_tables
#print axioms Johnson.AtFull.Shape.k8_slotAt
#print axioms Johnson.AtFull.Shape.k4_slotAt
#print axioms Johnson.AtFull.Shape.k5_slotAt
#print axioms Johnson.AtFull.Shape.k6_slotAt
#print axioms Johnson.AtFull.Shape.k11_slotAt
#print axioms Johnson.AtFull.Shape.SlotAt
