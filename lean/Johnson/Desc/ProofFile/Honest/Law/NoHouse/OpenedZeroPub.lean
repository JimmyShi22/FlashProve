-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/OpenedZeroPub.lean: behind number 2 of the first chain,
the nine public items that are open or tied at border 3 hold.

Number 2 of the first chain's flat list is the first segment's opening (kind K1) with the frame's
step "opened" of link 0 joined behind it. The table's promise at the border behind it asks, among
its six tests, that every public item that is open there, or tied to an item that is open there,
holds of the verifier's state. By a look over the written lists
 these are nine: "no reply is heard", "a ledger is open", "the slots above are free", "the link
is fresh", "the look-up's condition in front of its block", the two names "frame.sentIs" and
"ledger.treesAre" at segment 0, and, tied to the index masks' pin, "the index masks' number is the
plan's" and "the statement holds that message". This file shows each of the nine behind an accept
of the whole member, under the library's head, at the library's own meaning. It adds no definition.

The road. The library has a maker for each item at the bare joined block `K1.openingZero`, from
that block's accept, under ties on the plan's letters. The chain's own member stands under that
block (`IM.first_under`). The ties are theorems under the head (`K1.G_…_atAll`,
Johnson/Desc/K1/Law/TiesAtAll.lean and TiesAtAll2.lean; Johnson/Desc/AtSeats/PlanGAtAll.lean and
PlanZeroAtAll.lean). What the meaning's public test is at each item: Johnson/Desc/AtSeats/
MgGCAtBase.lean. What is asked of the state in front of the member follows from the reach: that
state is the first state (`P1L20.reach_two`).

  `opening_yes`     an accept of the chain's member number 2 is an accept of the bare joined block
  `start_frame`     the first state's frame keeps nothing and has nothing "at the start"
  `three_unheard`, `three_ledger`, `three_freeAbove`, `three_linkFresh`, `three_lookIn`,
  `three_sentIs`, `three_treesAre`, `three_index`   the nine, one by one (the last has two)

Limits. The full size and the format's second hash function alone: the library's head is a premise. That
just these nine are open or tied at border 3 is not shown here. The state in front is asked to be
reached at border 2 and to bear no mark. This file imports one module under Johnson/Goal/ directly
(Johnson/Goal/Skeleton/CutIsOfLaid.lean). None of these is one of the library's goals. Nothing is
said on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.CallsBetween
import Johnson.Desc.AtSeats.MgGCAtBase
import Johnson.Desc.AtSeats.PlanGAtAll
import Johnson.Desc.AtSeats.PlanZeroAtAll
import Johnson.Desc.AtSeats.StatementSeat
import Johnson.Desc.K1.Law.TiesAtAll2
import Johnson.Desc.K1.Law.IndexBools
import Johnson.IMR.ReplyNatField
import Johnson.IMR.AtReach
import Johnson.K11R.CondOfTwo
import Johnson.P1L20R.RoomFold
import Johnson.Goal.Skeleton.CutIsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain K1.openingZero K1.gpOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (mgAll mgBase)
open VerifiableInference.Desc.K13.Law (StepG)
open Johnson.Desc.First.Walk.Seat (fvsOf zeroAt)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

/-- The first state's frame keeps nothing, and nothing is laid "at the start". -/
theorem start_frame {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).check.frame.keptBefore = #[] ∧
      (ProofFile.startS Z p).check.frame.atStart = #[] := by
  unfold ProofFile.startS
  dsimp only
  split
  · rw [Meaning.K2.s0_first h]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
  {z : ProofFile.InstPub} {s t : TS} {e : Block TS ProofFile.Cl}
include h O

/-- **An accept of the chain's member number 2 is an accept of the bare joined block.** -/
theorem opening_yes (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    ∃ nm X r₁ r₂ gs, zeroAt Zp.p.built.links Zp.p.X = some X ∧
      (K1.openingZero Bs.G₀.first (K1.gpOf Zp) nm X (fvsOf Zp.p.built.links) Zp.first.lin.kCol :
        Block TS ProofFile.Cl).decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨e', nm, X, he', hX, hU⟩ := IM.first_under h.scope h.reads O
  obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
  obtain ⟨R, c, -, hs⟩ := hy
  have hst : StepG ProofFile.Cl Bs.G₀.first (K1.gpOf Zp) nm X (fvsOf Zp.p.built.links)
      Zp.first.lin.kCol ((), s) ((), t) :=
    ⟨rfl, 0, R, c, c.length, VerifiableInference.Desc.step_under hU hs⟩
  obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
  exact ⟨nm, X, r₁, r₂, gs, hX, hd⟩

/-- "No reply is heard." -/
theorem three_unheard (R : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s))
    (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub .unheard (z, t) = true := by
  have R3 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (2 + 1) (z, t) := .succ R he hy
  rw [HashBuild.unheard_base]
  show t.out.reply.isNone = true
  rw [IM.unheard_reach h.scope h.reads O (by omega) R3]
  rfl

/-- "A ledger is open, with its three arrays at its number of slots." -/
theorem three_ledger (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub (.ledger 0) (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, -, hd⟩ := opening_yes h O he hy
  rw [(HashBuild.mgGC_base h.𝔇 false (VerifiableInference.Desc.K1.G_hdg_atAll h)).ledger]
  exact VerifiableInference.Desc.K13.Law.openingZero_ledger hd

/-- "Every slot from the next free number on is free, and the ledger has the plan's slots." -/
theorem three_freeAbove (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub (.freeAbove 0) (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, hX, hd⟩ := opening_yes h O he hy
  have PG := VerifiableInference.Desc.K1.G_hPlG_atAll h hX
    (VerifiableInference.Desc.K1.planG_atAll h O)
  rw [(HashBuild.mgGC_base h.𝔇 false (VerifiableInference.Desc.K1.G_hdg_atAll h)).freeAbove,
    PG.slots]
  exact VerifiableInference.Desc.K13.Law.openingZero_freeAbove hd

/-- "The link is fresh." -/
theorem three_linkFresh (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub (.linkFresh 0) (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, hX, hd⟩ := opening_yes h O he hy
  have PG := VerifiableInference.Desc.K1.G_hPlG_atAll h hX
    (VerifiableInference.Desc.K1.planG_atAll h O)
  rw [(HashBuild.mgGC_base h.𝔇 false (VerifiableInference.Desc.K1.G_hdg_atAll h)).linkFresh]
  exact VerifiableInference.Desc.K13.Law.openingZero_linkFresh hd _ PG.unheard PG.arrays

/-- "The look-up's condition in front of its block." -/
theorem three_lookIn (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub (.lookIn 0 2) (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, hX, hd⟩ := opening_yes h O he hy
  have PG := VerifiableInference.Desc.K1.G_hPlG_atAll h hX
    (VerifiableInference.Desc.K1.planG_atAll h O)
  obtain ⟨p, f, a1, a2, a3, a4, a5, a6⟩ := PG.place
  rw [(HashBuild.mgGC_base h.𝔇 false (VerifiableInference.Desc.K1.G_hdg_atAll h)).lookIn]
  exact VerifiableInference.Desc.K13.Law.openingZero_lookIn hd _ false p f a1 a2 a3 a4 a5 a6
    PG.arrays

/-- The name "frame.sentIs" at segment 0. -/
theorem three_sentIs (R : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s)) (hm : s.failed = none)
    (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub HashBuild.sentItem0 (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, -, hd⟩ := opening_yes h O he hy
  have RA := Meaning.K2.recAll_all h.scope h.reads O (P5J.flat_ok h.toAtMg) R hm
  obtain ⟨-, -, -, hl⟩ := calls_behind_laid h.scope h.reads O (l := 0) (by omega) R
  obtain rfl := P1L20.reach_two h.scope h.reads O R
  have h0 : (ProofFile.startS Zp z).st.oracles.size = 0 := by
    rw [(Meaning.K2.startS_facts h.laid.pub z).2.1]
    rfl
  obtain ⟨s₁, g₁, h1, -⟩ := VerifiableInference.Desc.K1.openingZero_mid hd
  obtain ⟨g, mask, -, -, hlt⟩ :=
    VerifiableInference.Desc.K1.firstAtS_frame _ _ _ s₁ r₁ r₂ g₁ h1
  obtain ⟨hb, hk, ho⟩ := HashBuild.frontG Bs.G₀.first (K1.gpOf Zp) h.𝔇.shape h.𝔇.N h.𝔇.links
    (VerifiableInference.Desc.First.flatPlacesOf h.𝔇.links true) h.𝔇.built (ProofFile.startS Zp z) h0
    RA.walk.shape hl (by rw [RA.walk.groups, RA.walk.shape]) (start_frame h.laid.pub z).1
    (VerifiableInference.Desc.K1.G_hb0_atAll h O (P5J.pins_of_laid h.scope h.laid).1
      (P5J.cutIs_of_laid h.scope h.laid)) (Nat.le_of_lt hlt)
  rw [HashBuild.sent_base]
  exact VerifiableInference.Desc.K13.Law.openingZero_sentIs hd _ hb hk ho

/-- The name "ledger.treesAre" at segment 0. -/
theorem three_treesAre (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub HashBuild.treesItem0 (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, hX, hd⟩ := opening_yes h O he hy
  obtain ⟨Y, hY, hYF⟩ := VerifiableInference.Desc.K1.G_hY_atAll h O X hX
  rw [HashBuild.trees_base]
  exact VerifiableInference.Desc.K13.Law.openingZero_treesAre hd _
    (HashBuild.trees_zero _ _ _ _ _ X.X X.ns Y hY hYF)

/-- "The index masks' number is the plan's", and "the statement holds that message". -/
theorem three_index (R : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s))
    (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    (mgAll h.𝔇 mgBase).pub .indexIs (z, t) = true ∧
      (mgAll h.𝔇 mgBase).pub .indexThere (z, t) = true := by
  obtain ⟨nm, X, r₁, r₂, gs, -, hd⟩ := opening_yes h O he hy
  obtain rfl := P1L20.reach_two h.scope h.reads O R
  have hn : VerifiableInference.Desc.K1.noneSentB (ProofFile.startS Zp z) = true := by
    unfold VerifiableInference.Desc.K1.noneSentB
    rw [(Meaning.K2.startS_facts h.laid.pub z).2.1, (start_frame h.laid.pub z).2]
    rfl
  obtain ⟨i1, i2⟩ := VerifiableInference.Desc.K1.openingZero_makes hd hn
  rw [VerifiableInference.Desc.K1.eG_atAll h O (P5J.pins_of_laid h.scope h.laid).1,
    VerifiableInference.Desc.K1.sizes_two.2.1] at i1
  refine ⟨?_, i2⟩
  show VerifiableInference.Desc.K13.indexIsC (P5J.At.N Zp cF).indexNo t = true
  rw [_root_.K11.indexNo_four h]
  exact i1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.start_frame
#print axioms ProofFile.Honest.FirstThread.opening_yes
#print axioms ProofFile.Honest.FirstThread.three_unheard
#print axioms ProofFile.Honest.FirstThread.three_ledger
#print axioms ProofFile.Honest.FirstThread.three_freeAbove
#print axioms ProofFile.Honest.FirstThread.three_linkFresh
#print axioms ProofFile.Honest.FirstThread.three_lookIn
#print axioms ProofFile.Honest.FirstThread.three_sentIs
#print axioms ProofFile.Honest.FirstThread.three_treesAre
#print axioms ProofFile.Honest.FirstThread.three_index
