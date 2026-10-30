-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FoldFactsAtAll.lean: THE STRUCTURE OF FOLD FACTS (First.FoldFacts),
WHOLE, AT THE CLOSED CONSTANT (P5J.mgAtAll, MgAtAll.lean), BY CALLS:
a value of it along every family Rch that lies within "reached at the IOP as written in Lean", at
the laws' own written lists of segments and places. No law of other files is typed here.
  foldDAt            the public numbers d: first tree 0 · sent := sentAt Zp · the group of segment m
                     is m · ownAt, keptAt: the plan's terms off what the sub-protocols tell · L :=
                     LFull, M := MFull (the written ones) · free0, fvs: K1.free0Of, Walk.Seat.fvsOf
  **foldFacts_atAll**  FoldFacts Rch (fun a => a.1) (foldDAt …) (the request's words) linksFull
                     (flatPlacesOf linksFull true), from hA, hP1, the opening O, hRch
  foldD_sent         (foldDAt …).sent = hA.𝔇.sent, by unfolding (L, M: LFull, MFull by the make)
  mgMore_fit, hfit_atAll   the table's test pubFit accepts the composed meaning's closed list of
                     named public items (Lean's kernel) · mgMore_fit_rejects: a negative test
THE PAYERS. foldFacts_of_rest (Johnson/IMR/AtReachFits.lean): twenty-four
fields, each another file's theorem, called there · room, roomEarly: room_field_paid,
roomEarly_field_paid (Johnson/P1L20R/RoomKeepAll.lean) · its premise hB: sends_pinned_paid
(Johnson/IMR/FivePinned.lean) at the entry tests' first comparison's own accept, which hP1 gives in
scope (pinnedAt_row, key_in_scope_pure) · hLd: laid_in_scope; M by msgs_in_scope
(Johnson/HB/LLHARD/PlanInScope.lean) · the written lists: linksW_full, placesW_linksFull.
LETTERS. N, built: free, as in foldFacts_of_rest: ownAt and keptAt read of N what withTold lays
alone, and nothing of built.
PREMISES. hA: the shared head. hP1: a test with code on the public files, NOT PAID HERE. O: the
maker's opening (the head holds that there is one). hRch.
What is not claimed. That the premises can be met: NO MEMBER. At Rch := never every field is free.
Nothing on soundness.

-/
import Johnson.IMR.AtReachFits
import Johnson.P1L20R.RoomKeepAll
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.P5J.MgAtAll
import Johnson.Top.H0.Walk.ReachAt
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S Numbers FoldData FoldFacts flatPlacesOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten (madePinnedAt madeRow pinnedAt_row key_in_scope_pure)
open VerifiableInference.Desc.K13.Law (LFull MFull laid_in_scope msgs_in_scope)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- The public numbers. -/
def foldDAt (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (cF : Chain S Cl) (N : Numbers)
    (built : Array Stages.LinkH) : FoldData :=
  { ft := 0, sent := _root_.Meaning.K2.sentAt Zp, groupAt := fun m => m,
    ownAt := First.FillSent.ownAt Zp.first.shape
      (N.withTold (flatPlacesOf linksFull true) (_root_.Meaning.Carry.toldOf cF.blocksInOrder)) linksFull
      (flatPlacesOf linksFull true) built,
    keptAt := First.FillSent.keptAt Zp.first.shape
      (N.withTold (flatPlacesOf linksFull true) (_root_.Meaning.Carry.toldOf cF.blocksInOrder)) linksFull
      (flatPlacesOf linksFull true) built,
    L := LFull, M := MFull, free0 := free0Of Bs.G₀.first (gpOf Zp),
    fvs := Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links }

set_option maxRecDepth 1000000 in
/-- The table's test pubFit accepts the composed meaning's closed list of named public items, at the
written lists of segments and places (Lean's kernel). -/
theorem mgMore_fit : First.pubFit mgMore linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- The closed list with the maker's row of "frame.sentIs" struck. -/
def mgMoreBent : First.More :=
  ((((((({} : First.More).merge First.rowMore).merge First.FillBare.leftMore).merge
    First.FillSent.sent1More).merge First.FillSent.sentMoreNoMaker).merge H2K5.Door.more).merge
      K13.Law.wSitsMore).strike First.leavesName

set_option maxRecDepth 1000000 in
/-- **A negative test**: with that row struck the test rejects. -/
theorem mgMore_fit_rejects :
    First.pubFit mgMoreBent linksFull (flatPlacesOf linksFull true) = false := by
  decide +kernel

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

/-- **The fold facts, whole, at the constant.** -/
theorem foldFacts_atAll
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) {Bs : ProofFile.PureBase}
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {Str : Type} (Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop)
    (hRch : ∀ k a, Rch k a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) k a) (N : Numbers)
    (built : Array Stages.LinkH) :
    FoldFacts Rch (fun a => a.1) (foldDAt Zp Bs cF N built)
      (fun p : ProofFile.InstPub => Verify.words32 p.request) linksFull
      (flatPlacesOf linksFull true) := by
  have hy : madeRow Zp = true := by
    have h := hP1
    rw [pinnedAt_row, if_pos (key_in_scope_pure hA.scope hA.laid.pub)] at h
    exact h
  have hpl : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc hA.laid.planOk
  have hB := IM.sends_pinned_paid O hy
    (IM.hp_of_planOk hA.scope hA.reads O (IM.blocksOk_of_planOk O hA.laid.planOk))
  have hraw : ∀ k a, Rch k a →
      Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a.1 :=
    fun k a h => Johnson.Desc.First.Walk.Tied.rchAt_raw (hRch k a h)
  have H := _root_.Meaning.K2.foldFacts_of_rest hA.scope hA.reads O hA.laid.planOk Rch
    (fun a => a.1) (fun k a h => hRch k a h) N built hB (laid_in_scope hA.scope hA.laid.pub hP1)
    hA.laid.value _ _ (P1L20.room_field_paid hA.scope hA.reads O hpl hraw)
    (P1L20.roomEarly_field_paid hA.scope hA.reads O hpl hraw)
  rw [msgs_in_scope hA.scope hA.laid.pub hP1, _root_.Meaning.K2.placesW_linksFull,
    LPFK9.linksW_full] at H
  exact H

/-- **hfit at the constant**: the table's test on the list of named public items. -/
theorem hfit_atAll :
    First.pubFit (mgAll hA.𝔇 mgBase).more linksFull (flatPlacesOf linksFull true) = true := by
  rw [mgAll_more_base]
  exact mgMore_fit

/-- The part "sent" is the constant's own. -/
theorem foldD_sent (Bs : ProofFile.PureBase) (N : Numbers) (built : Array Stages.LinkH) :
    (foldDAt Zp Bs cF N built).sent = hA.𝔇.sent := rfl

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.foldFacts_atAll
#print axioms VerifiableInference.Desc.K1.foldD_sent
#print axioms VerifiableInference.Desc.K1.mgMore_fit
#print axioms VerifiableInference.Desc.K1.mgMore_fit_rejects
#print axioms VerifiableInference.Desc.K1.hfit_atAll
