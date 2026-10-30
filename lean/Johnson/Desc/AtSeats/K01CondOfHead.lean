-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
A MEMBER OF THE HEAD P5J.AtMgA IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction, WITH fixedConfigurationDigest IN THE
DIGEST's PLACE; SIDE LIBRARY AtFullSide/Top/); SO WHAT RESTS ON THE HEAD COUNTS AS PROVED AT storedPublicFiles
AND zGap ALONE.
KIND K1's NAMED CONDITION FROM THE HEAD. The condition P5J.AtMgA.K1Cond stands frozen in
Johnson/Desc/AtSeats/K01KindAll.lean and is not re-cut; Johnson/Desc/AtSeats/K01CondOfRest.lean
brings it down to the eleven fields of K1Owed. HERE EACH OF THE ELEVEN IS ONE CALL:
  pin1 · pin2      P5J.pins_of_laid | P5J.cutIs_of_laid at h.scope, h.laid. They are not proved
                   here: they are assumed with h. They are two of the entry tests that the field
                   «laid» of h holds: the rows of lawsAsk (Johnson/Desc/Laid/ProofAsks.lean) that
                   ask PlanWritten.madeRow and PlanWritten.cutRow. The fields of «plan» that are
                   named at k01_kind_of_head below are assumed with h in the same way.
  hArr · hLab      readsArrB · labPB: theorems under the head alone (hArr_atAll · hLab_atAll).
  hKB              layKB: a theorem at every opening (layKB_scope).
  hSecB · hCallsB · hBattB · hBlayB   theorems under the head, an opening and pin1: each over one fact by Lean's kernel at the
                   written values, with negative tests beside it: 12 segments · 8 matrices · 12 × 5
                   · 12 × 9 cases. The negative tests do not bend every one of these cases. Some
                   arms of the tests say yes where an entry that they look up is missing: restCB
                   where the layout lacks the array; secB, battB and blayB where the plan has no
                   entry for the segment.
  hMP              matsP_342 (Johnson/P4R/Head342Cols.lean) at the closed constant: its five premises are calls.
  h342             THE HEAVY ONE: JHead at border 342: four clauses on the state in front of the output head's reads (what the
                   lookup has heard · the state's tables are the lookup's own run's · the layout in use · the matrices are
                   seated): jHead3_342 (Johnson/Desc/K1/Law/JHead342.lean) with the same five, two
                   sentences on the public parameters (cols_in_scope, Johnson/Goal/Meaning/HeadColsScope.lean · nums_whole, Johnson/Desc/Reads/RunIsInScope.lean) and liveLayout_at_rch.
  k1Cond_of_head   (h) (𝔏) : h.K1Cond 𝔏.
  k01_kind_of_head (h) (𝔏) (q₁) (q₂) (q₃) : h.Kind 𝔏 KindName.K1. Its hypotheses are h and the three
                   equations on 𝔏. Of h the proof uses at most these fields: scope, reads, pubOne;
                   of «laid»: pub, value, planOk, data, run, asks, opened; of «plan»: shape, laid,
                   named, fit, groups, radii. The six fields of «plan» are Boolean tests on values
                   computed from the public files; they are not themselves entry tests. None of
                   these fields is proved in this file: all are assumed with h. The head of
                   Johnson/Goal/Skeleton/CondsOfLaid.lean lists from what each follows where h is
                   built.
The two readers under K1Rest's «∃» are read by no owed field: laid at the constant's own reader (h.𝔇.rw13).
IT PAYS NO LAW OF OTHER FILES: IT CALLS THEM. What is not claimed. That the head has a member at other files than storedPublicFiles and zGap, or at another hash than secondHashFunction. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K01CondOfRest
import Johnson.Desc.AtSeats.ReadsArrAtAll
import Johnson.Desc.AtSeats.LabAtAll
import Johnson.Desc.AtSeats.LayKAt
import Johnson.Desc.AtSeats.SymsLayAtAll
import Johnson.Desc.AtSeats.SymsAttAtAll
import Johnson.Desc.AtSeats.CallsAtAllPaid
import Johnson.Desc.K1.Law.SecAtAllPaid
import Johnson.Desc.AtSeats.FoldFactsAtAll
import Johnson.Desc.AtSeats.SeatsK6AtAll
import Johnson.P4R.Head342Cols
import Johnson.Desc.K1.Law.JHead342
import Johnson.Goal.Skeleton.CutIsOfLaid
import Johnson.Goal.Meaning.HeadColsScope
import Johnson.Desc.Reads.RunIsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ Stated smpNamed widen TiedAtR HandsOn doorsFitB MgData
  mgAll d13)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt readsOf)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt OldKept plus13 cA13 FactsK13 wSitsItem wSitsB
  planSitsB
  planSeatB FillsK13C PlanM3 PlanM4 SmpOld DecBlind plusG FactsG PlanG PlanGSeats StepG)
open VerifiableInference.Desc.K12.Door (K12Data toTree)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.Desc.First.Walk (LayPar)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open k1Ix k1Reads)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt readsOf uHeadK6 K6Name)
open VerifiableInference.Desc.K13.Law (openAt OldKept plus13 cA13 FactsK13)
open IM (Open k1Ix k1Reads k1Quiet)
open VerifiableInference.Desc.First.Att.P (uArm)
open OnBytes.Road.K4 (uLay)
open VerifiableInference.Desc.K9 (readersOfLink holesAt)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)

open VerifiableInference.Desc.First.Att.P (uArm plannedK)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6 ColFour CallsSeated lab_of_calls)
open VerifiableInference.Desc.First.Look (sigListCalls)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Model.Verify (borderOf publicOf layerShape)

section
open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : First.Look.Place}

/-- **Kind K1's named condition, from the head.** -/
theorem _root_.P5J.k1Cond_of_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : h.K1Cond 𝔏 := by
  have p1 := (P5J.pins_of_laid h.scope h.laid).1
  have p2 := P5J.cutIs_of_laid h.scope h.laid
  refine P5J.k1Cond_of_rest h 𝔏 fun Bs base₀ O => ⟨h.𝔇.rw13, h.𝔇.rw13, ?_⟩
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hC := hC_atAll h p1 (VerifiableInference.PlanWritten.cutIs_eq p2).1 (reads_named_at24 h)
  exact
    { pin1 := p1
      pin2 := p2
      hArr := hArr_atAll h
      hLab := hLab_atAll h
      hKB := layKB_scope O O.W
      hSecB := hSecB_atAll h O p1
      hCallsB := hCallsB_atAll h O p1
      hBattB := hBattB_atAll h O p1
      hBlayB := hBlayB_atAll h O p1
      hMP := VerifiableInference.Desc.Kinds.Head.Law.AtFold.matsP_342 h.𝔇 mgBase h.𝔇.layout (P5J.At.num Zp) _ _
        (foldDAt Zp Bs cF h.𝔇.N Zp.made.p.built.links) _ (hfit_atAll h)
        (foldFacts_atAll h p1 O _ (fun _ _ hr => hr.1) h.𝔇.N Zp.made.p.built.links)
        (foldD_sent h Bs h.𝔇.N Zp.made.p.built.links) rfl hC
      h342 := fun a hr hon hm => jHead_of_live (liveLayout_at_rch h _ a hr.1 hm)
        (jHead3_342 h.𝔇 mgBase h.𝔇.layout (P5J.At.num Zp) _ _ (foldDAt Zp Bs cF h.𝔇.N Zp.made.p.built.links) _
          h.scope h.reads O h.laid.planOk eW (fun _ _ hr => hr.1) (hfit_atAll h)
          (foldFacts_atAll h p1 O _ (fun _ _ hr => hr.1) h.𝔇.N Zp.made.p.built.links)
          (foldD_sent h Bs h.𝔇.N Zp.made.p.built.links) rfl hC
          (eW ▸ VerifiableInference.Desc.Kinds.Head.Law.InScope.cols_in_scope h.scope h.reads O.public)
          (eW ▸ VerifiableInference.Reads.AtSeat.nums_whole h.scope h.reads O.public) a hr hon hm) }

/-- **Kind K1's law in the counted form, from the head.** -/
theorem _root_.P5J.k01_kind_of_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) : h.Kind 𝔏 KindName.K1 :=
  P5J.k01_kind_all h 𝔏 q₁ q₂ q₃ (P5J.k1Cond_of_head h 𝔏)

end

end VerifiableInference.Desc.K1

#print axioms P5J.k1Cond_of_head
#print axioms P5J.k01_kind_of_head
