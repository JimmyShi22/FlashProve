-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmReachHeadB.lean: THE LIBRARY's ARMS ("the committed cell is
its stated function", behind the tie), UNDER THE HEAD, AT THE MEANING AT WHICH THE HONEST THREAD's
OWN PROMISE STANDS, WITH THE SEVEN PREMISES OF arm_at_head_b (Twin/ArmAtHeadB.lean) PAID AT ONE J:
"A REACHED STATE INSIDE THE PROMISE AT THAT MEANING". TYPED BY HAND, OVER THE TWINS THAT A PROGRAM
MADE. One theorem; no definition.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

  - arm_reach_head_b: UNDER h (the library's head: A HYPOTHESIS), O: arm_at_head_b's end, with J
    laid at the library's own JReach (Johnson/Desc/K1/Law/JReach.lean: general in its three letters)
    at: "reached", the library's RchPub at the head's description, AT A LETTER Pp for what is asked
    of the public part (the library lays typedPub there); the head's numbers; THE MEANING honest
    (mgAll h.𝔇 mgBase) ans test, where the library has mgAll h.𝔇 mgBase.

How. The six sentences on J by the library's jReach_elim, TERM FOR TERM AS
Johnson/Desc/AtSeats/K01CondOfRest.lean PAYS THEM (the fields hJl, hLay's two, hJt, hJH, hElse's
one): four payers are general in the meaning and are called as they lie (liveIs_at_rch, jLay2_paid,
tlIsPlan_at_reads, rowsBareH_at_reads); one is a twin (jFirst_at_reads_b); jH_at_pub's eight lines
are typed anew here, since the library's has typedPub in its statement. JHead at border 342 and the
matrices' seats there as Johnson/Desc/AtSeats/K01CondOfHead.lean pays its fields h342 and hMP, with
the twins jHead3_342_b and matsP_342_b. PlanesLeft6 by planesLeft6_atAll_b.

WHAT IS LEFT. ArmOk at that J, at a thread's state: that the state is a reached one (the threads'
own law says so in the raw form), and the promise there. NOT SHOWN HERE.

Limits. THE FULL SIZE; the format's second hash function; under the head, of which no member is shown.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtHeadB
import Johnson.Desc.ProofFile.Honest.K1.Twin.FirstSeatedAtLinkNoB
import Johnson.Desc.ProofFile.Honest.K1.Twin.JHead342B
import Johnson.Desc.ProofFile.Honest.K1.Twin.Head342ColsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.PlanesLeft6AtAllB

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
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)

section
open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : First.Look.Place}
  {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs →
    Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Prop}
  {test : ℕ → S → Option String}

/-- **THE ARMS UNDER THE HEAD, AT THE THREAD's OWN MEANING, AT "A REACHED STATE INSIDE THE PROMISE
AT THAT MEANING".** -/
theorem arm_reach_head_b (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (dk : K12Data) (Pp : ProofFile.InstPub → Prop) (aN : ℕ) (R₁ R₂ R₃ : Rounds) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      YesOf (blkL Zp Bs.G₀ l false X arrs) x x' →
      InAt h.𝔇.N (honest (mgAll h.𝔇 mgBase) ans test) linksFull (flatPlacesOf linksFull true)
        (noL l false) x y →
      ArmOk (JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp) h.𝔇.N
        (honest (mgAll h.𝔇 mgBase) ans test)) x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ cF l false) y y' → (mgAll h.𝔇 mgBase).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ h.𝔇.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (h.𝔇.Rd l) (h.𝔇.N.sent l 0) (h.𝔇.N.group l) p.1 p.2 x.2 A B
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w) (uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH) := by
  have p1 := (P5J.pins_of_laid h.scope h.laid).1
  have p2 := P5J.cutIs_of_laid h.scope h.laid
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hC := hC_atAll h p1 (VerifiableInference.PlanWritten.cutIs_eq p2).1 (reads_named_at24 h)
  exact arm_at_head_b h O dk _
    (jReach_elim _ _ _ (LiveIs _ _) fun _ _ a hr _ hm => liveIs_at_rch h _ a hr.1 hm)
    (jReach_elim _ _ _ (JFirst _) (fun l hl a hr hon hm =>
      jFirst_at_reads_b h p1 (VerifiableInference.PlanWritten.cutIs_eq p2).1 l hl a hr.1 hon hm))
    (jReach_elim _ _ _ (JLay2 _) (fun l hl a hr =>
      jLay2_paid h.𝔇 h.scope h.reads O (hOk_atAll h O) (hDlk_atAll h) (hlk_atAll h) O.W
        (layKB_scope O O.W) _ _ l hl a hr.1))
    (jReach_elim _ _ _ (TlIsPlan _) (fun l hl a hr =>
      tlIsPlan_at_reads h.scope h.reads O O.W _ _ l hl a hr.1))
    (jReach_elim _ _ _ (JH _ _ _ _ _ _) (fun l hl a hr hon hm =>
      ⟨noTables_at_reads h.scope h.reads O _ _ l hl a hr.1 hon hm, by
        by_cases h24 : l = 24
        · subst h24
          exact jHead_of_live (liveLayout_at_rch h _ a hr.1 hm)
            (jHead3_342_b h.𝔇 mgBase h.𝔇.layout (P5J.At.num Zp) _ _
              (foldDAt Zp Bs cF h.𝔇.N Zp.made.p.built.links) _
              h.scope h.reads O h.laid.planOk eW (fun _ _ hr => hr.1) (hfit_atAll h)
              (foldFacts_atAll h p1 O _ (fun _ _ hr => hr.1) h.𝔇.N Zp.made.p.built.links)
              (foldD_sent h Bs h.𝔇.N Zp.made.p.built.links) rfl hC
              (eW ▸ VerifiableInference.Desc.Kinds.Head.Law.InScope.cols_in_scope h.scope h.reads
                O.public)
              (eW ▸ VerifiableInference.Reads.AtSeat.nums_whole h.scope h.reads O.public)
              a hr hon hm)
        · exact jHead_low _ _ _ _ _ _ l (by omega) a.1 _ ⟨hon, hm⟩⟩))
    (jReach_elim _ _ _ RowsBareH (fun l hl a hr =>
      rowsBareH_at_reads h.scope h.reads O (k3Bare_of h.scope h.reads O (hOk_atAll h O)) _ _ l hl a
        hr.1))
    aN R₁ R₂ R₃
    (fun X arrs x x' y y' w p A B Fc _ =>
      planesLeft6_atAll_b h dk Pp (P5J.At.num Zp)
        (VerifiableInference.Desc.Kinds.Head.Law.AtFold.matsP_342_b h.𝔇 mgBase h.𝔇.layout
          (P5J.At.num Zp) _ _ (foldDAt Zp Bs cF h.𝔇.N Zp.made.p.built.links) _ (hfit_atAll h)
          (foldFacts_atAll h p1 O _ (fun _ _ hr => hr.1) h.𝔇.N Zp.made.p.built.links)
          (foldD_sent h Bs h.𝔇.N Zp.made.p.built.links) rfl hC)
        aN R₁ R₂ R₃ Fc)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.arm_reach_head_b
