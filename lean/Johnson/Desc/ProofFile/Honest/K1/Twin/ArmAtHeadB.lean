-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmAtHeadB.lean: THE LIBRARY's ARMS ("the committed cell is
its stated function", behind the tie: ArmCellIn, Johnson/Desc/Sound/StatedCellIn.lean), UNDER THE
HEAD, AT THE MEANING AT WHICH THE HONEST THREAD's OWN PROMISE STANDS: ONE LAW, WITHOUT THE THREAD.
TYPED BY HAND, OVER THE TWINS THAT A PROGRAM MADE. One theorem; no definition.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

  - arm_at_head_b: UNDER h (the library's head: A HYPOTHESIS), O: at every link l < 25: from the
    reads' block's yes (YesOf), the library's promise InAt at honest (mgAll h.𝔇 mgBase) ans test in
    front, ArmOk J, KeptBelow and the item "tie" behind: ArmCellIn at every run of an item formsT
    that the row takes in, at ONE stated function: uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH.

How. arm_at_reads_three_b, with its five premises that take the fence paid by the payers' twins, and
its other premises by the library's own laws under the head: TERM FOR TERM AS THE LIBRARY PAYS THE
ELDERS' (Johnson/Desc/K1/Law/K01FiftyPaid.lean, at its call of arm_at_reads_three;
Johnson/Desc/AtSeats/K01CondOfRest.lean, the fields hLay to hElse;
Johnson/Desc/AtSeats/K01CondOfHead.lean, the fields hArr to hBlayB); then armCellIn_bySort_b.

WHAT IT LEAVES AS PREMISES. J IS A LETTER. SIX SENTENCES ON THE VERIFIER's STATE ARE ASKED OF IT
(hJl, hJf, hJ2, hJt, hJH, hJb): the library lays J at "a reached state inside its whole promise"
(JReach) and gets the six from that: not so here. A SEVENTH: hP6: PlanesLeft6 at the state in front
of the output head's reads, at the run "planes": the library's payer (planesLeft6_atAll) is not
general in J. THE SEVEN ARE NOT SHOWN AT A THREAD's STATE.

Limits. THE FULL SIZE; the format's second hash function; under the head, of which no member is shown.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.K01CondOfHead
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmBySortB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttEntryB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttInB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmLayInB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadJB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadBareB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmElsePaidB
import Johnson.Desc.ProofFile.Honest.K1.Twin.PlanesAtAllB

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
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : First.Look.Place}
  {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs →
    Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Prop}
  {test : ℕ → S → Option String}

/-- **THE ARMS UNDER THE HEAD, AT THE THREAD's OWN MEANING.** -/
theorem arm_at_head_b (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (dk : K12Data) (J : S → Prop)
    (hJl : ∀ s, J s → LiveIs h.𝔇.shape h.𝔇.layout s)
    (hJf : ∀ s, J s → JFirst h.𝔇.N s)
    (hJ2 : ∀ s, J s → JLay2 h.𝔇 s)
    (hJt : ∀ s, J s → TlIsPlan (P5J.At.X Zp) s)
    (hJH : ∀ s, J s → JH (P5J.At.X Zp) (h.𝔇.N.sent 24 0) h.𝔇.arr h.𝔇.N (P5J.At.num Zp)
      (P5J.At.layout Zp) s)
    (hJb : ∀ s, J s → RowsBareH s)
    (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hP6 : ∀ X arrs x x' y y' w p A B,
      ReadsFenceB h.𝔇 mgBase ans test J Zp Bs aN R₁ R₂ R₃ cF 24 X arrs x x' y y' w p A B →
      p.2 = "planes" →
      PlanesLeft6 (P5J.At.X Zp) (h.𝔇.N.sent 24 0) x.2 A h.𝔇.arr h.𝔇.N (P5J.At.num Zp)
        (P5J.At.layout Zp)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      YesOf (blkL Zp Bs.G₀ l false X arrs) x x' →
      InAt h.𝔇.N (honest (mgAll h.𝔇 mgBase) ans test) linksFull (flatPlacesOf linksFull true)
        (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ cF l false) y y' → (mgAll h.𝔇 mgBase).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ h.𝔇.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (h.𝔇.Rd l) (h.𝔇.N.sent l 0) (h.𝔇.N.group l) p.1 p.2 x.2 A B
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w) (uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH) := by
  intro l hl X arrs hX x x' y y' w hy hIn hK hk ht j n hjn p hp A B hA hB
  have p1 := (P5J.pins_of_laid h.scope h.laid).1
  obtain ⟨cU, hcU⟩ := hU_atAll h (hArr_atAll h)
  refine armCellIn_bySort_b h.𝔇 dk mgBase rfl l hl x y hIn A B hA _ _ _ _ _ _ ?_
  exact arm_at_reads_three_b h.𝔇 dk J h.scope h.reads O (hDlk_atAll h) aN R₁ R₂ R₃
    (hLay_ofB_b h.𝔇 dk J h.scope h.reads O O.W _ _ hJl hJf hJ2 aN R₁ R₂ R₃
      (fun l => h.𝔇.pubD.d3.arrayOf.getD l #[]) (hUL_atAll h O) (fun _ _ => rfl)
      (hBlay_of (hBlayB_atAll h O p1)) (fun l _ => hsub_any _ l))
    rfl
    (hAtt_of2_b h.𝔇 dk J h.scope h.reads O O.W hJt _ _ hJl aN R₁ R₂ R₃ (hWn_atAll h)
      (hSec_atAll h (hSecB_atAll h O p1))
      (hAtt2_ofB_b h.𝔇 dk J h.scope h.reads O (hDlk_atAll h) (hlk_atAll h)
        (show headLink Zp.p.X = 24 from O.W ▸ headLink_open h.scope h.reads O) O.W _ _ hJl hJf
        aN R₁ R₂ R₃ (hKl_of_B (hKlB_atAll h O)) (hBatt_of (hBattB_atAll h O p1))
        (fun l _ => hsub_any _ l)))
    rfl O.W
    (hK6_ofJ_b h.𝔇 dk J (P5J.At.num Zp) (P5J.At.layout Zp) hJH h.scope h.reads O (hDlk_atAll h)
      (hlk_atAll h) O.W aN R₁ R₂ R₃ cU hcU (hKw_atAll h (hWide_atAll h O)) h.𝔇.ms (fun _ => 0)
      (fun j => P5J.At.seat3At Zp 24 false j.val) (hLaid6_atAll h)
      (hCalls_atAll h (hCallsB_atAll h O p1)) (hsub_atAll h))
    (hPl_of3_b h.𝔇 dk J (fun s hs => (hJH s hs).1) h.scope h.reads O (hDlk_atAll h) (hlk_atAll h)
      O.W aN R₁ R₂ R₃ cU hcU (hKw_atAll h (hWide_atAll h O))
      (fun X arrs x x' y y' w p A B Fc hp =>
        planesLeft4_atAll_b h O (hArr_atAll h) (hWide_atAll h O) (hLab_atAll h) (shapeH_atAll h)
          dk J aN R₁ R₂ R₃ Fc (hP6 X arrs x x' y y' w p A B Fc hp)))
    (hElse_of_b h.𝔇 dk J hJb h.scope h.reads O (hDlk_atAll h) (hlk_atAll h) O.W aN R₁ R₂ R₃)
    l hl X arrs hX x x' y y' w hy hIn hK hk ht j n hjn p hp A B hA hB

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.arm_at_head_b
