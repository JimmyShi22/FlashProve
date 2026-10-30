-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
NO EXAMPLE: IT COUNTS FOR NOTHING. 36 of the frozen 38 fields are paid or moved; what is owed: nine tests with code on the public files and two facts at border 342.
«REST → CONDITION» FOR KIND K1: the condition
P5J.AtMgA.K1Cond STANDS FROZEN in Johnson/Desc/AtSeats/K01KindAll.lean (K1Left: 38 fields) AND IS NOT RE-CUT: this file
PAYS FIELDS OF IT. MADE BY PROGRAM out of the same parse that gives the frozen file again byte for byte.
  K1Owed …           a structure of the 11 that are still owed: 2 fields of K1Left TO THE LETTER and 9 smaller ones that come in a paid field's place (hArr · hSecB · hCallsB · h342 · hLab · hKB · hBattB · hBlayB · hMP).
  AtMgA.K1Rest h 𝔏   AT EVERY OPENING OF THE MAKER (∀ Bs base₀, IM.Open … →; the head gives one: h.laid.opened) there are W_rwD · G_rwD with K1Owed at the closed constant's letters.
  k1Cond_of_rest     h.K1Rest 𝔏 → h.K1Cond 𝔏. PAID HERE (36): G_hX · G_hPlG · hUA · hUH · hWX · hJt · hJl · hmono · hidle · hlk · hquiet · hPlanR · hsub · hWn · hU · hKw · ht · hT83 · h4 · W_HP · G_HP · W_hPl3 · hLaid6 · hSec · hAtt'' · hheard · hheard2 · hCalls · hElse · O · W_hFacts · G_hFacts · hFacts · hJH · hPl' · hLay. LETTERS THAT LEAVE THE «∃» (13): Wp · shp · lay₀ · lay6 · msR · num6 · rad6 · seatT · W_y₀ · G_X · cU · Bs · base₀.
  k01_kind_of_rest   h.K1Rest 𝔏 → h.Kind 𝔏 KindName.K1: the two in a row.
IT PAYS NO LAW OF OTHER FILES. What is not claimed. That the rest can be met. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K01KindAll
import Johnson.Desc.AtSeats.PlanGAtAll
import Johnson.Desc.AtSeats.TlAtRch
import Johnson.IMR.AtReach
import Johnson.Desc.Kinds.Law.WtK6Mono
import Johnson.Desc.K1.Law.LinksQuietAtAll
import Johnson.Desc.K1.Law.RadiiAtAllPaid
import Johnson.Desc.K1.Law.HeadNumbersAtAll
import Johnson.Desc.AtSeats.ToldLeftAtAll
import Johnson.Desc.K1.Law.QuietInScope
import Johnson.Desc.AtSeats.PlanAtTwoOfTold
import Johnson.Desc.K1.Law.PlanM3AtAll
import Johnson.Desc.K1.Law.SecAtAll
import Johnson.Desc.K1.Law.ToldAtTwo
import Johnson.Desc.K1.Law.ArmAttMats
import Johnson.Desc.K1.Law.HeardPaid
import Johnson.Desc.K1.Law.CallsAtAll
import Johnson.Desc.AtSeats.RowsBareWalk
import Johnson.Desc.AtSeats.K01FactsWG
import Johnson.Desc.AtSeats.K01FactsAtAll
import Johnson.Desc.AtSeats.TablesAtHead
import Johnson.Desc.AtSeats.ArmAtRch
import Johnson.Desc.K1.Law.ArmPlanesLen
import Johnson.Desc.K1.Law.ArmLayMats
import Johnson.Desc.K1.Law.ArmAttIn
import Johnson.Desc.K1.Law.ArmLayIn
import Johnson.Desc.K1.Law.ArmLettersB
import Johnson.Desc.K1.Law.PlanesAtAll
import Johnson.Desc.AtSeats.FirstSeatedAtLinkNo
import Johnson.Desc.AtSeats.LiveAtRch
import Johnson.Desc.AtSeats.PlanZeroAtAll
import Johnson.Desc.AtSeats.ULayAtAll
import Johnson.Desc.AtSeats.RowsBareAtHead
import Johnson.Desc.AtSeats.PadAtRch
import Johnson.Desc.K1.Law.PlanesLeft6AtAll
import Johnson.Desc.K1.Law.SymsHalvesB
import Johnson.Desc.K1.Law.ShapeAtAll
import Johnson.Desc.K1.Law.LedgersAtAll

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
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)

/-- **What is still owed of K1Left**, at its own letters. -/
structure K1Owed
    (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub)
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV)
    (D : WholeD)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt D (Sound.allOf D) D.key₁ 0).E.Str → Prop)
    (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout)
    (msR : List Mem)
    (lay6 : OnBytes.Params.ReqLayout)
    (num6 : ℕ → ℕ → ℕ)
    (rad6 : OnBytes.OracleShape → ℕ)
    (seatT : Fin (sigListCalls Dm.sent rad6 24).length → ℕ × ℕ)
    (W_nWr : ℕ)
    (W_rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE W_nWr (whereOf
            Z).lin.kCol)
    (G_nGr : ℕ)
    (G_rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE G_nGr (whereOf
            Z).lin.kCol) : Prop where
  hArr : readsArrB Z.made.p.built.links Z.p.X = true
  hSecB : secB Z.made.p.built.links Z.p.X shp lay₀ = true
  hCallsB : callsB (colFourB XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num6 Dm.sent rad6 24 seatT = true
  h342 : ∀ a, Rch (14 * 24 + k1Ix 24 false + 2) a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * 24 + k1Ix 24 false + 2) a → a.1.2.failed = none → JHead XV (Dm.N.sent 24 0) Dm.arr Dm.N num6 lay6 a.1.2
  hLab : labPB Z.made.p.built.links Z.p.X = true
  hKB : layKB XV 0 = true
  hBattB : battB Dm.pubD.d3.arrayOf XV lay₀ shp = true
  hBlayB : blayB Dm.pubD.d3.arrayOf XV lay₀ shp = true
  hMP : ∀ a, Rch 342 a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a → a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK → VerifiableInference.Desc.Kinds.Head.Law.MatsSeated (fun μ _ => μ = XV.hS.NHf + 2) Dm.arr Dm.N XV (Dm.N.sent 24 0) aK num6 lay6
  pin1 : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true
  pin2 : VerifiableInference.PlanWritten.cutIs F = true

end

section
open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : First.Look.Place}

/-- ArmOk at the closed J, along «reached and typed»: the proof of armOk_at_rch, line for line, with the state in
front taken at the typed relation (there J holds by its own definition). -/
theorem armOk_at_pub (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) j a → onQ h.𝔇.N (mgAll h.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
      ArmOk (JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) h.𝔇.N (mgAll h.𝔇 mgBase)) a.1.2 := by
  intro l hl d j hj a hr hon hm
  cases d with
  | true =>
    exact armOk_three_rchAt _ h.scope h.reads O l hl j
      (hj.elim (fun e => .inr (.inl e)) fun e => .inr (.inr e)) a hr.1
  | false =>
    rcases hj with rfl | rfl
    · exact fun _ => jReach_at _ _ _ l hl a hr hon hm
    · exact armOk_three_rchAt _ h.scope h.reads O l hl _ (.inl rfl) a hr.1

/-- JH along «reached and typed» in front of the reads: the proof of jH_at_reads, line for line, with the one fact
that is owed (JHead at border 342) asked at the typed relation alone. -/
theorem jH_at_pub (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (X : OnBytes.Model.Verify.Public) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (N : Numbers) (num : ℕ → ℕ → ℕ)
    (lay6 : OnBytes.Params.ReqLayout)
    (h342 : ∀ a, (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) (14 * 24 + k1Ix 24 false + 2) a → onQ h.𝔇.N (mgAll h.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * 24 + k1Ix 24 false + 2) a →
      a.1.2.failed = none → JHead X own arr N num lay6 a.1.2) :
    ∀ l, l < 25 → ∀ a, (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) (14 * l + k1Ix l false + 2) a → onQ h.𝔇.N (mgAll h.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → JH X own arr N num lay6 a.1.2 := by
  intro l hl a hr hon hm
  refine ⟨noTables_at_reads h.scope h.reads O _ _ l hl a hr.1 hon hm, ?_⟩
  by_cases h24 : l = 24
  · subst h24
    exact h342 a hr hon hm
  · exact jHead_low X own arr N num lay6 l (by omega) a.1 _ ⟨hon, hm⟩

/-- **What is still owed, at the closed constant.** -/
def _root_.P5J.AtMgA.K1Rest (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (_𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  ∀ Bs base₀, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
  ∃ W_rwD G_rwD,
    K1Owed (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
      Zp
      h.𝔇
      (D.at frS.P.T.a)
      (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub)
      h.𝔇.shape
      h.𝔇.layout
      h.𝔇.ms
      (P5J.At.layout Zp)
      (P5J.At.num Zp)
      (fun _ => 0)
      (fun j => P5J.At.seat3At Zp 24 false j.val)
      OnBytes.Flat.numsFull.rows
      W_rwD
      OnBytes.Flat.numsFull.rows
      G_rwD

/-- **Rest → condition.** -/
theorem _root_.P5J.k1Cond_of_rest (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (R : h.K1Rest 𝔏) : h.K1Cond 𝔏 := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have R := R Bs base₀ O
  obtain ⟨W_rwD, G_rwD, R⟩ := R
  obtain ⟨G_X, hGX⟩ := G_hX_atAll h O
  obtain ⟨cU, hcU⟩ := hU_atAll h R.hArr
  exact ⟨Bs, base₀, (P5J.At.X Zp), h.𝔇.shape, h.𝔇.layout, cU, h.𝔇.ms, (P5J.At.layout Zp), (P5J.At.num Zp), (fun _ => 0), (fun j => P5J.At.seat3At Zp 24 false j.val), W_rwD, default, G_X, G_rwD,
    { pin1 := R.pin1
      pin2 := R.pin2
      O := O
      hmono := VerifiableInference.Desc.Kinds.Head.Law.AtTable.hmono_atAll h
      hheard := hheard_paid h.𝔇 _ _ h.scope h.reads O (hDlk_atAll h) (hlk_atAll h) O.W true
      hPlanR := hPlanR_paid h O R.pin1 R.pin2
      hFacts := K13.Law.factsK1_atAllQ h R.pin1 (xbK Bs.G₀ _) link_two (fun l hl d j hj a hr hon hm => (xbK_iff _ _ _).2 ⟨tablesOk_at_rch_all h.scope h.reads O _ _ l hl d j hj a hr.1 hon hm, armOk_at_pub h O l hl d j hj a hr hon hm⟩)
      hLay := fun td R₁ R₂ R₃ _ _ => hLay_ofB h.𝔇 _ _ h.scope h.reads O O.W _ _ (jLive_atAll h) (jReach_elim _ _ _ (JFirst _) (fun l hl a hr hon hm => jFirst_at_reads h R.pin1 (VerifiableInference.PlanWritten.cutIs_eq R.pin2).1 l hl a hr.1 hon hm)) (jReach_elim _ _ _ (JLay2 _) (fun l hl a hr => jLay2_paid h.𝔇 h.scope h.reads O (hOk_atAll h O) (hDlk_atAll h) (hlk_atAll h) O.W R.hKB _ _ l hl a hr.1)) td R₁ R₂ R₃ (fun l => h.𝔇.pubD.d3.arrayOf.getD l #[]) (hUL_atAll h O) (fun _ _ => rfl) (hBlay_of R.hBlayB) (fun l _ => hsub_any _ l)
      hUA := rfl
      hJt := jReach_elim _ _ _ (TlIsPlan _) (fun l hl a hr => tlIsPlan_at_reads h.scope h.reads O O.W _ _ l hl a hr.1)
      hJl := jLive_atAll h
      hWn := hWn_atAll h
      hSec := hSec_atAll h R.hSecB
      hAtt'' := fun td R₁ R₂ R₃ _ _ => hAtt2_ofB h.𝔇 _ _ h.scope h.reads O (hDlk_atAll h) (hlk_atAll h) (show headLink Zp.p.X = 24 from O.W ▸ headLink_open h.scope h.reads O) O.W _ _ (jLive_atAll h) (jReach_elim _ _ _ (JFirst _) (fun l hl a hr hon hm => jFirst_at_reads h R.pin1 (VerifiableInference.PlanWritten.cutIs_eq R.pin2).1 l hl a hr.1 hon hm)) td R₁ R₂ R₃ (hKl_of_B (hKlB_atAll h O)) (hBatt_of R.hBattB) (fun l _ => hsub_any _ l)
      hUH := rfl
      hWX := O.W
      hU := hcU
      hKw := hKw_atAll h (hWide_atAll h O)
      hLaid6 := hLaid6_atAll h
      hCalls := hCalls_atAll h R.hCallsB
      hJH := jReach_elim _ _ _ (JH _ _ _ _ _ _) (jH_at_pub h O _ _ _ _ _ _ R.h342)
      hsub := hsub_atAll h
      hPl' := fun td R₁ R₂ R₃ e₁ e₂ X arrs x x' y y' w p A B Fc hp => planesLeft4_atAll h O R.hArr (hWide_atAll h O) R.hLab (shapeH_atAll h) _ _ td R₁ R₂ R₃ Fc (planesLeft6_atAll h _ K13.Law.typedPub (P5J.At.num Zp) R.hMP td R₁ R₂ R₃ Fc)
      hElse := fun td R₁ R₂ R₃ _ _ => hElse_of h.𝔇 _ _ (jReach_elim _ _ _ RowsBareH (fun l hl a hr => rowsBareH_at_reads h.scope h.reads O (k3Bare_of h.scope h.reads O (hOk_atAll h O)) _ _ l hl a hr.1)) h.scope h.reads O (hDlk_atAll h) (hlk_atAll h) O.W td R₁ R₂ R₃
      hlk := hlk_atAll h
      ht := ht_atAll
      hT83 := hT83_atAll _
      h4 := h4_atAll h O R.pin1 R.pin2
      hidle := VerifiableInference.Desc.Kinds.Head.Law.AtTable.hidle_atAll h
      hheard2 := hheard_paid h.𝔇 _ _ h.scope h.reads O (hDlk_atAll h) (hlk_atAll h) O.W false
      hquiet := hquiet_in_scope h.scope h.reads O
      W_hPl3 := W_hPl3_atAll h R.pin1 R.pin2 rfl rfl
      W_HP := W_HP_of_told h O R.pin1 R.pin2 (htoldW_atAll h R.pin2)
      W_hFacts := K13.Law.W_hFacts_atAll h R.pin1 _ W_rwD
      G_hX := hGX
      G_hPlG := G_hPlG_atAll h hGX (planG_atAll h O)
      G_HP := G_HP_of_told h O R.pin1 R.pin2 (htoldG_atAll h R.pin2)
      G_hFacts := K13.Law.G_hFacts_atAll h R.pin1 G_rwD }⟩

/-- The two in a row. -/
theorem _root_.P5J.k01_kind_of_rest (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : h.K1Rest 𝔏) : h.Kind 𝔏 KindName.K1 :=
  P5J.k01_kind_all h 𝔏 q₁ q₂ q₃ (P5J.k1Cond_of_rest h 𝔏 R)

end

end VerifiableInference.Desc.K1
