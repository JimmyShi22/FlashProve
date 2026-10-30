-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawAtThree
/-
THE ROW's STATEMENT, BY A DECISION IN THIS PROJECT ON HOW A ROW COUNTS: THE TIGHT FORM: k13_law_atThree (Johnson/Desc/AtSeats/K13LawAtThree.lean) with, in the one structure FoldFacts' place, JUST WHAT THE ROW SPENDS: FactsK13's own fields at reached, unmarked states: K13's own
conjunct of «in order» (tidy · codes · shape · layout) · pileMasks · pileWithin · oneRow · weightsOk · bookInOrder · seatsCarried · msgShapes · bookFits · and pubP's silence at the eight (which is paid at the closed base).
The weaker premise, so the stronger theorem; k13_law_atThree is its corollary by factsK13_of_fold.
NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)

open _root_.Desc.K14.Law (roundsIn)
open OnBytes.Params (Rounds)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (Pub)
open VerifiableInference.Desc.Sound (TiedAtR HandsOn)

open VerifiableInference.Desc.Sound (mgAll MgData CellsQ)

open VerifiableInference.Desc.Sound (mgBase)

open VerifiableInference.Desc.Sound (mgBase threeCap four_together)

open VerifiableInference.Desc.Sound (mgBase threeCap four_together)

theorem k13_law_atThreeT {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {D : WholeD} {file : String} (hD : (FD Z A B c).data file = .ok D)
    (hp : (FD Z A B c).planOk = true)
    {b₁ : Block (FD Z A B c).S₁ (FD Z A B c).Cl} {l₁ : List (Block (FD Z A B c).S₁ (FD Z A B c).Cl)}
    {b₂ : Block (FD Z A B c).S₂ (FD Z A B c).Cl} {l₂ : List (Block (FD Z A B c).S₂ (FD Z A B c).Cl)}
    {b₃ : Block (FD Z A B c).S₃ (FD Z A B c).Cl} {l₃ : List (Block (FD Z A B c).S₃ (FD Z A B c).Cl)}
    (q₁ : (FD Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Z A B c).second.blocksInOrder = b₃ :: l₃)
    {Xi Tok : Type} {rows cols nR : ℕ} {X₉ : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi ProofFile.InstPub Tok rows cols nR X₉)
    (hP : 𝔇.P13 = K13.whereOf Z) (d₁₂ : K12.Door.K12Data)
    (e₁ : (i : ℕ) → (ds : List RDT) →
      ((FD Z A B c).XiPub × (FD Z A B c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → (Desc.Wit (CellsQ rows cols) Tok MsgT) → (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) →
      (((FD Z A B c).XiPub × (FD Z A B c).S₁) × (FD Z A B c).S₂) ×
        (frameAt D (allOf D) D.key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → (Desc.Wit (CellsQ rows cols) Tok MsgT) → (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) →
      (((FD Z A B c).XiPub × (FD Z A B c).S₁ × (FD Z A B c).S₂) × (FD Z A B c).S₃) ×
        (frameAt D (allOf D) D.key₃ (FD Z A B c).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → (Desc.Wit (CellsQ rows cols) Tok MsgT) → (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (dW wEnd : (Desc.Wit (CellsQ rows cols) Tok MsgT)) (c₀ : CellsQ rows cols) (tokOf : ProofFile.InstPub × S → Tok)
    (hCapB : capB 𝔇.P13 = true)
    (hNt : 𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : 𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : 𝔇.N.index.1 < nTrees (D.ds₁.take (inFront355 c)))
    (hft : d₁₂.ft = 0) (hPl : PlanM3 d₁₂.L d₁₂.M 𝔇.ms 𝔇.cs 𝔇.N)
    (hsmp : SmpReads 𝔇.smp) (hdec : DecBlind 𝔇.decT)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (hFacts : ∀ j x, Rch j x → x.1.2.failed = none →
      FactsK13 (⟨𝔇.P13, 𝔇.cs, 𝔇.shape, 𝔇.layout, 𝔇.N, 𝔇.rw13⟩ : DataK13 _ _ nR) d₁₂ (mgAll 𝔇 mgBase) x.1)
    (hHand : ∀ i q, ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[i]? = some q →
      HandsOn Rch i (q.withMap ((fun k => extQAt 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT c₀ tokOf 𝔇.N Sound.linksFull
        (flatPlacesOf Sound.linksFull true) (fun a => a) k) i))) :
    ∀ i q p, ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[i]? = some q →
      (flatPlacesOf Sound.linksFull true)[i]? = some p → p.kind = KindName.K13 →
      TiedAtR 𝔇.N (mgAll 𝔇 mgBase) Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch i
        (q.withMap ((fun k => extQAt 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT c₀ tokOf 𝔇.N Sound.linksFull
        (flatPlacesOf Sound.linksFull true) (fun a => a) k) i)) := by
  obtain ⟨R₁, R₂, R₃, hDD, w₁, hall⟩ := four_together (W := (Desc.Wit (CellsQ rows cols) Tok MsgT)) hD hp q₁ q₂ q₃
  subst hDD
  obtain ⟨hT, hC, herr⟩ := hall e₁ e₂ e₃ dW wEnd
  exact k13_law_atW hS hR O hT 𝔇.P13 hP 𝔇.N 𝔇 mgBase base_more 𝔇.shape 𝔇.layout 𝔇.N 𝔇.rw13 d₁₂ c₀ tokOf hC
    (fun ds => herr 355 ds) hCapB w₁ hNt hNm hbase (fillsK13C_base 𝔇) hft hPl hsmp hdec
    (inOrder_rides_base 𝔇 Cl 𝔇.P13) Rch hFacts hHand

end VerifiableInference.Desc.K13.Law
