-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawKindR
import Johnson.Desc.AtSeats.DoorAt9
/-
K13's SHARE OF THE CHAIN OF PROMISES IN THE SECOND FORM, AT THE COMPOSED MEANING mgAll 𝔇 Mg₀ (Johnson/Desc/Sound/MgAll.lean) (the small door; the 9 in the names here marks it), over a base whose door is empty.
k13_law_kindR at Mg₉ := mgAll 𝔇 Mg₀; ITS FOUR PREMISES ON DOORS (hRowB · hIn · hQ · hDoors) ARE PAID BY THE KERNEL (doors_at_mgAll9); one comes: Mg₀.more = {}.
The statement was made by program out of k13_law_kindR's own binder text.
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

theorem k13_law_at9 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)}
    {all : List LeftT} {X₁ X₂ Xi Xi₉ Tok : Type} {rows cols nR₉ : ℕ}
    {X₉ : OnBytes.Model.Verify.Public}
    {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hT : OfDesc _ T) (N : Numbers) (𝔇 : MgData Xi₉ ProofFile.InstPub Tok rows cols nR₉ X₉)
    (Mg₀ : Meaning ProofFile.InstPub (Desc.Wit (CellsQ rows cols) Tok MsgT)) (h0 : Mg₀.more = {})
    {cs : Codes} (sh : Params.ReqShape) (ly : Params.ReqLayout)
    {arr : ℕ → ℕ → ℕ} {nR : ℕ}
    {mat : (CellsQ rows cols) → Fin nR → (Fin (K13.whereOf Z).lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option (CellsQ rows cols)}
    (N₁₃ : Numbers)
    (rw₁₃ : ProofFile.InstPub × S → Desc.Wit (CellsQ rows cols) Tok MsgT → Wit GE nR (K13.whereOf Z).lin.kCol)
    (d₁₂ : K12.Door.K12Data) (c₀ : (CellsQ rows cols)) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (ProofFile.InstPub × S) (Desc.Wit (CellsQ rows cols) Tok MsgT) ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (herr : ∀ ds : List RDT, (rest₁ 355 ds).err = _root_.Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hCapB : capB (K13.whereOf Z) = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hNt : N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : N.index.1 < nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront355 c)))
    (hFlC : FillsK13C (K13.whereOf Z) N (mgAll 𝔇 Mg₀) cs arr mat G smp ms decT) (hft : d₁₂.ft = 0)
    (hPl : PlanM3 d₁₂.L d₁₂.M ms cs N)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl (K13.whereOf Z) x x' →
      (mgAll 𝔇 Mg₀).inOrder x = true → (mgAll 𝔇 Mg₀).inOrder x' = true)
    (Rch : ℕ → (ProofFile.InstPub × S) ×
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ j x, Rch j x → x.1.2.failed = none →
      FactsK13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ (mgAll 𝔇 Mg₀) x.1)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i))) :
    ∀ i q p, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf Sound.linksFull true)[i]? = some p →
      p.kind = KindName.K13 →
      TiedAtR N (mgAll 𝔇 Mg₀) Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch i
        (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i)) :=
  have hd := doors_at_mgAll9 𝔇 Mg₀ h0 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂
  k13_law_kindR hS hR O hT N (mgAll 𝔇 Mg₀) sh ly N₁₃ rw₁₃ d₁₂ c₀ tokOf hC herr hCapB hWr hd.1 hNt hNm hbase hFlC
    hft hPl hd.2.1 hd.2.2.1 hsmp hdec hrest Rch hd.2.2.2 hFacts hHand

end VerifiableInference.Desc.K13.Law
