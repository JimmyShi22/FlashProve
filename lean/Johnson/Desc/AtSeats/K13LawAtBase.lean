-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawAt9F
import Johnson.Desc.AtSeats.FillsAtBase
/-
K13's SHARE IN THE COUNTED FORM AT THE COMPOSED MEANING OVER ITS CLOSED BASE, mgAll 𝔇 mgBase (Johnson/Desc/Sound/MgAll.lean), EVERY LETTER OF THE TOP 𝔇's OWN FIELD. General in 𝔇: at the closed structure of parameters P5J.At.𝔇All (Johnson/P5J/LettersAll.lean)
hP is rfl (its P13 := K13.whereOf Zp).
  k13_law_atW      k13_law_at9 with a letter W₁₃ in the place of K13.whereOf Z, under W₁₃ = K13.whereOf Z (so that 𝔇's own P13 can stand there without a cast): by subst.
  **k13_law_atBase**   N · cs · arr · mat · G · smp · ms · decT := 𝔇's; Mg₀ := mgBase. PAID, beside the four on the doors: h0 (base_more) · hFlC (fillsK13C_base) · hrest
                   (inOrder_rides_base) · hFacts (factsK13_of_fold out of First.FoldFacts). COME: hP · three equations that tie the fold's data to 𝔇's (codes · shape · layout).
Both statements were made by program out of k13_law_at9's own binder text.
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

theorem k13_law_atW {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
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
    (hT : OfDesc _ T) (W₁₃ : Where) (hW : W₁₃ = K13.whereOf Z) (N : Numbers) (𝔇 : MgData Xi₉ ProofFile.InstPub Tok rows cols nR₉ X₉)
    (Mg₀ : Meaning ProofFile.InstPub (Desc.Wit (CellsQ rows cols) Tok MsgT)) (h0 : Mg₀.more = {})
    {cs : Codes} (sh : Params.ReqShape) (ly : Params.ReqLayout)
    {arr : ℕ → ℕ → ℕ} {nR : ℕ}
    {mat : (CellsQ rows cols) → Fin nR → (Fin W₁₃.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option (CellsQ rows cols)}
    (N₁₃ : Numbers)
    (rw₁₃ : ProofFile.InstPub × S → Desc.Wit (CellsQ rows cols) Tok MsgT → Wit GE nR W₁₃.lin.kCol)
    (d₁₂ : K12.Door.K12Data) (c₀ : (CellsQ rows cols)) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (ProofFile.InstPub × S) (Desc.Wit (CellsQ rows cols) Tok MsgT) ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (herr : ∀ ds : List RDT, (rest₁ 355 ds).err = _root_.Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hCapB : capB W₁₃ = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hNt : N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : N.index.1 < nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront355 c)))
    (hFlC : FillsK13C W₁₃ N (mgAll 𝔇 Mg₀) cs arr mat G smp ms decT) (hft : d₁₂.ft = 0)
    (hPl : PlanM3 d₁₂.L d₁₂.M ms cs N)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl W₁₃ x x' →
      (mgAll 𝔇 Mg₀).inOrder x = true → (mgAll 𝔇 Mg₀).inOrder x' = true)
    (Rch : ℕ → (ProofFile.InstPub × S) ×
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ j x, Rch j x → x.1.2.failed = none →
      FactsK13 (⟨W₁₃, cs, sh, ly, N₁₃, rw₁₃⟩ : DataK13 _ _ nR) d₁₂ (mgAll 𝔇 Mg₀) x.1)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i))) :
    ∀ i q p, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf Sound.linksFull true)[i]? = some p →
      p.kind = KindName.K13 →
      TiedAtR N (mgAll 𝔇 Mg₀) Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch i
        (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i)) := by
  subst hW
  exact k13_law_at9 hS hR O hT N 𝔇 Mg₀ h0 sh ly N₁₃ rw₁₃ d₁₂ c₀ tokOf hC herr hCapB hWr hNt hNm hbase hFlC hft hPl hsmp
    hdec hrest Rch hFacts hHand

theorem k13_law_atBase {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)}
    {all : List LeftT} {X₁ X₂ Xi Tok : Type} {rows cols nR : ℕ}
    {X₉ : OnBytes.Model.Verify.Public}
    {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hT : OfDesc _ T) (𝔇 : MgData Xi ProofFile.InstPub Tok rows cols nR X₉)
    (hP : 𝔇.P13 = K13.whereOf Z) (f : First.FoldData) (reqW : ProofFile.InstPub → Array UInt32)
    (hcs : 𝔇.cs = f.sent.codes) (hsh : 𝔇.shape = f.sent.shape) (hly : 𝔇.layout = f.sent.layout)
    (c₀ : (CellsQ rows cols)) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (ProofFile.InstPub × S) (Desc.Wit (CellsQ rows cols) Tok MsgT) ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (herr : ∀ ds : List RDT, (rest₁ 355 ds).err = _root_.Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hCapB : capB 𝔇.P13 = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hNt : 𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : 𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : 𝔇.N.index.1 < nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront355 c)))
    (hft : (d12Of f).ft = 0)
    (hPl : PlanM3 (d12Of f).L (d12Of f).M 𝔇.ms 𝔇.cs 𝔇.N)
    (hsmp : SmpReads 𝔇.smp) (hdec : DecBlind 𝔇.decT)
    (Rch : ℕ → (ProofFile.InstPub × S) ×
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (H : First.FoldFacts Rch (fun x => x.1) f reqW Sound.linksFull
      (flatPlacesOf Sound.linksFull true))
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT c₀ tokOf 𝔇.N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i))) :
    ∀ i q p, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf Sound.linksFull true)[i]? = some p →
      p.kind = KindName.K13 →
      TiedAtR 𝔇.N (mgAll 𝔇 mgBase) Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch i
        (q.withMap ((fun k => extQAt 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT c₀ tokOf 𝔇.N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i)) :=
  k13_law_atW hS hR O hT 𝔇.P13 hP 𝔇.N 𝔇 mgBase base_more 𝔇.shape 𝔇.layout 𝔇.N 𝔇.rw13 (d12Of f) c₀ tokOf hC herr hCapB
    hWr hNt hNm hbase (fillsK13C_base 𝔇) hft hPl hsmp hdec (inOrder_rides_base 𝔇 Cl 𝔇.P13) Rch
    (fun j x hr hm => factsK13_of_fold H _ _ _ hcs hsh hly rfl rfl rfl
      (fun q hq y => (fillsK13C_base 𝔇).quiet q (quietC_of_cA13 q hq) y) j x hr hm) hHand

end VerifiableInference.Desc.K13.Law
