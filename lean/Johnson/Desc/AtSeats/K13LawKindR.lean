-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawTop
import Johnson.Desc.K13.Law.BridgeKind
import Johnson.Desc.K13.Law.FillsK13C
/-
K13's SHARE OF THE CHAIN OF PROMISES IN THE SECOND FORM: THE KIND's FORM, WITH THE PREMISES ON THE FILLING AT THE NARROWER Mg₉.
As in K13LawTopR.lean (a file of this project that is not in this library): k13_law_top AS IT STANDS at the wider filling plus13 … Mg₉; OTHERWISE THAN THERE: carried by kind_plus13 (the kind's form: at every
place of the kind) · FillsK13 at the wider filling by fillsK13_plus from FillsK13C AT Mg₉ and d₁₂.ft = 0 · «pubP says nothing» at the two riders out of
FillsK13C's field quiet · what the wider filling says at the two riders: rfl · ONE Bool on the two doors at all borders (doorsFitAllB) · the facts are
asked at REACHED AND UNMARKED states alone.
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

/-- Our layer's data at the place's own parameters. -/
def d13At {W : Type} {nR : ℕ} (Z : ProofFile.Pub) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (N₁₃ : Numbers)
    (rw₁₃ : ProofFile.InstPub × S → W → Wit GE nR (K13.whereOf Z).lin.kCol) :
    DataK13 ProofFile.InstPub W nR := ⟨K13.whereOf Z, cs, sh, ly, N₁₃, rw₁₃⟩

theorem k13_law_kindR {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)}
    {all : List LeftT} {X₁ X₂ Xi Cells Tok : Type}
    {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit Cells Tok MsgT)}
    (hT : OfDesc _ T) (N : Numbers) (Mg₉ : Meaning ProofFile.InstPub (Desc.Wit Cells Tok MsgT))
    {cs : Codes} (sh : Params.ReqShape) (ly : Params.ReqLayout)
    {arr : ℕ → ℕ → ℕ} {nR : ℕ}
    {mat : Cells → Fin nR → (Fin (K13.whereOf Z).lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option Cells}
    (N₁₃ : Numbers)
    (rw₁₃ : ProofFile.InstPub × S → Desc.Wit Cells Tok MsgT → Wit GE nR (K13.whereOf Z).lin.kCol)
    (d₁₂ : K12.Door.K12Data) (c₀ : Cells) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (ProofFile.InstPub × S) (Desc.Wit Cells Tok MsgT) ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (herr : ∀ ds : List RDT, (rest₁ 355 ds).err = _root_.Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hCapB : capB (K13.whereOf Z) = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hRowB : rowM3B (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉).more Sound.linksFull (flatPlacesOf Sound.linksFull true) 355 = true)
    (hNt : N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : N.index.1 < nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront355 c)))
    (hFlC : FillsK13C (K13.whereOf Z) N Mg₉ cs arr mat G smp ms decT) (hft : d₁₂.ft = 0)
    (hPl : PlanM3 d₁₂.L d₁₂.M ms cs N)
    (hIn : bookItem ∈ (First.pubSets (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉).more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [] ∧
      seatsItem ∈ (First.pubSets (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉).more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [] ∧
      shapesItem ∈ (First.pubSets (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉).more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [])
    (hQ : ∀ q ∈ (First.pubSets (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉).more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [],
      q ∈ knownK13 ∨ q = weightsItem ∨ q = pileWithinItem ∨ q = oneRowItem ∨ q = bookFitsItem)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl (K13.whereOf Z) x x' →
      Mg₉.inOrder x = true → Mg₉.inOrder x' = true)
    (Rch : ℕ → (ProofFile.InstPub × S) ×
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hDoors : doorsFitAllB Mg₉.more (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉).more cA13
      Sound.linksFull (flatPlacesOf Sound.linksFull true) = true)
    (hFacts : ∀ j x, Rch j x → x.1.2.failed = none →
      FactsK13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉ x.1)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i))) :
    ∀ i q p, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf Sound.linksFull true)[i]? = some p →
      p.kind = KindName.K13 →
      TiedAtR N Mg₉ Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch i
        (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i)) :=
  kind_plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉ N Sound.linksFull
    (flatPlacesOf Sound.linksFull true) _ (T.p₁ :: T.l₁) Rch KindName.K13 hDoors hFacts hHand
    (k13_law_top hS hR O hT N (plus13 (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ Mg₉) c₀ tokOf hC herr hCapB hWr hRowB hNt hNm hbase
      (fillsK13_plus (d13At Z cs sh ly N₁₃ rw₁₃) d₁₂ hFlC hft) (fun _ => rfl)
      (fun x => hFlC.quiet _ (by decide) x) (fun _ => rfl)
      (fun x => hFlC.quiet _ (by decide) x) hPl hIn hQ hsmp hdec hrest)

end VerifiableInference.Desc.K13.Law
