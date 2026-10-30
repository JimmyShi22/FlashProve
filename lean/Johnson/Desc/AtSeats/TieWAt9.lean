-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TieWAt9.lean: THE TIE AT W's COMMITMENT (number 356 of the
proof file's first chain: one of kind K1's 52 places) IN THE SECOND FORM (`TiedAtR`), AT A FILLING
Mg FROM WHICH THE EIGHT NAMES HAVE BEEN STRUCK. A definition, and one statement with its proof:
calls. `dW Z msg sh ly N rwD`: our layer's data at the seat's own numbers and the sending's own
  codes. `w_tiedR_at`: at every piece at number 356 of the first row. HOW: `HW_of`
  (the first form's exchange) is called AT THE WIDER FILLING `plus13 (dW …) d
    Mg`; its `RowM4` comes from the test with code `rowM4B` and the numbers' two counts; its
    `FillM4` from `fillM4_paid6`, whose structure on the letters comes from the narrow `FillsK13C`
    at Mg by `fillsK13_plus`; `tiedAtR_plus13` carries the tie to Mg.
The premises that name the two rounds' plain data d₁ d₂ (hNew, hshown) bear the
data's own equation as a third antecedent: they are asked at the row's own two rounds alone (the
first form's exchanges' third form). As they were bound (two tags on d₁, none on d₂) we had marked
them "in doubt". What is not claimed. The premises. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.HWOf
import Johnson.Desc.K13.Law.FillM4Paid6
import Johnson.Desc.K13.Law.FillsK13C

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (RowM4 FillM4 wSitsItem wSitsB planSitsB planSeatB DataK13
  plus13 cA13 FactsK13 FillsK13C fillsK13_plus weights_plus fits_plus tiedAtR_plus13 rowM4B
  rowM4_of_test fillM4_paid6 PlanM3 PlanM4 knownK13 weightsItem pileWithinItem oneRowItem
  bookFitsItem SmpOld DecBlind StepM4 quietC)

/-- Our layer's data at the seat's own numbers and the sending's own codes. -/
def dW {Pp W : Type} {nR : ℕ} (Z : ProofFile.Pub) (msg : Array OracleNotice) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (N : Numbers)
    (rwD : Pp × S → W → K13.Law.Wit GE nR (whereOf Z).lin.kCol) : DataK13 Pp W nR :=
  ⟨whereOf Z, (parWZ Z msg).codes, sh, ly, N, rwD⟩

/-- **The tie at W's commitment, in the second form, at the narrower filling.** -/
theorem w_tiedR_at {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {e₁ : List (List ByteArray × ByteArray)} {all : List LeftT} {X₁ X₂ Xi Cells Tok : Type}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit Cells Tok MsgT)}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option Cells)
    (c₀ : Cells) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) →
      Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)
        (ProofFile.InstPub × S) (Wit Cells Tok MsgT) ds}
    {r : Fmt.RoundView} (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ d₁ d₂ : RDT, (rest₁ 356 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (msg : Array OracleNotice) (hm : linMessageW Z.first.lin = some msg) (rad : ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf (parWZ Z msg).codes s.l).om i).Smp)
    (hCond : condPort (parWZ Z msg) rad = true) (h1 : (parWZ Z msg).seeds = 1)
    (hpow : powB (parWZ Z msg) rad 128 = true)
    {nR : ℕ} (sh : Params.ReqShape) (ly : Params.ReqLayout)
    (rwD : ProofFile.InstPub × S → Wit Cells Tok MsgT → K13.Law.Wit GE nR (whereOf Z).lin.kCol)
    (d : K12Data) (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (y₀ : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str)
    (hRowB : rowM4B (plus13 (dW Z msg sh ly N rwD) d Mg).more Sound.linksFull psF 356 = true)
    (hNt : N.treesAt psF[356 + 1]? = N.treesAt psF[356]? + (layOf (parWZ Z msg)).shapes.size)
    (hNm : N.msgsAt psF[356 + 1]? = N.msgsAt psF[356]? + (parWZ Z msg).sent.size)
    (hFlC : FillsK13C (whereOf Z) N Mg (parWZ Z msg).codes arr mat G smp ms decT) (hft : d.ft = 0)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B)
    (hPl3 : PlanM3 d.L d.M ms (parWZ Z msg).codes N)
    (h4 : PlanM4 0 d.L d.M N psF[356]? (parWZ Z msg))
    (hplan : (atM4 (Cl := Cl) (whereOf Z) (sendAtS (parWZ Z msg))).planOk = true)
    (hQ : ∀ q ∈ (First.pubSets (plus13 (dW Z msg sh ly N rwD) d Mg).more Sound.linksFull
    psF)[356]?.getD [],
      q ∈ knownK13 ∨ q = .frontOk ∨ q = weightsItem ∨ q = pileWithinItem ∨ q = oneRowItem ∨
        q = bookFitsItem)
    (hIn : ∀ q ∈ knownK13,
      q ∈ (First.pubSets (plus13 (dW Z msg sh ly N rwD) d Mg).more Sound.linksFull psF)[356]?.getD
      [])
    (hsmp : SmpOld N psF[356]? ms smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM4 Cl (whereOf Z) (parWZ Z msg) x x' → Mg.inOrder x = true →
      Mg.inOrder x' = true)
    (hPl : wSitsItem ∈ (First.pubSets (plus13 (dW Z msg sh ly N rwD) d Mg).more Sound.linksFull
    psF)[356 + 1]?.getD [] →
      planSitsB (whereOf Z) (parWZ Z msg) = true ∧ planSeatB N psF[356]? (parWZ Z msg) = true)
    (hbase : N.index.1 < nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
    (hNew : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds → ((dataOf aN R₁ R₂
        R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val)).Str),
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msg))) →
      (∀ y τ, fOf ((sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates
        (errPort (parWZ Z msg) rad)).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N (plus13 (dW Z msg sh ly N rwD) d Mg) Sound.linksFull psF (fun s : S => (z, s)) 356 a →
      a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates
        (errPort (parWZ Z msg) rad)).ior.red.out a τ = some x →
      (∀ j, sampledAt (parWZ Z msg) j →
        Sealed (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msg)).length + j.val)) →
      (wSitsItem ∈ (First.pubSets (plus13 (dW Z msg sh ly N rwD) d Mg).more Sound.linksFull
      psF)[356 + 1]?.getD [] →
        wSitsB (parWZ Z msg).codes (whereOf Z) x.1 = true ∧
          x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z msg)).length]? = some N.w) →
      (plus13 (dW Z msg sh ly N rwD) d Mg).held N.w.1 N.w.2 (z, x.1) = true ∧
        (plus13 (dW Z msg sh ly N rwD) d Mg).noColl N.w.1 N.w.2 (z, x.1)
          (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    (hshown : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds → ((dataOf aN R₁
        R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msg))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N (plus13 (dW Z msg sh ly N rwD) d Mg) Sound.linksFull psF (fun s : S => (z, s)) 356 a →
      a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates
        (errPort (parWZ Z msg) rad)).ior.red.out a τ = some x →
      (plus13 (dW Z msg sh ly N rwD) d Mg).shown N.w.1 N.w.2
        (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    (Rch : ℕ → (ProofFile.InstPub × S) ×
      (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hD : doorsFitB Mg.more (plus13 (dW Z msg sh ly N rwD) d Mg).more cA13 Sound.linksFull psF 356
    = true) (hD' : doorsFitB Mg.more (plus13 (dW Z msg sh ly N rwD) d Mg).more cA13
    Sound.linksFull psF (356 + 1) = true)
    (hFacts : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13 (dW Z msg sh ly N rwD) d Mg a.1)
    (hHand : ∀ q, (T.p₁ :: T.l₁)[356]? = some q → HandsOn Rch 356
      (q.withMap ((fun k => extQAt (parWZ Z msg).codes G arr smp ms decT c₀ tokOf N Sound.linksFull
        (flatPlacesOf Sound.linksFull true) (fun a => a) k) 356))) :
    ∀ q, (T.p₁ :: T.l₁)[356]? = some q →
      TiedAtR N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch 356
        (q.withMap ((fun k => extQAt (parWZ Z msg).codes G arr smp ms decT c₀ tokOf N
        Sound.linksFull
          (flatPlacesOf Sound.linksFull true) (fun a => a) k) 356)) := by
  intro q hq
  have hFl := fillsK13_plus (dW Z msg sh ly N rwD) d (mat := mat) (smp := smp) hFlC hft
  refine tiedAtR_plus13 (dW Z msg sh ly N rwD) d Mg N Sound.linksFull psF (fun a => a) Rch 356 _ hD
    hD' hFacts (hHand q hq) ?_
  exact HW_of hS hR O hT N (plus13 (dW Z msg sh ly N rwD) d Mg) (parWZ Z msg).codes G arr smp ms
    decT c₀ tokOf hC hWr hCap msg hm rad hCond h1 hpow
    (rowM4_of_test _ _ _ 356 _ _ hRowB N hNt hNm)
    (fillM4_paid6 y₀ _ _ hFl (weights_plus _ d) (fun x => hFlC.quiet _ (by decide) x)
      (fits_plus _ d) (fun x => hFlC.quiet _ (by decide) x) hfB hPl3 h4 hplan hQ hIn hsmp
      hdec hrest)
    hPl hbase hNew hshown q hq

end VerifiableInference.Desc.K1
