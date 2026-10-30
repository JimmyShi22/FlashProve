-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TieGAt9.lean: THE TIE AT THE FIRST SEGMENT's OPENING
(number 2 of the proof file's first chain: one of kind K1's 52 places) IN THE SECOND FORM
(`TiedAtR`), AT A FILLING Mg FROM WHICH THE NINE NAMES HAVE BEEN STRUCK. A definition, and one
statement with its proof: calls. `dG Z cs sh ly N rwD`: K13's data at the seat's own
  numbers. `first_tiedR_at`: at every piece at number 2 of the first row. HOW: `H0_of`
  (Johnson/Desc/K1/Law/H0Of.lean: the first form's exchange) is called AT THE WIDER FILLING
  `plusG (dG …) d dk Mg` (Johnson/Desc/K13/Law/BridgeG.lean); its `RowG` comes from the test with
  code `rowGB` and the numbers' two counts; its `FillG` from `fillG_paid`, whose two structures on
  the letters come from the narrow `FillsK13C` and `MgGC` at Mg; the groups' count from K13's test
  "nothing is sent yet"; `tiedAtR_plusG` carries the tie to Mg.
The premise hmore ("whatever else comes is made") is not asked here:
as a bare premise it would have, by our reading, no member; it is a theorem at the wider filling
(`hmore_plusG`, MoreAtOpening.lean); what that theorem asks stands here
by name. The facts under the condition Rch are asked at borders 2 and 3 alone. The premises that
name the two rounds' plain data d₁ d₂ (hNew, hshown) bear the data's own equation as a third
antecedent: they are asked at the row's own two rounds alone (the first form's exchanges' third
form).
What is not claimed. The premises. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.H0Of
import Johnson.Desc.K13.Law.FillGPaid
import Johnson.Desc.K13.Law.BridgeG
import Johnson.Desc.AtSeats.MoreAtOpening

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
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First.Look (K3Data)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (RowG FillG openAt DataK13 plusG cAG FactsG FillsK13C MgGC
  mgG_plus fillsK13C_live fillsK13_plus weights_plus fits_plus tiedAtR_plusG rowGB rowG_of_test
  fillG_paid PlanG PlanGSeats knownG madeSix weightsItem pileWithinItem oneRowItem bookFitsItem
  DecBlind StepG groups_of_sentence plusG_hand withLive0 frontB openingZero_front)

/-- K13's data at the seat's own numbers. -/
def dG {Pp W : Type} {nR : ℕ} (Z : ProofFile.Pub) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (N : Numbers)
    (rwD : Pp × S → W → K13.Law.Wit GE nR (whereOf Z).lin.kCol) : DataK13 Pp W nR :=
  ⟨whereOf Z, cs, sh, ly, N, rwD⟩

/-- **The tie at the first segment's opening, in the second form, at the narrower filling.** -/
theorem first_tiedR_at
    {P : VerifierAndGoals.PublicFiles}
    {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray}
    {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)}
    {c : Chain S Cl}
    {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat}
    {aN : ℕ}
    {R₁ R₂ R₃ : Rounds}
    {e₁ : List (List ByteArray × ByteArray)}
    {all : List LeftT}
    {X₁ X₂ Xi Cells Tok : Type}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all (ProofFile.fileDescBy OnBytes.secondHashFunction
      ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ (Wit Cells Tok MsgT)}
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (N : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
    (cs : Codes)
    (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs
            s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option Cells)
    (c₀ : Cells)
    (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl}
    {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃)
      all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) (Wit Cells Tok MsgT) ds}
    {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hU : ∃ (e : Block S Cl) (nm : String) (X : LayPar), c.blocksInOrder[2]? = some e ∧
      Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X ∧ e.UnderR (openingZero
      Bs.G₀.first (gpOf Z) nm X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links)
      Z.first.lin.kCol : Block S Cl))
    (hCap : ∀ d₁ d₂ : RDT, (rest₁ 2 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (X : LayPar)
    (hX : Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X)
    (mk : List Pub)
    (rad : ℕ → ℕ)
    (hCond : condPort (firstPar Bs.G₀.first (gpOf Z)) rad = true)
    (h1 : (firstPar Bs.G₀.first (gpOf Z)).seeds = 1)
    (hpow : powB (firstPar Bs.G₀.first (gpOf Z)) rad 128 = true)
    {nR : ℕ}
    (sh : Params.ReqShape)
    (ly : Params.ReqLayout)
    (rwD : ProofFile.InstPub × S → Wit Cells Tok MsgT → K13.Law.Wit GE nR (whereOf Z).lin.kCol)
    (d : K12Data)
    (dk : K3Data)
    (nsOf : ℕ → Option ℕ)
    (dg : Bool)
    (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (hRowB : rowGB (plusG (dG Z cs sh ly N rwD) d dk Mg).more Sound.linksFull psF 2 mk = true)
    (hNt : N.treesAt psF[2 + 1]? = N.treesAt psF[2]? + (layOf (firstPar Bs.G₀.first (gpOf
      Z))).shapes.size)
    (hNm : N.msgsAt psF[2 + 1]? = N.msgsAt psF[2]? + (firstPar Bs.G₀.first (gpOf Z)).sent.size)
    (hFlC : FillsK13C (whereOf Z) N Mg cs arr mat G smp ms decT)
    (hft : d.ft = 0)
    (hGC : MgGC N Mg nsOf dk dg)
    (hUn : ∀ x, Mg.pub .unheard x = First.unheardB x.2)
    (hUP : ∀ x, Mg.pubP .unheard x)
    (hPlG : PlanG X nsOf dk dg sh ly)
    (hm : Pub.noneSent ∈ ((First.pubSets (plusG (dG Z cs sh ly N rwD) d dk Mg).more
      Sound.linksFull psF)[2]?.getD []))
    (hplan : ∀ nm : String, (openingZero Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl).planOk =
      true)
    (hSeats : PlanGSeats d.L d.M N psF[2]? (firstPar Bs.G₀.first (gpOf Z)))
    (hft1 : (firstPar Bs.G₀.first (gpOf Z)).gp.firstTree = 0)
    (hdec : DecBlind decT)
    (hrest : ∀ (nm : String) x x', StepG Cl Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol x x' → Mg.inOrder x =
      true → Mg.inOrder x' = true)
    (hconstr : ∀ (nm : String) x x' y y' w m c', StepG Cl Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol x x' → (∀ q' ∈
      ((First.pubSets (plusG (dG Z cs sh ly N rwD) d dk Mg).more Sound.linksFull psF)[2]?.getD
      []), (plusG (dG Z cs sh ly N rwD) d dk Mg).pub q' x = true) → First.bookAt N psF[2]? x.2 =
      true → y'.cell = y.cell → (plusG (dG Z cs sh ly N rwD) d dk Mg).constr m c' x' y' w → (plusG
      (dG Z cs sh ly N rwD) d dk Mg).constr m c' x y w)
    (built : Array Stages.LinkH)
    (hmk : ∀ i ∈ mk, i ∈ madeSix ∨ i = HashBuild.sentItem0 ∨ i = HashBuild.treesItem0)
    (hSent : ∀ x, Mg.pub HashBuild.sentItem0 x = First.FillSent.sentIsB (First.FillSent.sentDataAt
      sh N Sound.linksFull psF built) 0 x.2)
    (hTrees : ∀ x, Mg.pub HashBuild.treesItem0 x = First.FillSent.treesAreB
      (First.FillSent.sentDataAt sh N Sound.linksFull psF built) 0 x.2)
    (hSP : ∀ x, Mg.pubP HashBuild.sentItem0 x)
    (hTP : ∀ x, Mg.pubP HashBuild.treesItem0 x)
    (hb0 : First.FillSent.baseAt N Sound.linksFull psF 0 = 0)
    (Y : Stages.LinkH)
    (hY : built[0]? = some Y)
    (hYF : Y.Fp = X.X.Fp)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B)
    (hQ : ∀ i ∈ ((First.pubSets (plusG (dG Z cs sh ly N rwD) d dk Mg).more Sound.linksFull
      psF)[2]?.getD []), i = .noneSent ∨ i ∈ knownG ∨ i = weightsItem ∨ i = pileWithinItem ∨ i =
      oneRowItem ∨ i = bookFitsItem)
    (hownB : ownSeatsB N (openAt Sound.linksFull psF (2 + 1)) (firstPar Bs.G₀.first (gpOf Z))
      (((sh.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length (N.treesAt
      psF[2]?) = true)
    (hNew : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) → d₁.kind = .seeds
      → ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] → ∃ (fOf : (Sound.frameAt
      (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → ∀ j, (portOmZ (firstPar
      Bs.G₀.first (gpOf Z)).codes (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) (rad j.val)).Str)
      (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → (wT
      d₁).Msg → ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes (shapeAt (firstPar Bs.G₀.first
      (gpOf Z)) j) (rad j.val)).Str), ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero
      Bs.G₀.first (gpOf Z) nm X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links)
      Z.first.lin.kCol) → (∀ y τ, fOf ((sendPiece (W := Wit Cells Tok MsgT) (F := (Sound.frameAt
      (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂
      R₃).ds₁.take (inFront c 2))) d₁ d₂ (firstPar Bs.G₀.first (gpOf Z)).coordinates (errPort
      (firstPar Bs.G₀.first (gpOf Z)) rad)).ior.imp y τ) = fIn y τ.1) ∧ ∀ (z : ProofFile.InstPub) a τ x,
      onQ N (plusG (dG Z cs sh ly N rwD) d dk Mg) Sound.linksFull psF (fun s : S => (z, s)) 2 a →
      a.1.failed = none → (sendPiece (W := Wit Cells Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁
      R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take
      (inFront c 2))) d₁ d₂ (firstPar Bs.G₀.first (gpOf Z)).coordinates (errPort (firstPar
      Bs.G₀.first (gpOf Z)) rad)).ior.red.out a τ = some x → (∀ j, sampledAt (firstPar Bs.G₀.first
      (gpOf Z)) j → Sealed (firstPar Bs.G₀.first (gpOf Z)).codes (shapeAt (firstPar Bs.G₀.first
      (gpOf Z)) j) (rad j.val) (fOf x.2 j) x.1.st (x.1.st.oracles.size - (shapesOf (firstPar
      Bs.G₀.first (gpOf Z))).length + j.val)) → ∀ t ∈ First.sampledIn N (openAt Sound.linksFull
      psF (2 + 1)), (plusG (dG Z cs sh ly N rwD) d dk Mg).held t.1 t.2 (z, x.1) = true ∧ (plusG
      (dG Z cs sh ly N rwD) d dk Mg).shown t.1 t.2 (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all
      (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) ∧ (plusG (dG Z cs sh ly N rwD) d dk Mg).noColl t.1 t.2
      (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)
      x.2))
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
            R₃).key₁ T.ft₁).E.Str → Prop)
    (hD : doorsFitB Mg.more (plusG (dG Z cs sh ly N rwD) d dk Mg).more cAG Sound.linksFull psF 2 =
      true)
    (hD' : doorsFitB Mg.more (plusG (dG Z cs sh ly N rwD) d dk Mg).more cAG Sound.linksFull psF (2
      + 1) = true)
    (hFacts : ∀ j a, Rch j a → j = 2 ∨ j = 2 + 1 → a.1.2.failed = none → FactsG (dG Z cs sh ly N
      rwD) d dk Mg a.1)
    (hHand : ∀ q, (T.p₁ :: T.l₁)[2]? = some q → HandsOn Rch 2 (q.withMap ((fun k => extQAt cs G
      arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a)
      k) 2))) :
    ∀ q, (T.p₁ :: T.l₁)[2]? = some q →
      TiedAtR N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch 2
        (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull
          (flatPlacesOf Sound.linksFull true) (fun a => a) k) 2)) := by
  intro q hq
  have hFl := fillsK13_plus (dG Z cs sh ly N rwD) d (mat := mat) (smp := smp)
    (fillsK13C_live dk hFlC) hft
  have hG := mgG_plus (dG Z cs sh ly N rwD) d dk hGC
  refine tiedAtR_plusG (dG Z cs sh ly N rwD) d dk Mg N Sound.linksFull psF (fun a => a) Rch 2 _ hD
    hD' hFacts (hHand q hq) ?_
  exact H0_of hS hR O hT N (plusG (dG Z cs sh ly N rwD) d dk Mg) cs G arr smp ms decT c₀ tokOf hC
    hWr hU hCap X hX mk rad hCond h1 hpow (rowG_of_test _ _ _ 2 _ _ mk hRowB N hNt hNm)
    (fun nm => fillG_paid _ _ mk hFl hG
      (fun x => (plusG_hand _ d dk Mg _ rfl x).trans (hUn x)) hUP hPlG hm (hplan nm) hSeats hft1
      hdec
      (fun x x' hst h0 => by
        have h1 : (Mg.inOrder x && frontB x.2) = true := h0
        rw [Bool.and_eq_true] at h1
        obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
        show (Mg.inOrder x' && frontB x'.2) = true
        rw [hrest nm x x' hst h1.1, openingZero_front hd, h1.2]
        rfl)
      (hconstr nm)
      (HashBuild.hmore_plusG (dG Z cs sh ly N rwD) d dk hGC Sound.linksFull psF built _ _ hm mk hmk
        hSent hTrees hSP hTP hb0 Y hY hYF)
      (weights_plus _ d)
      (fun x => hFlC.quiet _ (by decide) x) (fits_plus _ d) (fun x => hFlC.quiet _ (by decide) x)
      hfB hQ)
    (groups_of_sentence hG.noneSent)
    (HashBuild.hown_plusG (dG Z cs sh ly N rwD) d dk N Mg _ _ _ hownB) hNew q hq

end VerifiableInference.Desc.K1
