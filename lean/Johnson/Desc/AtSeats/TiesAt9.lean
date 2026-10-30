-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TiesAt9.lean: THE TIES AT W's COMMITMENT (356) AND AT THE
FIRST SEGMENT's OPENING (2): TWO OF KIND K1's 52 PLACES: IN THE SECOND FORM (`TiedAtR`), AT THE
COMPOSED FILLING OVER ITS CLOSED BASE: `mgAll 𝔇 mgBase`. Two
statements, made by program out of `w_tiedR_at` and `first_tiedR_at` (TieWAt9.lean,
TieGAt9.lean): each a call. WHAT FALLS AGAINST THE GENERAL FORMS: every premise that reads doors
alone: by the kernel (DoorAt9WG.lean): six at 356 with hrest, seven at 2 with hrest and
the letter mk (`mkG9`: what comes there); hrest: "in order" of that filling reads the public part
alone (RestAt9.lean). At 2 the premise hmore is not asked
(in TieGAt9.lean); hmk is the kernel's. The premises that name
the two rounds' plain data d₁ d₂ (hNew, hshown) bear the data's own equation as a third
antecedent: they are asked at the row's own two rounds alone (the first form's exchanges' third
form). As they were bound (two tags on d₁, none on d₂) we had marked them "in doubt". What is not
claimed. The premises that stay. Nothing on soundness.
-/
import Johnson.Desc.AtSeats.TieWAt9
import Johnson.Desc.AtSeats.TieGAt9
import Johnson.Desc.AtSeats.DoorAt9WG
import Johnson.Desc.AtSeats.RestAt9

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
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (wSitsItem wSitsB planSitsB planSeatB plus13 cA13 FactsK13
  FillsK13C PlanM3 PlanM4 SmpOld DecBlind openAt plusG cAG FactsG MgGC PlanG PlanGSeats madeSix
  StepG plus13_moreW plusG_more rowW_9 qW_9 inW_9 doorsW_9 mkG9 rowG_9 mk_9 mG_9 qG_9 doorsG_9)

/-- **The tie at W's commitment, at the composed filling over its closed base.** -/
theorem w_tiedR_at9
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
    {X₁ X₂ Xi Xj Tok : Type} {rows cols nD : ℕ} {XV : OnBytes.Model.Verify.Public}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all (ProofFile.fileDescBy OnBytes.secondHashFunction
      ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ (Wit (CellsQ rows cols) Tok
                  MsgT)}
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (N : Numbers)
    (𝔇 : MgData Xj ProofFile.InstPub Tok rows cols nD XV)
    (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option (CellsQ rows cols))
    (c₀ : (CellsQ rows cols))
    (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl}
    {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃)
      all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) (Wit (CellsQ rows cols) Tok MsgT) ds}
    {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ d₁ d₂ : RDT, (rest₁ 356 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (msg : Array OracleNotice)
    (hm : linMessageW Z.first.lin = some msg)
    (rad : ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf (parWZ Z
            msg).codes s.l).om i).Smp)
    (hCond : condPort (parWZ Z msg) rad = true)
    (h1 : (parWZ Z msg).seeds = 1)
    (hpow : powB (parWZ Z msg) rad 128 = true)
    {nR : ℕ}
    (sh : Params.ReqShape)
    (ly : Params.ReqLayout)
    (rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE nR (whereOf
            Z).lin.kCol)
    (d : K12Data)
    (mat : (CellsQ rows cols) → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (y₀ : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str)
    (hNt : N.treesAt psF[356 + 1]? = N.treesAt psF[356]? + (layOf (parWZ Z msg)).shapes.size)
    (hNm : N.msgsAt psF[356 + 1]? = N.msgsAt psF[356]? + (parWZ Z msg).sent.size)
    (hFlC : FillsK13C (whereOf Z) N (mgAll 𝔇 mgBase) (parWZ Z msg).codes arr mat G smp ms decT)
    (hft : d.ft = 0)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B)
    (hPl3 : PlanM3 d.L d.M ms (parWZ Z msg).codes N)
    (h4 : PlanM4 0 d.L d.M N psF[356]? (parWZ Z msg))
    (hplan : (atM4 (Cl := Cl) (whereOf Z) (sendAtS (parWZ Z msg))).planOk = true)
    (hsmp : SmpOld N psF[356]? ms smp)
    (hdec : DecBlind decT)
    (hPl : wSitsItem ∈ (First.pubSets (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).more
      Sound.linksFull psF)[356 + 1]?.getD [] → planSitsB (whereOf Z) (parWZ Z msg) = true ∧
      planSeatB N psF[356]? (parWZ Z msg) = true)
    (hbase : N.index.1 < nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
    (hNew : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds → ((dataOf aN R₁ R₂
        R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] → ∃ (fOf :
      (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → ∀ j,
      (portOmZ (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val)).Str) (fIn :
      (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → (wT d₁).Msg
      → ∀ j, (portOmZ (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val)).Str), ∀ c' :
      Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msg))) → (∀ y τ, fOf ((sendPiece
      (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf
      aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂
      (parWZ Z msg).coordinates (errPort (parWZ Z msg) rad)).ior.imp y τ) = fIn y τ.1) ∧ ∀ (z :
      ProofFile.InstPub) a τ x, onQ N (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)) Sound.linksFull
      psF (fun s : S => (z, s)) 356 a → a.1.failed = none → (sendPiece (W := Wit (CellsQ rows
      cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁
      T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z
      msg).coordinates (errPort (parWZ Z msg) rad)).ior.red.out a τ = some x → (∀ j, sampledAt
      (parWZ Z msg) j → Sealed (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val) (fOf x.2
      j) x.1.st (x.1.st.oracles.size - (shapesOf (parWZ Z msg)).length + j.val)) → (wSitsItem ∈
      (First.pubSets (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).more Sound.linksFull
      psF)[356 + 1]?.getD [] → wSitsB (parWZ Z msg).codes (whereOf Z) x.1 = true ∧
      x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z msg)).length]? = some N.w) → (plus13
      (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).held N.w.1 N.w.2 (z, x.1) = true ∧ (plus13 (dW Z
      msg sh ly N rwD) d (mgAll 𝔇 mgBase)).noColl N.w.1 N.w.2 (z, x.1) (strsOf (Sound.frameAt
      (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    (hshown : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds → ((dataOf aN R₁
        R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] → ∀ c' : Block
      S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msg))) → ∀ (z : ProofFile.InstPub) a τ x, onQ
      N (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)) Sound.linksFull psF (fun s : S => (z,
      s)) 356 a → a.1.failed = none → (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F :=
      (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees
      ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates (errPort
      (parWZ Z msg) rad)).ior.red.out a τ = some x → (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇
      mgBase)).shown N.w.1 N.w.2 (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
      R₃).key₁ T.ft₁) x.2))
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
            R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13 (dW Z msg sh ly N rwD) d (mgAll 𝔇
      mgBase) a.1)
    (hHand : ∀ q, (T.p₁ :: T.l₁)[356]? = some q → HandsOn Rch 356 (q.withMap ((fun k => extQAt
      (parWZ Z msg).codes G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf
      Sound.linksFull true) (fun a => a) k) 356))) :
    ∀ q, (T.p₁ :: T.l₁)[356]? = some q → TiedAtR N (mgAll 𝔇 mgBase) Sound.linksFull (flatPlacesOf
      Sound.linksFull true) (fun a => a) Rch 356 (q.withMap ((fun k => extQAt (parWZ Z msg).codes
      G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a =>
      a) k) 356)) :=
  w_tiedR_at hS hR O hT N (mgAll 𝔇 mgBase) G arr ms decT c₀ tokOf hC hWr hCap msg hm rad smp hCond
    h1 hpow sh ly rwD d mat y₀
    (by rw [plus13_moreW, mgAll_more_base]; exact rowW_9)
    hNt hNm hFlC hft hfB hPl3 h4 hplan
    (by rw [plus13_moreW, mgAll_more_base]; exact qW_9)
    (by rw [plus13_moreW, mgAll_more_base]; exact inW_9)
    hsmp hdec (HashBuild.rest9_M4 𝔇) hPl hbase hNew hshown Rch
    (by rw [plus13_moreW, mgAll_more_base]; exact doorsW_9.1)
    (by rw [plus13_moreW, mgAll_more_base]; exact doorsW_9.2)
    hFacts hHand

/-- **The tie at the first segment's opening, at the composed filling over its closed base.** -/
theorem first_tiedR_at9
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
    {X₁ X₂ Xi Xj Tok : Type}
    {rows cols nD : ℕ}
    {XV : OnBytes.Model.Verify.Public}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all (ProofFile.fileDescBy OnBytes.secondHashFunction
      ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ (Wit (CellsQ rows cols) Tok
                  MsgT)}
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (N : Numbers)
    (𝔇 : MgData Xj ProofFile.InstPub Tok rows cols nD XV)
    (cs : Codes)
    (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs
            s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option (CellsQ rows cols))
    (c₀ : (CellsQ rows cols))
    (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl}
    {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃)
      all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) (Wit (CellsQ rows cols) Tok MsgT) ds}
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
    (rad : ℕ → ℕ)
    (hCond : condPort (firstPar Bs.G₀.first (gpOf Z)) rad = true)
    (h1 : (firstPar Bs.G₀.first (gpOf Z)).seeds = 1)
    (hpow : powB (firstPar Bs.G₀.first (gpOf Z)) rad 128 = true)
    {nR : ℕ}
    (sh : Params.ReqShape)
    (ly : Params.ReqLayout)
    (rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE nR (whereOf
            Z).lin.kCol)
    (d : K12Data)
    (dk : K3Data)
    (nsOf : ℕ → Option ℕ)
    (dg : Bool)
    (mat : (CellsQ rows cols) → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (hNt : N.treesAt psF[2 + 1]? = N.treesAt psF[2]? + (layOf (firstPar Bs.G₀.first (gpOf
      Z))).shapes.size)
    (hNm : N.msgsAt psF[2 + 1]? = N.msgsAt psF[2]? + (firstPar Bs.G₀.first (gpOf Z)).sent.size)
    (hFlC : FillsK13C (whereOf Z) N (mgAll 𝔇 mgBase) cs arr mat G smp ms decT)
    (hft : d.ft = 0)
    (hGC : MgGC N (mgAll 𝔇 mgBase) nsOf dk dg)
    (hUn : ∀ x, (mgAll 𝔇 mgBase).pub .unheard x = First.unheardB x.2)
    (hUP : ∀ x, (mgAll 𝔇 mgBase).pubP .unheard x)
    (hPlG : PlanG X nsOf dk dg sh ly)
    (hplan : ∀ nm : String, (openingZero Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl).planOk =
      true)
    (hSeats : PlanGSeats d.L d.M N psF[2]? (firstPar Bs.G₀.first (gpOf Z)))
    (hft1 : (firstPar Bs.G₀.first (gpOf Z)).gp.firstTree = 0)
    (hdec : DecBlind decT)
    (hconstr : ∀ (nm : String) x x' y y' w m c', StepG Cl Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol x x' → (∀ q' ∈
      ((First.pubSets (plusG (dG Z cs sh ly N rwD) d dk (mgAll 𝔇 mgBase)).more Sound.linksFull
      psF)[2]?.getD []), (plusG (dG Z cs sh ly N rwD) d dk (mgAll 𝔇 mgBase)).pub q' x = true) →
      First.bookAt N psF[2]? x.2 = true → y'.cell = y.cell → (plusG (dG Z cs sh ly N rwD) d dk
      (mgAll 𝔇 mgBase)).constr m c' x' y' w → (plusG (dG Z cs sh ly N rwD) d dk (mgAll 𝔇
      mgBase)).constr m c' x y w)
    (built : Array Stages.LinkH)
    (hSent : ∀ x, (mgAll 𝔇 mgBase).pub HashBuild.sentItem0 x = First.FillSent.sentIsB
      (First.FillSent.sentDataAt sh N Sound.linksFull psF built) 0 x.2)
    (hTrees : ∀ x, (mgAll 𝔇 mgBase).pub HashBuild.treesItem0 x = First.FillSent.treesAreB
      (First.FillSent.sentDataAt sh N Sound.linksFull psF built) 0 x.2)
    (hSP : ∀ x, (mgAll 𝔇 mgBase).pubP HashBuild.sentItem0 x)
    (hTP : ∀ x, (mgAll 𝔇 mgBase).pubP HashBuild.treesItem0 x)
    (hb0 : First.FillSent.baseAt N Sound.linksFull psF 0 = 0)
    (Y : Stages.LinkH)
    (hY : built[0]? = some Y)
    (hYF : Y.Fp = X.X.Fp)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B)
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
      Z.first.lin.kCol) → (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F :=
      (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees
      ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂ (firstPar Bs.G₀.first (gpOf
      Z)).coordinates (errPort (firstPar Bs.G₀.first (gpOf Z)) rad)).ior.imp y τ) = fIn y τ.1) ∧ ∀
      (z : ProofFile.InstPub) a τ x, onQ N (plusG (dG Z cs sh ly N rwD) d dk (mgAll 𝔇 mgBase))
      Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none → (sendPiece (W := Wit
      (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
      R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂ (firstPar
      Bs.G₀.first (gpOf Z)).coordinates (errPort (firstPar Bs.G₀.first (gpOf Z)) rad)).ior.red.out
      a τ = some x → (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j → Sealed (firstPar
      Bs.G₀.first (gpOf Z)).codes (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) (rad j.val) (fOf x.2
      j) x.1.st (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val))
      → ∀ t ∈ First.sampledIn N (openAt Sound.linksFull psF (2 + 1)), (plusG (dG Z cs sh ly N rwD)
      d dk (mgAll 𝔇 mgBase)).held t.1 t.2 (z, x.1) = true ∧ (plusG (dG Z cs sh ly N rwD) d dk
      (mgAll 𝔇 mgBase)).shown t.1 t.2 (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN
      R₁ R₂ R₃).key₁ T.ft₁) x.2) ∧ (plusG (dG Z cs sh ly N rwD) d dk (mgAll 𝔇 mgBase)).noColl t.1
      t.2 (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁
      T.ft₁) x.2))
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
            R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ j a, Rch j a → j = 2 ∨ j = 2 + 1 → a.1.2.failed = none → FactsG (dG Z cs sh ly N
      rwD) d dk (mgAll 𝔇 mgBase) a.1)
    (hHand : ∀ q, (T.p₁ :: T.l₁)[2]? = some q → HandsOn Rch 2 (q.withMap ((fun k => extQAt cs G
      arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a)
      k) 2))) :
    ∀ q, (T.p₁ :: T.l₁)[2]? = some q → TiedAtR N (mgAll 𝔇 mgBase) Sound.linksFull (flatPlacesOf
      Sound.linksFull true) (fun a => a) Rch 2 (q.withMap ((fun k => extQAt cs G arr smp ms decT
      c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) k) 2)) :=
  first_tiedR_at hS hR O hT N (mgAll 𝔇 mgBase) cs G arr smp ms decT c₀ tokOf hC hWr hU hCap X hX
    mkG9 rad hCond h1 hpow sh ly rwD d dk nsOf dg mat
    (by rw [plusG_more, plus13_moreW, mgAll_more_base]; exact rowG_9)
    hNt hNm hFlC hft hGC hUn hUP hPlG
    (by rw [plusG_more, plus13_moreW, mgAll_more_base]; exact mG_9)
    hplan hSeats hft1 hdec (fun _ => HashBuild.rest9_G 𝔇) hconstr built mk_9 hSent hTrees hSP hTP
    hb0 Y hY hYF hfB
    (by rw [plusG_more, plus13_moreW, mgAll_more_base]; exact qG_9)
    hownB hNew Rch
    (by rw [plusG_more, plus13_moreW, mgAll_more_base]; exact doorsG_9.1)
    (by rw [plusG_more, plus13_moreW, mgAll_more_base]; exact doorsG_9.2)
    hFacts hHand

end VerifiableInference.Desc.K1
