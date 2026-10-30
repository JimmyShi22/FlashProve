-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TieGAtBase.lean: THE TIE AT THE FIRST SEGMENT's OPENING
(number 2) IN THE SECOND FORM AT `mgAll 𝔇 mgBase`, WITH ITS LETTERS AT THE COMPOSED FILLING's OWN
TERMS: N := 𝔇.N; the shape and the layout 𝔇's; the look-ups' data `𝔇.pubD.d3`; the numbers of
slots `𝔇.pubD.nsOf`; the built segments 𝔇's. One statement, made by program out of
`first_tiedR_at9`: a call. WHAT FALLS AGAINST THAT FORM: the seven
premises on the filling's letters; hconstr, which was bound at every
segment and constraint: it follows from three plain sentences on three of 𝔇's letters:
hreq, hdig, hhead. WHAT COMES: these three; hlinks (𝔇's list of
segments is the written one); hdg (one test on the public parameters). The premises
that name the two rounds' plain data d₁ d₂ (hNew, hshown) bear the data's own equation as a third
antecedent: they are asked at the row's own two rounds alone (the first form's exchanges' third
form). As they were bound (two tags on d₁, none on d₂) we had marked them "in doubt". What is not
claimed. The premises that stay. Nothing on soundness.
-/
import Johnson.Desc.AtSeats.TiesAt9
import Johnson.Desc.AtSeats.MgGCAtBase
import Johnson.Desc.AtSeats.ConstrBackAt9

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open)
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (FillsK13C DecBlind openAt plusG FactsG PlanG PlanGSeats StepG
  plus13_moreW plusG_more plusG_hand mkG9 qAt9)

set_option maxRecDepth 1000000 in
/-- "No reply has been heard" is open in front of number 2 at the wider door. -/
theorem unheardG_9 : Pub.unheard ∈ qAt9 2 := by
  decide +kernel

/-- **The tie at the first segment's opening, with its letters at the composed filling's own
terms.** -/
theorem first_tiedR_atBase
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
    (𝔇 : MgData Xj ProofFile.InstPub Tok rows cols nD XV)
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (cs : Codes)
    (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs
            s.l).om i).Smp)
    (ms : List Mem)
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
    (rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE nR (whereOf
            Z).lin.kCol)
    (d : K12Data)
    (dg : Bool)
    (mat : (CellsQ rows cols) → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (hNt : 𝔇.N.treesAt psF[2 + 1]? = 𝔇.N.treesAt psF[2]? + (layOf (firstPar Bs.G₀.first (gpOf
      Z))).shapes.size)
    (hNm : 𝔇.N.msgsAt psF[2 + 1]? = 𝔇.N.msgsAt psF[2]? + (firstPar Bs.G₀.first (gpOf
      Z)).sent.size)
    (hFlC : FillsK13C (whereOf Z) 𝔇.N (mgAll 𝔇 mgBase) cs arr mat G smp ms 𝔇.decT)
    (hft : d.ft = 0)
    (hPlG : PlanG X 𝔇.pubD.nsOf 𝔇.pubD.d3 dg 𝔇.shape 𝔇.layout)
    (hplan : ∀ nm : String, (openingZero Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl).planOk =
      true)
    (hSeats : PlanGSeats d.L d.M 𝔇.N psF[2]? (firstPar Bs.G₀.first (gpOf Z)))
    (hft1 : (firstPar Bs.G₀.first (gpOf Z)).gp.firstTree = 0)
    (hdec : DecBlind 𝔇.decT)
    (hlinks : 𝔇.links = Sound.linksFull)
    (hdg : First.Look.k3SortAt 𝔇.pubD.d3.X 0 2 = some dg)
    (hreq : ∀ x x' : ProofFile.InstPub × S, x'.1 = x.1 → 𝔇.H.req x' = 𝔇.H.req x)
    (hdig : ∀ (x x' : ProofFile.InstPub × S) (y y' : Strs) w k, x'.1 = x.1 → y'.cell = y.cell →
      𝔇.digitsPart k x' y' w → 𝔇.digitsPart k x y w)
    (hhead : ∀ (nm : String) (x x' : ProofFile.InstPub × S) (y y' : Strs) w p i, StepG Cl Bs.G₀.first
      (gpOf Z) nm X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol x x' →
      (mgAll 𝔇 mgBase).pub .unheard x = true → y'.cell = y.cell → 𝔇.headPart p i x' y' w →
      𝔇.headPart p i x y w)
    (hb0 : First.FillSent.baseAt 𝔇.N Sound.linksFull psF 0 = 0)
    (Y : Stages.LinkH)
    (hY : 𝔇.built[0]? = some Y)
    (hYF : Y.Fp = X.X.Fp)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B)
    (hownB : ownSeatsB 𝔇.N (openAt Sound.linksFull psF (2 + 1)) (firstPar Bs.G₀.first (gpOf Z))
      (((𝔇.shape.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
      (𝔇.N.treesAt psF[2]?) = true)
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
      (z : ProofFile.InstPub) a τ x, onQ 𝔇.N (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3
            (mgAll 𝔇 mgBase)) Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃)
      all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c
      2))) d₁ d₂ (firstPar Bs.G₀.first (gpOf Z)).coordinates (errPort (firstPar Bs.G₀.first (gpOf
      Z)) rad)).ior.red.out a τ = some x → (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j →
      Sealed (firstPar Bs.G₀.first (gpOf Z)).codes (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j)
      (rad j.val) (fOf x.2 j) x.1.st (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf
      Z))).length + j.val)) → ∀ t ∈ First.sampledIn 𝔇.N (openAt Sound.linksFull psF (2 + 1)),
      (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇 mgBase)).held t.1 t.2 (z,
      x.1) = true ∧ (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇 mgBase)).shown
      t.1 t.2 (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)
      x.2) ∧ (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇 mgBase)).noColl t.1
      t.2 (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁
      T.ft₁) x.2))
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
            R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ j a, Rch j a → j = 2 ∨ j = 2 + 1 → a.1.2.failed = none → FactsG (dG Z cs 𝔇.shape
      𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇 mgBase) a.1)
    (hHand : ∀ q, (T.p₁ :: T.l₁)[2]? = some q → HandsOn Rch 2 (q.withMap ((fun k => extQAt cs G
      arr smp ms 𝔇.decT c₀ tokOf 𝔇.N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a =>
      a) k) 2))) :
    ∀ q, (T.p₁ :: T.l₁)[2]? = some q → TiedAtR 𝔇.N (mgAll 𝔇 mgBase) Sound.linksFull (flatPlacesOf
      Sound.linksFull true) (fun a => a) Rch 2 (q.withMap ((fun k => extQAt cs G arr smp ms 𝔇.decT
      c₀ tokOf 𝔇.N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) k) 2)) := by
  have hS0 := HashBuild.sent_base 𝔇
  have hT0 := HashBuild.trees_base 𝔇
  rw [hlinks] at hS0 hT0
  have hU9 : Pub.unheard ∈
      (First.pubSets (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇 mgBase)).more
        Sound.linksFull psF)[2]?.getD [] := by
    rw [plusG_more, plus13_moreW, mgAll_more_base]
    exact unheardG_9
  have hUnQ : ∀ x : ProofFile.InstPub × S,
      (∀ q' ∈ ((First.pubSets (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇
          mgBase)).more
        Sound.linksFull psF)[2]?.getD []),
        (plusG (dG Z cs 𝔇.shape 𝔇.layout 𝔇.N rwD) d 𝔇.pubD.d3 (mgAll 𝔇 mgBase)).pub q' x = true) →
      (mgAll 𝔇 mgBase).pub .unheard x = true := fun x hQ =>
    (plusG_hand _ d 𝔇.pubD.d3 (mgAll 𝔇 mgBase) _ rfl x).symm.trans (hQ _ hU9)
  exact first_tiedR_at9 hS hR O hT 𝔇.N 𝔇 cs G arr smp ms 𝔇.decT c₀ tokOf hC hWr hU hCap X hX rad
    hCond h1 hpow 𝔇.shape 𝔇.layout rwD d 𝔇.pubD.d3 𝔇.pubD.nsOf dg mat hNt hNm hFlC hft
    (HashBuild.mgGC_base 𝔇 dg hdg) (HashBuild.unheard_base 𝔇) (HashBuild.unheardP_base 𝔇) hPlG
    hplan hSeats hft1 hdec (fun nm x x' y y' w m c' hst hQ _ hc h => HashBuild.constr_back_at9 𝔇
    mgBase hdec hst.1 hc (hreq x x' hst.1) (fun k => hdig x x' y y' w k hst.1 hc) (fun p i =>
    hhead nm x x' y y' w p i hst (hUnQ x hQ) hc) m c' h) 𝔇.built hS0
    hT0 (HashBuild.sentP_base 𝔇) (HashBuild.treesP_base 𝔇) hb0 Y hY
    hYF hfB hownB hNew Rch hFacts hHand

end VerifiableInference.Desc.K1
