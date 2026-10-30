-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K01KindAtBase.lean: KIND K1's SHARE OF THE FIRST TABLE's
TIES, ALL 52 PLACES, IN THE SECOND FORM (`TiedAtR`), AT THE COMPOSED FILLING OVER ITS CLOSED BASE
`mgAll Dm mgBase`. Two statements, MADE BY PROGRAM out of three
theorems' own binders (shared names once; the two ties' own under W_ and G_): each a call.
  `w_tiedR_at9c`: `w_tiedR_at9` (TiesAt9.lean) with the codes a letter cs under hcs: the
  sending's own codes are cs. `k01_kind_atBase`: by `k01_law_frameR` (K01FrameR.lean): the
  fifty later sendings: `k01_fifty_atBase` (K01FiftyAtBase.lean); the first segment's
  opening (2): `first_tiedR_atBase` (Johnson/Desc/AtSeats/TieGAtBase.lean); W's commitment (356):
  `w_tiedR_at9c`: ALL AT ONE T, ONE Rch, ONE EXTRACTOR, ONE Dm. SHARED: the scope; the four on T;
  the hand-on hHand; "the decoder reads the public part alone" (hBlind); Dm's list of segments
  (hDlk); the book's test is its sentence (`bookFitsB_iff`, Johnson/Desc/Sound/BookTestsLaw.lean).
What W's sending newly holds and shows at the tie at 356 is no premise:
they are calls (`hNewW_weak`, NewAtW9.lean; `hshownW_of`,
Johnson/Desc/K1/Law/NewAtTwo.lean). THE PREMISES: FOUR ON THE PUBLIC VALUES AND THE DATA: W_HP (PlanAt at the
data's own two rounds), W_hbaseT, W_hsam (a message at whose seat a member sits has an OOD
sample), W_hpl. The like at number 2: what is newly held is a call (`hNew0_weak`,
NewAtG9.lean), at the radii `radRec 0` of the opening's own parameters (no letter for the radii);
the premises there are G_HP, G_hbaseT, G_hsam, G_hpl. What is not claimed. The premises. Nothing
on soundness.
-/
import Johnson.Desc.K1.Law.K01FiftyAtBase
import Johnson.Desc.K1.Law.K01FrameR
import Johnson.Desc.AtSeats.TieGAtBase
import Johnson.Desc.AtSeats.NewAtW9
import Johnson.Desc.AtSeats.NewAtG9

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

/-- **The tie at W's commitment, with the codes a letter**: so that it can be called at the composed
filling's own codes. -/
theorem w_tiedR_at9c
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
    (cs : Codes)
    (hcs : (parWZ Z msg).codes = cs)
    (rad : ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs
            s.l).om i).Smp)
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
    (hFlC : FillsK13C (whereOf Z) N (mgAll 𝔇 mgBase) cs arr mat G smp ms decT)
    (hft : d.ft = 0)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B)
    (hPl3 : PlanM3 d.L d.M ms cs N)
    (h4 : PlanM4 0 d.L d.M N psF[356]? (parWZ Z msg))
    (hplan : (atM4 (Cl := Cl) (whereOf Z) (sendAtS (parWZ Z msg))).planOk = true)
    (hsmp : SmpOld N psF[356]? ms smp)
    (hdec : DecBlind decT)
    (hPl : wSitsItem ∈ (First.pubSets (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).more
      Sound.linksFull psF)[356 + 1]?.getD [] → planSitsB (whereOf Z) (parWZ Z msg) = true ∧
      planSeatB N psF[356]? (parWZ Z msg) = true)
    (hbase : N.index.1 < nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
    (hNew : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds → ((dataOf aN R₁
      R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] → ∃ (fOf : (Sound.frameAt (dataOf aN R₁
      R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → ∀ j, (portOmZ (parWZ Z msg).codes
      (shapeAt (parWZ Z msg) j) (rad j.val)).Str) (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all
      (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → (wT d₁).Msg → ∀ j, (portOmZ (parWZ Z msg).codes
      (shapeAt (parWZ Z msg) j) (rad j.val)).Str), ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z)
      (sendAtS (parWZ Z msg))) → (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F
      := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees
      ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates (errPort
      (parWZ Z msg) rad)).ior.imp y τ) = fIn y τ.1) ∧ ∀ (z : ProofFile.InstPub) a τ x, onQ N (plus13 (dW
            Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)) Sound.linksFull psF (fun s : S => (z, s)) 356 a →
      a.1.failed = none → (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt
      (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂
      R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates (errPort (parWZ Z msg)
      rad)).ior.red.out a τ = some x → (∀ j, sampledAt (parWZ Z msg) j → Sealed (parWZ Z
      msg).codes (shapeAt (parWZ Z msg) j) (rad j.val) (fOf x.2 j) x.1.st (x.1.st.oracles.size -
      (shapesOf (parWZ Z msg)).length + j.val)) → (wSitsItem ∈ (First.pubSets (plus13 (dW Z msg sh
      ly N rwD) d (mgAll 𝔇 mgBase)).more Sound.linksFull psF)[356 + 1]?.getD [] → wSitsB (parWZ Z
      msg).codes (whereOf Z) x.1 = true ∧ x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z
      msg)).length]? = some N.w) → (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).held N.w.1
      N.w.2 (z, x.1) = true ∧ (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).noColl N.w.1
      N.w.2 (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁
      T.ft₁) x.2))
    (hshown : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds → ((dataOf aN
      R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] → ∀ c' : Block S Cl, c'.UnderR (atM4
      (whereOf Z) (sendAtS (parWZ Z msg))) → ∀ (z : ProofFile.InstPub) a τ x, onQ N (plus13 (dW Z msg sh
            ly N rwD) d (mgAll 𝔇 mgBase)) Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed =
      none → (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁
      R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take
      (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates (errPort (parWZ Z msg) rad)).ior.red.out a
      τ = some x → (plus13 (dW Z msg sh ly N rwD) d (mgAll 𝔇 mgBase)).shown N.w.1 N.w.2 (strsOf
      (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
            R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13 (dW Z msg sh ly N rwD) d (mgAll 𝔇
      mgBase) a.1)
    (hHand : ∀ q, (T.p₁ :: T.l₁)[356]? = some q → HandsOn Rch 356 (q.withMap ((fun k => extQAt cs
      G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a =>
      a) k) 356))) :
    ∀ q, (T.p₁ :: T.l₁)[356]? = some q → TiedAtR N (mgAll 𝔇 mgBase) Sound.linksFull (flatPlacesOf
      Sound.linksFull true) (fun a => a) Rch 356 (q.withMap ((fun k => extQAt cs G arr smp ms decT
      c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) k) 356)) := by
  subst hcs
  exact w_tiedR_at9 hS hR O hT N 𝔇 G arr ms decT c₀ tokOf hC hWr hCap msg hm rad smp hCond h1 hpow
    sh ly rwD d mat y₀ hNt hNm hFlC hft hfB hPl3 h4 hplan hsmp hdec hPl hbase hNew hshown Rch
    hFacts hHand

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- **KIND K1's SHARE, ALL 52 PLACES, IN THE SECOND FORM, AT THE COMPOSED FILLING OVER ITS
CLOSED BASE.** -/
theorem k01_kind_atBase
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
    {X₁ X₂ : Type}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV)
    (dk : K12Data)
    (xb : S → Bool)
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all (ProofFile.fileDescBy OnBytes.secondHashFunction
      ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ (Wit (CellsQ rows cols) Tok
                  MsgT)}
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (seats : List (ℕ × ℕ))
    (c₀ : CellsQ rows cols)
    (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl}
    {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃)
      all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) (Wit (CellsQ rows cols) Tok MsgT) ds}
    {r : Fmt.RoundView}
    (hc : Bs.G₀.first.codes = codesFull2)
    (hs : Bs.G₀.first.shape = shapeFull)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, (rest₁ (noL l d) [d₁, d₂]).err = Err.cap 128
      (uLT (ckP .two) [d₁, d₂]))
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hRows : First.eachOnce ((List.range 26).map fun m => (Dm.N.groupAt m, 0)) = true)
    (hBook : First.bookFit Dm.N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true)
    (hFence : First.fenceFit Dm.N linksFull (flatPlacesOf linksFull true) = true)
    (hSent : ∀ l, l < 25 → ∀ d : Bool, sentAtB Dm.N (toldBy c.blocksInOrder) (noL l d) l (momL d) = true)
    (hBlind : K13.Law.DecBlind Dm.decT)
    (hNd : seats.Nodup)
    (hSeats : ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? = some (seatOfMsg (parL
      Z Bs.G₀ l d) (baseL aN R₁ R₂ R₃ c l d) j.val))
    (hRd : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf
      (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb)
      linksFull (flatPlacesOf linksFull true) (noL l d) x y → (Pub.formsIn m j r ∈ (First.pubSets
      (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb).more linksFull (flatPlacesOf linksFull
      true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true)
      (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)
      xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems
      (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) → ReadersStay (dK Dm.pubD
      Dm.sent) m j r x.2 x'.2)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z
      Bs.G₀ l d X arrs) x x' → Dm.H.req x' = Dm.H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb)
      linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d)
      y y' → Item.constr (headLink XV) p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l
      d) → Dm.headPart p i x' y' w → Dm.headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf
      (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb)
      linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d)
      y y' → Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d)
      → Dm.digitsPart m x' y' w → Dm.digitsPart m x y w)
    (Wp : OnBytes.Model.Verify.Public)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w, (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2
            cc mm) → Dm.wt 24 a' y' w → Dm.wt 24 a y w)
    (hheard : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf
      linksFull true) (noL 24 true) x y → ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H)
    (hAtA : ∀ l, l < 25 → aheadAtB Dm.shape (Dm.N.sent l) (parL Z Bs.G₀ l true) l (Dm.pubD.dS1.own
      l).size (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true)
    (hPlanR : ∀ l, l < 25 → ∀ d : Bool, PlanRest Dm.pubD.cs Dm.G Dm.ms (parL Z Bs.G₀ l d) (radRec
      (recL l d) (parL Z Bs.G₀ l d)) (baseL aN R₁ R₂ R₃ c l d) (Dm.N.sent l (momL d)))
    (hTold : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) →
      d₁.kind = .seeds → ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, Dm.G.oracleAt (baseL aN R₁ R₂ R₃ c l d + n) =
      some o → o.logLength = sh.a ∧ o.words = sh.W)
    (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) dep
      0 b₁ l₁ (dataOf aN R₁ R₂ R₃).ds₁ [r])
    (hDsh : Dm.shape = shapeFull)
    (hDlk : Dm.links = linksFull)
    (hP1 : ∀ l, l < 25 → laterSeatsB Dm.N (parL Z Bs.G₀ l false) l 1 (Dm.N.treesAt (flatPlacesOf
      linksFull true)[14 * l + k1Ix l false + 2]?) = true)
    (hArm : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' (w
            : Wit (CellsQ rows cols) Tok MsgT), YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N
      (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL l
      false) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mw1 Dm.N (d13 Dm) dk (mgAll Dm
      mgBase) xb).tie l x' y' w → ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf
      linksFull true) (noL l false)).ins → ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A →
      K9.segAt? x'.2 = some B → ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
      (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l))
    (hwtR : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)
      xb) linksFull (flatPlacesOf linksFull true) (noL l false) x y → KeptBelow (baseL aN R₁ R₂ R₃
      c l false) y y' → Dm.wt l x' y' w → Dm.wt l x y w)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂
            R₃).key₁ T.ft₁).E.Str → Prop)
    (hxb : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' : ProofFile.InstPub ×
      S, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → xb x.2 = true → xb x'.2 = true)
    (hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d +
      2 + 1) → ∀ a, Rch j a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true)
      (fun a => a) j a → a.1.2.failed = none → FactsK13 (d13 Dm) dk (mgAll Dm mgBase) a.1 ∧ (∀ L,
      a.1.2.link? = some L → L.check.frame.group = Dm.N.groupAt l ∧ L.check.frame.shape = (d13
      Dm).shape) ∧ xb a.1.2 = true)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt
      Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull
      true) (fun a => a) k) i)))
    (hsmp : Dm.smp = smpNamed Dm.cs seats)
    (hidx : ∀ l, l < 25 → ∀ d : Bool, ∀ u ∈ First.sampledIn Dm.N (openAt linksFull (flatPlacesOf
      linksFull true) (noL l d)), seats.idxOf u < Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l
      d]?)
    (hft : dk.ft = (gpOf Z).firstTree)
    (hPlan3 : planThreeB dk Dm.N Z Bs.G₀ = true)
    (hSortB : sortB XV = true)
    (W_hCap : ∀ d₁ d₂ : RDT, (rest₁ 356 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (W_msg : Array OracleNotice)
    (W_hm : linMessageW Z.first.lin = some W_msg)
    (W_hcs : (parWZ Z W_msg).codes = Dm.pubD.cs)
    (W_rad : ℕ → ℕ)
    (W_hCond : condPort (parWZ Z W_msg) W_rad = true)
    (W_h1 : (parWZ Z W_msg).seeds = 1)
    (W_hpow : powB (parWZ Z W_msg) W_rad 128 = true)
    {W_nWr : ℕ}
    (W_rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE W_nWr (whereOf
            Z).lin.kCol)
    (W_mat : (CellsQ rows cols) → Fin W_nWr → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (W_y₀ : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str)
    (W_hNt : Dm.N.treesAt psF[356 + 1]? = Dm.N.treesAt psF[356]? + (layOf (parWZ Z
      W_msg)).shapes.size)
    (W_hNm : Dm.N.msgsAt psF[356 + 1]? = Dm.N.msgsAt psF[356]? + (parWZ Z W_msg).sent.size)
    (W_hFlC : FillsK13C (whereOf Z) Dm.N (mgAll Dm mgBase) Dm.pubD.cs Dm.arr W_mat Dm.G Dm.smp
      Dm.ms Dm.decT)
    (W_hft : dk.ft = 0)
    (W_hPl3 : PlanM3 dk.L dk.M Dm.ms Dm.pubD.cs Dm.N)
    (W_h4 : PlanM4 0 dk.L dk.M Dm.N psF[356]? (parWZ Z W_msg))
    (W_hplan : (atM4 (Cl := Cl) (whereOf Z) (sendAtS (parWZ Z W_msg))).planOk = true)
    (W_hsmp : SmpOld Dm.N psF[356]? Dm.ms Dm.smp)
    (W_hPl : wSitsItem ∈ (First.pubSets (plus13 (dW Z W_msg Dm.shape Dm.layout Dm.N W_rwD) dk
      (mgAll Dm mgBase)).more Sound.linksFull psF)[356 + 1]?.getD [] → planSitsB (whereOf Z)
      (parWZ Z W_msg) = true ∧ planSeatB Dm.N psF[356]? (parWZ Z W_msg) = true)
    (W_hbase : Dm.N.index.1 < nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
    (W_HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z W_msg) → d₁.kind = .seeds → ((dataOf aN
      R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] → PlanAt (Sound.frameAt (dataOf aN R₁
      R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) Dm.pubD.cs Dm.G Dm.ms (parWZ Z W_msg) W_rad
      (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ [Dm.N.w])
    (W_hbaseT : Dm.N.treesAt psF[356]? = (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))))
    (W_hsam : ∀ j : Fin (shapesOf (parWZ Z W_msg)).length, ∀ m' ∈ Dm.ms, SitsAt m' (seatOfMsg
      (parWZ Z W_msg) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).1 (seatOfMsg
      (parWZ Z W_msg) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).2 →
      sampledAt (parWZ Z W_msg) j)
    (W_hpl : ∀ j : Fin (shapesOf (parWZ Z W_msg)).length, seats[Dm.N.msgsAt psF[356]? + j.val]? =
      some (seatOfMsg (parWZ Z W_msg) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
      j.val))
    (W_hFacts : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13 (dW Z W_msg Dm.shape Dm.layout
      Dm.N W_rwD) dk (mgAll Dm mgBase) a.1)
    (G_hU : ∃ (e : Block S Cl) (nm : String) (G_X : LayPar), c.blocksInOrder[2]? = some e ∧
      Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some G_X ∧ e.UnderR (openingZero
      Bs.G₀.first (gpOf Z) nm G_X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links)
      Z.first.lin.kCol : Block S Cl))
    (G_hCap : ∀ d₁ d₂ : RDT, (rest₁ 2 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (G_X : LayPar)
    (G_hX : Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some G_X)
    (G_hCond : condPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
      = true)
    (G_h1 : (firstPar Bs.G₀.first (gpOf Z)).seeds = 1)
    (G_hpow : powB (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) 128
      = true)
    {G_nGr : ℕ}
    (G_rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE G_nGr (whereOf
            Z).lin.kCol)
    (G_dg : Bool)
    (G_mat : (CellsQ rows cols) → Fin G_nGr → (Fin (whereOf Z).lin.kCol → Bool) → GE)
    (G_hNt : Dm.N.treesAt psF[2 + 1]? = Dm.N.treesAt psF[2]? + (layOf (firstPar Bs.G₀.first (gpOf
      Z))).shapes.size)
    (G_hNm : Dm.N.msgsAt psF[2 + 1]? = Dm.N.msgsAt psF[2]? + (firstPar Bs.G₀.first (gpOf
      Z)).sent.size)
    (G_hFlC : FillsK13C (whereOf Z) Dm.N (mgAll Dm mgBase) Dm.pubD.cs Dm.arr G_mat Dm.G Dm.smp
      Dm.ms Dm.decT)
    (G_hft : dk.ft = 0)
    (G_hPlG : PlanG G_X Dm.pubD.nsOf Dm.pubD.d3 G_dg Dm.shape Dm.layout)
    (G_hplan : ∀ nm : String, (openingZero Bs.G₀.first (gpOf Z) nm G_X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl).planOk =
      true)
    (G_hSeats : PlanGSeats dk.L dk.M Dm.N psF[2]? (firstPar Bs.G₀.first (gpOf Z)))
    (G_hft1 : (firstPar Bs.G₀.first (gpOf Z)).gp.firstTree = 0)
    (G_hdg : First.Look.k3SortAt Dm.pubD.d3.X 0 2 = some G_dg)
    (G_hreq : ∀ x x' : ProofFile.InstPub × S, x'.1 = x.1 → Dm.H.req x' = Dm.H.req x)
    (G_hdig : ∀ (x x' : ProofFile.InstPub × S) (y y' : Strs) w k, x'.1 = x.1 → y'.cell = y.cell →
      Dm.digitsPart k x' y' w → Dm.digitsPart k x y w)
    (G_hhead : ∀ (nm : String) (x x' : ProofFile.InstPub × S) (y y' : Strs) w p i, StepG Cl Bs.G₀.first
      (gpOf Z) nm G_X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol x x' →
      (mgAll Dm mgBase).pub .unheard x = true → y'.cell = y.cell → Dm.headPart p i x' y' w →
      Dm.headPart p i x y w)
    (G_hb0 : First.FillSent.baseAt Dm.N Sound.linksFull psF 0 = 0)
    (G_Y : Stages.LinkH)
    (G_hY : Dm.built[0]? = some G_Y)
    (G_hYF : G_Y.Fp = G_X.X.Fp)
    (G_hownB : ownSeatsB Dm.N (openAt Sound.linksFull psF (2 + 1)) (firstPar Bs.G₀.first (gpOf Z))
      (((Dm.shape.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
      (Dm.N.treesAt psF[2]?) = true)
    (G_HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) → d₁.kind = .seeds
      → ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] → PlanAt (Sound.frameAt
      (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) Dm.pubD.cs Dm.G Dm.ms (firstPar
      Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) (nTrees ((dataOf aN R₁ R₂
      R₃).ds₁.take (inFront c 2))) d₁ d₂ (First.sampledIn Dm.N (openAt Sound.linksFull psF (2 +
      1))))
    (G_hbaseT : Dm.N.treesAt psF[2]? = (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))))
    (G_hsam : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, ∀ m' ∈ Dm.ms, SitsAt m'
      (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c
      2))) j.val).1 (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂
      R₃).ds₁.take (inFront c 2))) j.val).2 → sampledAt (firstPar Bs.G₀.first (gpOf Z)) j)
    (G_hpl : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, seats[Dm.N.msgsAt
      psF[2]? + j.val]? = some (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁
      R₂ R₃).ds₁.take (inFront c 2))) j.val))
    (G_hFacts : ∀ j a, Rch j a → j = 2 ∨ j = 2 + 1 → a.1.2.failed = none → FactsG (dG Z Dm.pubD.cs
      Dm.shape Dm.layout Dm.N G_rwD) dk Dm.pubD.d3 (mgAll Dm mgBase) a.1) :
    ∀ i q a, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf linksFull true)[i]? = some a → a.kind =
      KindName.K1 → TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a
      => a) Rch i (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀
      tokOf Dm.N linksFull (flatPlacesOf linksFull true) (fun a => a) k) i)) :=
  k01_law_frameR Dm.N (mgAll Dm mgBase) Rch (fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms
    Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true) (fun a => a) k)
    (k01_fifty_atBase Dm dk xb hS hR O hT seats c₀ tokOf hc hs hC hWr hCap hOk hRoots hRows hBook
      hFence hSent hBlind hNd hSeats hRd hreq hhead hdig Wp hmono hheard hAtA hPlanR hTold dep
      hFit hDsh hDlk hP1 hArm hwtR Rch hxb hFacts hHand hsmp hidx hft hPlan3 hSortB)
    (first_tiedR_atBase Dm hS hR O hT Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms c₀ tokOf hC hWr G_hU
      G_hCap G_X G_hX (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) G_hCond G_h1 G_hpow G_rwD dk G_dg
      G_mat G_hNt G_hNm G_hFlC G_hft G_hPlG G_hplan G_hSeats G_hft1 hBlind hDlk G_hdg G_hreq
      G_hdig G_hhead G_hb0 G_Y G_hY G_hYF Sound.bookFitsB_iff G_hownB (hNew0_weak Dm.pubD.cs Dm.G
      Dm.smp Dm.ms Dm.N (plusG (dG Z Dm.pubD.cs Dm.shape Dm.layout Dm.N G_rwD) dk Dm.pubD.d3
      (mgAll Dm mgBase)) rfl rfl rfl G_X G_HP G_hbaseT K13.Law.bookFitsItem Sound.bookFitsB
      Sound.bookFitsB_iff (fun _ => rfl) (bookFits_openG Dm (dG Z Dm.pubD.cs Dm.shape Dm.layout
      Dm.N G_rwD) dk Dm.pubD.d3) seats hsmp G_hsam G_hCond hNd G_hpl) Rch G_hFacts (hHand 2))
    (w_tiedR_at9c hS hR O hT Dm.N Dm Dm.G Dm.arr Dm.ms Dm.decT c₀ tokOf hC hWr W_hCap W_msg W_hm
      Dm.pubD.cs W_hcs W_rad Dm.smp W_hCond W_h1 W_hpow Dm.shape Dm.layout W_rwD dk W_mat W_y₀
      W_hNt W_hNm W_hFlC W_hft Sound.bookFitsB_iff W_hPl3 W_h4 W_hplan W_hsmp hBlind W_hPl W_hbase
      (hNewW_weak Dm.pubD.cs Dm.G Dm.smp Dm.ms Dm.N (plus13 (dW Z W_msg Dm.shape Dm.layout Dm.N
      W_rwD) dk (mgAll Dm mgBase)) rfl rfl rfl W_msg W_rad W_HP W_hbaseT K13.Law.bookFitsItem
      Sound.bookFitsB Sound.bookFitsB_iff (fun _ => rfl) (bookFits_openW Dm (dW Z W_msg Dm.shape
      Dm.layout Dm.N W_rwD) dk) seats hsmp W_hsam W_hCond hNd W_hpl) (hshownW_of Dm.pubD.cs Dm.G
      Dm.smp Dm.ms Dm.N (plus13 (dW Z W_msg Dm.shape Dm.layout Dm.N W_rwD) dk (mgAll Dm mgBase))
      rfl W_msg W_rad W_HP) Rch W_hFacts (hHand 356))

end

end VerifiableInference.Desc.K1
