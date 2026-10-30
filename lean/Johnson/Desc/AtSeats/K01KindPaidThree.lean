-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K01KindPaidThree.lean: KIND K1's SHARE OF THE FIRST TABLE's TIES, ALL 52
PLACES, IN THE SECOND FORM, AT `mgAll Dm mgBase`, WITH THE FIFTY's PAYERS CALLED, AT THE ONE
CLOSED FORM OF THE PIECES (`threeCap`). One statement, MADE BY PROGRAM out of
`k01_kind_paid`'s own binders (Johnson/Desc/AtSeats/K01KindPaid.lean): a call, by `six_together`
(Johnson/Desc/Sound/SixTogether.lean). WHAT FALLS: the premises on the pieces (hT, hC, hWr, the
three on the cap, hRoots, hFit). A BINDER THAT NAMES THE THREE LISTS OF ROUNDS THEMSELVES, and not
the data made of them, is bound at every three lists of which the laid value's data are made: the
arms' binders (through the fence `ReadsFence`, which reads them in one antecedent that no payer
spends). NO EXAMPLE. What is not claimed. The premises. Nothing on soundness. Terms:
lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.K01KindPaid
import Johnson.Desc.K1.Law.K01FiftyAtThree

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

/-- **KIND K1's SHARE, ALL 52 PLACES, THE FIFTY's PAYERS CALLED,
AT THE ONE CLOSED FORM OF THE PIECES.** -/
theorem k01_kind_paidThree
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
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV)
    (dk : K12Data)
    (J : S → Prop)
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {D : WholeD}
    {file : String}
    (hD : (FD Z A B c).data file = .ok D)
    (hp : (FD Z A B c).planOk = true)
    {b₁ : Block (FD Z A B c).S₁ (FD Z A B c).Cl}
    {l₁ : List (Block (FD Z A B c).S₁ (FD Z A B c).Cl)}
    {b₂ : Block (FD Z A B c).S₂ (FD Z A B c).Cl}
    {l₂ : List (Block (FD Z A B c).S₂ (FD Z A B c).Cl)}
    {b₃ : Block (FD Z A B c).S₃ (FD Z A B c).Cl}
    {l₃ : List (Block (FD Z A B c).S₃ (FD Z A B c).Cl)}
    (q₁ : (FD Z A B c).first.blocksInOrder = b₁ :: l₁)
    (q₂ : (FD Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Z A B c).second.blocksInOrder = b₃ :: l₃)
    (e₁ : (i : ℕ) → (ds : List RDT) → ((FD Z A B c).XiPub × (FD Z A B c).S₁) × (Sound.frameAt D
      (Sound.allOf D) D.key₁ 0).E.Str → _root_.Iop.Tr (uLT (ckP .two) ds) → (Wit (CellsQ rows
      cols) Tok MsgT) → (Wit (CellsQ rows cols) Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) → (((FD Z A B c).XiPub × (FD Z A B c).S₁) × (FD Z A B c).S₂) ×
      (Sound.frameAt D (Sound.allOf D) D.key₂ 0).E.Str → _root_.Iop.Tr (uLT (ckP .two) ds) → (Wit
      (CellsQ rows cols) Tok MsgT) → (Wit (CellsQ rows cols) Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) → (((FD Z A B c).XiPub × (FD Z A B c).S₁ × (FD Z A B c).S₂) ×
      (FD Z A B c).S₃) × (Sound.frameAt D (Sound.allOf D) D.key₃ (FD Z A B c).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → (Wit (CellsQ rows cols) Tok MsgT) → (Wit (CellsQ rows
      cols) Tok MsgT))
    (dW wEnd : (Wit (CellsQ rows cols) Tok MsgT))
    (seats : List (ℕ × ℕ))
    (c₀ : CellsQ rows cols)
    (tokOf : ProofFile.InstPub × S → Tok)
    (hc : Bs.G₀.first.codes = codesFull2)
    (hs : Bs.G₀.first.shape = shapeFull)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hBlind : K13.Law.DecBlind Dm.decT)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z
      Bs.G₀ l d X arrs) x x' → Dm.H.req x' = Dm.H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)
      (xbK Bs.G₀ J)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseD D c
      l d) y y' → Item.constr (headLink XV) p ∈ openAt linksFull (flatPlacesOf linksFull true)
      (noL l d) → Dm.headPart p i x' y' w → Dm.headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf
      (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK
      Bs.G₀ J)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseD D c l d)
      y y' → Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d)
      → Dm.digitsPart m x' y' w → Dm.digitsPart m x y w)
    (Wp : OnBytes.Model.Verify.Public)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w, (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2
            cc mm) → Dm.wt 24 a' y' w → Dm.wt 24 a y w)
    (hheard : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull
      (flatPlacesOf linksFull true) (noL 24 true) x y → ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2
      = some H)
    (hPlanR : ∀ l, l < 25 → ∀ d : Bool, PlanRest Dm.pubD.cs Dm.G Dm.ms (parL Z Bs.G₀ l d) (radRec
      (recL l d) (parL Z Bs.G₀ l d)) (baseD D c l d) (Dm.N.sent l (momL d)))
    (hDsh : Dm.shape = shapeFull)
    (hDlk : Dm.links = linksFull)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt D (Sound.allOf D) D.key₁ 0).E.Str → Prop)
    (hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d +
      2 + 1) → ∀ a, Rch j a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true)
      (fun a => a) j a → a.1.2.failed = none → FactsK13 (d13 Dm) dk (mgAll Dm mgBase) a.1 ∧ (∀ L,
      a.1.2.link? = some L → L.check.frame.group = Dm.N.groupAt l ∧ L.check.frame.shape = (d13
      Dm).shape) ∧ (xbK Bs.G₀ J) a.1.2 = true)
    (hHand : ∀ i q, ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ :: (threeCap
      (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[i]? = some q → HandsOn Rch i
      (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N
      linksFull (flatPlacesOf linksFull true) (fun a => a) k) i)))
    (hsmp : Dm.smp = smpNamed Dm.cs seats)
    (hft : dk.ft = (gpOf Z).firstTree)
    {s : ReqShape}
    {links : List ModelPart}
    (hN : Dm.N = P5T.N0Full.atBlocks s links c.blocksInOrder)
    (hseats : seats = K13.Law.seatsFull)
    (hCnt : K13.Law.CountsAre (First.toldOf c.blocksInOrder))
    (hLk : dk.L = K13.Law.LFull)
    (hMk : dk.M = K13.Law.MFull)
    (hLay : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂ R₃
      → ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c l X arrs x x' y
      y' w p A B → (linksFull[l]?).getD .layers = .layers → ∀ b₀ o hp tl', x.2.here = .lay b₀ →
      b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp → x'.2.tl? = some tl' → ∀ e cc, NamedEntry
      (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc → ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
      LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl'
      M o n (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hJt : ∀ s, J s → TlIsPlan XV s)
    (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout)
    (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hWn : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap
      → ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC → ∃ z < Ap.nW,
      r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂
      R₃ → ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c l X arrs x
      x' y y' w p A B → (linksFull[l]?).getD .layers = .attention → ∀ a₀ Ap tl', x.2.here = .att
      a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl → x'.2.tl? = some tl' → ∃ i, AttLeft2
      (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w))
    (hUH : Dm.uH = uHeadK6 XV)
    (hWX : Bs.G₀.W = XV)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hKw : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t → XV.H.nU.getD 2 0 ≤
      t.2.1)
    (msR : List Mem)
    (lay6 : OnBytes.Params.ReqLayout)
    (num6 : ℕ → ℕ → ℕ)
    (rad6 : OnBytes.OracleShape → ℕ)
    (seatT : Fin (sigListCalls Dm.sent rad6 24).length → ℕ × ℕ)
    (hLaid6 : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hCalls : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num6
      Dm.sent rad6 24 seatT)
    (hJH : ∀ s, J s → JH XV (Dm.N.sent 24 0) Dm.arr Dm.N num6 lay6 s)
    (hsub : ∀ x ∈ Dm.N.sent 24 0, x ∈ Dm.N.group 24)
    (hPl' : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂ R₃
      → ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c 24 X arrs x x' y
      y' w p A B → p.2 = "planes" → PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B
      (seatTab Dm.cs Dm.arr Dm.ms w))
    (hElse : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂ R₃
      → ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c 24 X arrs x x' y
      y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" → ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0)
      (Dm.N.group 24) p.1 p.2 x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24))
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?)
    (eD : D.ds₁ = (dataOf (FD Z A B c).tableDepth dryProofFull.1 dryProofFull.2.1
      dryProofFull.2.2).ds₁)
    (eG : ∀ j, Dm.G.oracleAt j = F.oracleAt j)
    (ht : 83 ≤ Three.rootsIn dryProofFull.1)
    (hT83 : nTrees (dataOf (FD Z A B c).tableDepth dryProofFull.1 dryProofFull.2.1
      dryProofFull.2.2).ds₁ ≤ 83)
    (h4 : ∀ l, l < 25 → ∀ d : Bool, ∀ n, n < (layOf (parL Z Bs.G₀ l d)).shapes.size →
      HashBuild.laidFull[nTrees (D.ds₁.take (inFront c (noL l d))) + n]? = some (((layOf (parL Z
      Bs.G₀ l d)).shapes.getD n {}).logN, ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).mainWidth
      + ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).maskWidth))
    (hidle : ∀ l, l ≠ 24 → ∀ a y w, Dm.wt l a y w)
    (hheard2 : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y → ∃ H, (seatAt Wp.hS (readsOf Wp)).heard
      x.2 = some H)
    (hquiet : ∀ X, Bs.G₀.built[24]? = some X → ∃ P, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head P)
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
    (W_y₀ : (Sound.frameAt D (Sound.allOf D) D.key₁ 0).E.Str)
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
    (W_hPl : wSitsItem ∈ (First.pubSets (plus13 (_root_.VerifiableInference.Desc.K1.dW Z W_msg
      Dm.shape Dm.layout Dm.N W_rwD) dk (mgAll Dm mgBase)).more Sound.linksFull psF)[356 +
      1]?.getD [] → planSitsB (whereOf Z) (parWZ Z W_msg) = true ∧ planSeatB Dm.N psF[356]? (parWZ
      Z W_msg) = true)
    (W_hbase : Dm.N.index.1 < nTrees (D.ds₁.take (inFront c 356)))
    (W_HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z W_msg) → d₁.kind = .seeds → (D.ds₁.drop
      (inFront c 356)).take 2 = [d₁, d₂] → PlanAt (Sound.frameAt D (Sound.allOf D) D.key₁ 0)
      Dm.pubD.cs Dm.G Dm.ms (parWZ Z W_msg) W_rad (nTrees (D.ds₁.take (inFront c 356))) d₁ d₂
      [Dm.N.w])
    (W_hbaseT : Dm.N.treesAt psF[356]? = (nTrees (D.ds₁.take (inFront c 356))))
    (W_hsam : ∀ j : Fin (shapesOf (parWZ Z W_msg)).length, ∀ m' ∈ Dm.ms, SitsAt m' (seatOfMsg
      (parWZ Z W_msg) (nTrees (D.ds₁.take (inFront c 356))) j.val).1 (seatOfMsg (parWZ Z W_msg)
      (nTrees (D.ds₁.take (inFront c 356))) j.val).2 → sampledAt (parWZ Z W_msg) j)
    (W_hpl : ∀ j : Fin (shapesOf (parWZ Z W_msg)).length, seats[Dm.N.msgsAt psF[356]? + j.val]? =
      some (seatOfMsg (parWZ Z W_msg) (nTrees (D.ds₁.take (inFront c 356))) j.val))
    (W_hFacts : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13
      (_root_.VerifiableInference.Desc.K1.dW Z W_msg Dm.shape Dm.layout Dm.N W_rwD) dk (mgAll Dm
      mgBase) a.1)
    (G_hU : ∃ (e : Block S Cl) (nm : String) (G_X : LayPar), c.blocksInOrder[2]? = some e ∧
      Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some G_X ∧ e.UnderR (openingZero
      Bs.G₀.first (gpOf Z) nm G_X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links)
      Z.first.lin.kCol : Block S Cl))
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
      → (D.ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] → PlanAt (Sound.frameAt D (Sound.allOf D)
      D.key₁ 0) Dm.pubD.cs Dm.G Dm.ms (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar
      Bs.G₀.first (gpOf Z))) (nTrees (D.ds₁.take (inFront c 2))) d₁ d₂ (First.sampledIn Dm.N
      (openAt Sound.linksFull psF (2 + 1))))
    (G_hbaseT : Dm.N.treesAt psF[2]? = (nTrees (D.ds₁.take (inFront c 2))))
    (G_hsam : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, ∀ m' ∈ Dm.ms, SitsAt m'
      (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees (D.ds₁.take (inFront c 2))) j.val).1
      (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees (D.ds₁.take (inFront c 2))) j.val).2 →
      sampledAt (firstPar Bs.G₀.first (gpOf Z)) j)
    (G_hpl : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, seats[Dm.N.msgsAt
      psF[2]? + j.val]? = some (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees (D.ds₁.take
      (inFront c 2))) j.val))
    (G_hFacts : ∀ j a, Rch j a → j = 2 ∨ j = 2 + 1 → a.1.2.failed = none → FactsG (dG Z Dm.pubD.cs
      Dm.shape Dm.layout Dm.N G_rwD) dk Dm.pubD.d3 (mgAll Dm mgBase) a.1) :
    ∀ i q a, ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ :: (threeCap (FD Z A
      B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[i]? = some q → (flatPlacesOf linksFull
      true)[i]? = some a → a.kind = KindName.K1 → TiedAtR Dm.N (mgAll Dm mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) Rch i (q.withMap ((fun k => extQAt Dm.pubD.cs
      Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true) (fun
      a => a) k) i)) := by
  obtain ⟨R₁, R₂, R₃, hDD, w₁, hRoots, hFit, hall⟩ := six_together (W := (Wit (CellsQ rows cols)
    Tok MsgT)) hD hp q₁ q₂ q₃
  subst hDD
  obtain ⟨hT, hC, herr⟩ := hall e₁ e₂ e₃ dW wEnd
  exact k01_kind_paid Dm dk J hS hR O hT seats c₀ tokOf hc hs hC w₁ (fun _ _ _ _ _ => herr _ _)
    hOk hRoots hBlind hreq hhead hdig Wp hmono hheard hPlanR _ (hFit _ _ _) hDsh hDlk Rch hFacts
    hHand hsmp hft hN hseats hCnt hLk hMk (hLay _ R₁ R₂ R₃ rfl rfl) hUA hJt shp lay₀ hJl hWn hSec
    (hAtt'' _ R₁ R₂ R₃ rfl rfl) hUH hWX cU hU hKw msR lay6 num6 rad6 seatT hLaid6 hCalls hJH hsub
    (hPl' _ R₁ R₂ R₃ rfl rfl) (hElse _ R₁ R₂ R₃ rfl rfl) hlk eD eG ht hT83 h4 hidle hheard2 hquiet
    (fun _ _ => herr _ _) W_msg W_hm W_hcs W_rad W_hCond W_h1 W_hpow W_rwD W_mat W_y₀ W_hNt W_hNm
    W_hFlC W_hft W_hPl3 W_h4 W_hplan W_hsmp W_hPl W_hbase W_HP W_hbaseT W_hsam W_hpl W_hFacts G_hU
    (fun _ _ => herr _ _) G_X G_hX G_hCond G_h1 G_hpow G_rwD G_dg G_mat G_hNt G_hNm G_hFlC G_hft
    G_hPlG G_hplan G_hSeats G_hft1 G_hdg G_hreq G_hdig G_hhead G_hb0 G_Y G_hY G_hYF G_hownB G_HP
    G_hbaseT G_hsam G_hpl G_hFacts

end

end VerifiableInference.Desc.K1
