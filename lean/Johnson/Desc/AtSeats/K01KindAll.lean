-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
NO EXAMPLE: IT COUNTS FOR NOTHING. Made over k01_kind_paidThree (Johnson/Desc/AtSeats/K01KindPaidThree.lean; beneath it k01_fifty_paid, Johnson/Desc/K1/Law/K01FiftyPaid.lean): the readers' law and the arms' law are CALLED beneath, behind a test xbK on the state (TablesOk ∧ ArmOk J) that rides over the fifty places; J IS LAID AT A CLOSED TERM: JReach …: «the state of a reached and typed statement in front of some link's reads, inside the narrow promise, without a mark»: so every field behind ReadsFence or «J s →» speaks of such states alone. Whether the condition can be met is shown nowhere (by a text of this project that is not in this repository: not shown and
not refuted).
KIND K1's FIELD FOR THE KINDS' JOIN, in the form of K3Bridge.lean and the bridges beside it:
  P5J.AtMgA.K1Cond h 𝔏 : Prop      ·      P5J.k01_kind_all h 𝔏 q₁ q₂ q₃ (C : h.K1Cond 𝔏) : h.Kind 𝔏 KindName.K1.
MADE BY PROGRAM out of k01_kind_paidThree's own binder text (154 binders: 101 premises, 53 letters): no binder is retyped by hand.
  K1Left …      a structure of the 38 premises that are left, each TO THE LETTER, at k01_kind_paidThree's own letters, sorted:
                the opening 1 · the door's two pins 2 · laws on a step 8 · facts along reached states 3 · tests and equations on the public values 20 ·
                what hangs on the data or on what the sub-protocols tell 4.
  K1Cond h 𝔏    there are Bs · base₀ · Wp · shp · lay₀ · cU · msR · lay6 · num6 · rad6 · seatT · W_rwD · W_y₀ · G_X · G_rwD with K1Left AT THE CLOSED CONSTANT's LETTERS: Dm := h.𝔇 · the
                description := F0T … · the data := D.at frS.P.T.a · tokOf := At.tokOf (the letter 𝔏 does not occur in the condition's body) ·
                «reached» := RchPub (F0T …) typedPub: REACHED, AT A TYPED INSTANCE's PUBLIC PART: no more than the counted form's own fence.
  k01_kind_all  one call of k01_kind_paidThree; PAID INSIDE (65): hS · hR · hD · hp · q₁ · q₂ · q₃ · hBlind · hHand · hDlk · hsmp · hOk · hc · hs · hDsh · W_hft · G_hft · hft · G_hU · W_hFlC · G_hFlC · W_hcs · W_hbaseT · G_hbaseT · W_hm · W_h1 · G_h1 · G_hft1 · W_hNt · W_hNm · W_h4 · W_hsmp · W_hPl · W_hbase · W_hsam · W_hpl · G_hNt · G_hNm · G_hSeats · G_hb0 · G_hownB · G_hsam · G_hpl · eG · W_hCond · W_hpow · W_hplan · G_hplan · G_hreq · G_hdig · G_hhead · G_hdg · G_hCond · G_hpow · hreq · hhead · hdig · hN · hseats · hCnt · hLk · hMk · G_hY · G_hYF · eD; the end by kindA_iff.
IT PAYS NO LAW. What is not claimed. That the condition can be met. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K01KindPaidThree
import Johnson.Desc.AtSeats.K13KindRowA
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.TiesAtAll2
import Johnson.Desc.K1.Law.FiftyAtAll
import Johnson.Desc.K1.Law.JReach

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

open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)
open VerifiableInference.Desc.Sound (threeCap_ofDesc)

/-- **What is left of k01_kind_paidThree's premises**, at its own letters. -/
structure K1Left
    (P : VerifierAndGoals.PublicFiles)
    (lay : ByteArray)
    (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase)
    (base₀ : List (Block S Cl))
    (c : Chain S Cl)
    (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat)
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV)
    (dk : K12Data)
    (J : S → Prop)
    (D : WholeD)
    (Wp : OnBytes.Model.Verify.Public)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt D (Sound.allOf D) D.key₁ 0).E.Str → Prop)
    (s : ReqShape)
    (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout)
    (cU : ℕ × String)
    (msR : List Mem)
    (lay6 : OnBytes.Params.ReqLayout)
    (num6 : ℕ → ℕ → ℕ)
    (rad6 : OnBytes.OracleShape → ℕ)
    (seatT : Fin (sigListCalls Dm.sent rad6 24).length → ℕ × ℕ)
    (W_msg : Array OracleNotice)
    (W_rad : ℕ → ℕ)
    (W_nWr : ℕ)
    (W_rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE W_nWr (whereOf
            Z).lin.kCol)
    (W_y₀ : (Sound.frameAt D (Sound.allOf D) D.key₁ 0).E.Str)
    (G_X : LayPar)
    (G_nGr : ℕ)
    (G_rwD : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → K13.Law.Wit GE G_nGr (whereOf
            Z).lin.kCol)
    (G_dg : Bool) : Prop where
  /- the maker's opening, at the letters Bs · base₀ that the other fields read: 1 -/
  O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B
  /- THE DOOR's TWO PINS: tests with code on the public files (they follow from the head's scope and «laid»: a lemma of other files (P5J.pins_of_laid, Johnson/Goal/Skeleton/PinsOfLaid.lean | P5J.cutIs_of_laid, Johnson/Goal/Skeleton/CutIsOfLaid.lean)): 2 -/
  pin1 : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true
  pin2 : VerifiableInference.PlanWritten.cutIs F = true
  /- LAWS ON A STEP (other files', or K1's files', owed): from the state behind a sub-protocol's yes to the state in front, or at the promise: 8 -/
  hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w, (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2
            cc mm) → Dm.wt 24 a' y' w → Dm.wt 24 a y w
  hheard : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull
      (flatPlacesOf linksFull true) (noL 24 true) x y → ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2
      = some H
  hLay : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂ R₃
      → ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c l X arrs x x' y
      y' w p A B → (linksFull[l]?).getD .layers = .layers → ∀ b₀ o hp tl', x.2.here = .lay b₀ →
      b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp → x'.2.tl? = some tl' → ∀ e cc, NamedEntry
      (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc → ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
      LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl'
      M o n (Dm.A1 l x' w)
  hPl' : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂ R₃
      → ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c 24 X arrs x x' y
      y' w p A B → p.2 = "planes" → PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B
      (seatTab Dm.cs Dm.arr Dm.ms w)
  hElse : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂ R₃
      → ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c 24 X arrs x x' y
      y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" → ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0)
      (Dm.N.group 24) p.1 p.2 x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)
  hidle : ∀ l, l ≠ 24 → ∀ a y w, Dm.wt l a y w
  hheard2 : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y → ∃ H, (seatAt Wp.hS (readsOf Wp)).heard
      x.2 = some H
  hquiet : ∀ X, Bs.G₀.built[24]? = some X → ∃ P, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head P
  /- FACTS ALONG «REACHED AND TYPED» STATES (the induction along the run owes them): 3 -/
  hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d +
      2 + 1) → ∀ a, Rch j a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true)
      (fun a => a) j a → a.1.2.failed = none → FactsK13 (d13 Dm) dk (mgAll Dm mgBase) a.1 ∧ (∀ L,
      a.1.2.link? = some L → L.check.frame.group = Dm.N.groupAt l ∧ L.check.frame.shape = (d13
      Dm).shape) ∧ (xbK Bs.G₀ J) a.1.2 = true
  W_hFacts : ∀ j a, Rch j a → a.1.2.failed = none → FactsK13
      (_root_.VerifiableInference.Desc.K1.dW Z W_msg Dm.shape Dm.layout Dm.N W_rwD) dk (mgAll Dm
      mgBase) a.1
  G_hFacts : ∀ j a, Rch j a → j = 2 ∨ j = 2 + 1 → a.1.2.failed = none → FactsG (dG Z Dm.pubD.cs
      Dm.shape Dm.layout Dm.N G_rwD) dk Dm.pubD.d3 (mgAll Dm mgBase) a.1
  /- TESTS AND EQUATIONS ON THE PUBLIC VALUES (the plan · the numbers · the seats): 20 -/
  hUA : Dm.uA = uArm XV
  hJt : ∀ s, J s → TlIsPlan XV s
  hJl : ∀ s, J s → LiveIs shp lay₀ s
  hWn : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap
  hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap
      → ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC → ∃ z < Ap.nW,
      r = z / plannedK Ap ∧ i = z % plannedK Ap
  hAtt'' : ∀ (td : ℕ) (R₁ R₂ R₃ : Rounds), td = (FD Z A B c).tableDepth → D = dataOf td R₁ R₂
      R₃ → ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs td R₁ R₂ R₃ c l X arrs x
      x' y y' w p A B → (linksFull[l]?).getD .layers = .attention → ∀ a₀ Ap tl', x.2.here = .att
      a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl → x'.2.tl? = some tl' → ∃ i, AttLeft2
      (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)
  hUH : Dm.uH = uHeadK6 XV
  hWX : Bs.G₀.W = XV
  hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU
  hKw : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t → XV.H.nU.getD 2 0 ≤
      t.2.1
  hLaid6 : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true
  hCalls : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num6
      Dm.sent rad6 24 seatT
  hJH : ∀ s, J s → JH XV (Dm.N.sent 24 0) Dm.arr Dm.N num6 lay6 s
  hsub : ∀ x ∈ Dm.N.sent 24 0, x ∈ Dm.N.group 24
  hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?
  W_hPl3 : PlanM3 dk.L dk.M Dm.ms Dm.pubD.cs Dm.N
  W_HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z W_msg) → d₁.kind = .seeds → (D.ds₁.drop
      (inFront c 356)).take 2 = [d₁, d₂] → PlanAt (Sound.frameAt D (Sound.allOf D) D.key₁ 0)
      Dm.pubD.cs Dm.G Dm.ms (parWZ Z W_msg) W_rad (nTrees (D.ds₁.take (inFront c 356))) d₁ d₂
      [Dm.N.w]
  G_hX : Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some G_X
  G_hPlG : PlanG G_X Dm.pubD.nsOf Dm.pubD.d3 G_dg Dm.shape Dm.layout
  G_HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) → d₁.kind = .seeds
      → (D.ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] → PlanAt (Sound.frameAt D (Sound.allOf D)
      D.key₁ 0) Dm.pubD.cs Dm.G Dm.ms (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar
      Bs.G₀.first (gpOf Z))) (nTrees (D.ds₁.take (inFront c 2))) d₁ d₂ (First.sampledIn Dm.N
      (openAt Sound.linksFull psF (2 + 1)))
  /- WHAT HANGS ON THE DATA OR ON WHAT THE SUB-PROTOCOLS TELL (the written cut): 4 -/
  hPlanR : ∀ l, l < 25 → ∀ d : Bool, PlanRest Dm.pubD.cs Dm.G Dm.ms (parL Z Bs.G₀ l d) (radRec
      (recL l d) (parL Z Bs.G₀ l d)) (baseD D c l d) (Dm.N.sent l (momL d))
  ht : 83 ≤ Three.rootsIn dryProofFull.1
  hT83 : nTrees (dataOf (FD Z A B c).tableDepth dryProofFull.1 dryProofFull.2.1
      dryProofFull.2.2).ds₁ ≤ 83
  h4 : ∀ l, l < 25 → ∀ d : Bool, ∀ n, n < (layOf (parL Z Bs.G₀ l d)).shapes.size →
      HashBuild.laidFull[nTrees (D.ds₁.take (inFront c (noL l d))) + n]? = some (((layOf (parL Z
      Bs.G₀ l d)).shapes.getD n {}).logN, ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).mainWidth
      + ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).maskWidth)

end

section
open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)
open VerifiableInference.Desc.Sound (threeCap_ofDesc)
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : First.Look.Place}

/-- **Kind K1's condition, at the closed constant and at reached states with a typed instance's public part.** -/
def _root_.P5J.AtMgA.K1Cond (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  ∃ Bs base₀ Wp shp lay₀ cU msR lay6 num6 rad6 seatT W_rwD W_y₀ G_X G_rwD,
    K1Left Z
      Z.lay
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
      Zp
      Bs
      base₀
      cF
      (_root_.Desc.K14.Law.seatZ Zp Np)
      (_root_.Desc.K14.Law.secondAt Zp Np)
      h.𝔇
      (⟨0, K13.Law.LFull, K13.Law.MFull⟩ : K12Data)
      (JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) h.𝔇.N (mgAll h.𝔇 mgBase))
      (D.at frS.P.T.a)
      Wp
      (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub)
      (P5J.At.shape Zp)
      shp
      lay₀
      cU
      msR
      lay6
      num6
      rad6
      seatT
      K13.Law.wMsgFull
      (radRec 81 (parWZ Zp K13.Law.wMsgFull))
      OnBytes.Flat.numsFull.rows
      W_rwD
      W_y₀
      G_X
      OnBytes.Flat.numsFull.rows
      G_rwD
      false

/-- **The field.** -/
theorem _root_.P5J.k01_kind_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K1Cond 𝔏) : h.Kind 𝔏 KindName.K1 := by
  obtain ⟨Bs, base₀, Wp, shp, lay₀, cU, msR, lay6, num6, rad6, seatT, W_rwD, W_y₀, G_X, G_rwD, C⟩ := C
  obtain ⟨G_Y, hGY, hGYF⟩ := G_hY_atAll h C.O G_X C.G_hX
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth h.scope h.laid]; exact h.laid.data
  refine (P5J.kindA_iff h 𝔏 KindName.K1).2 ?_
  exact k01_kind_paidThree
    h.𝔇
    (⟨0, K13.Law.LFull, K13.Law.MFull⟩ : K12Data)
    (JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) h.𝔇.N (mgAll h.𝔇 mgBase))
    h.scope
    h.reads
    C.O
    hD
    h.laid.planOk
    q₁
    q₂
    q₃
    𝔏.e₁
    𝔏.e₂
    𝔏.e₃
    𝔏.dW
    𝔏.wEnd
    (P5J.At.seats Zp)
    𝔏.c₀
    P5J.At.tokOf
    (hc_atAll h C.O C.pin1)
    (hs_atAll h C.O C.pin1)
    (hOk_atAll h C.O)
    (K13.Law.decBlind_atAll h)
    (hreq_atAll h Bs.G₀)
    (hhead_atAll h Bs.G₀ _ _)
    (hdig_atAll h Bs.G₀ _ _)
    Wp
    C.hmono
    C.hheard
    C.hPlanR
    (hDsh_atAll h C.O C.pin1)
    (hDlk_atAll h)
    (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub)
    C.hFacts
    (fun _ _ hq => handsOn_pub (threeCap_ofDesc 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd hD h.laid.planOk q₁ q₂ q₃) K13.Law.typedPub hq _)
    (hsmp_atAll h)
    (congrArg (·.firstTree) (K13.Law.gpOf_in_scope h.scope h.laid.pub C.pin1)).symm
    (hN_atAll h C.O C.pin1)
    (hseats_atAll h C.O C.pin1)
    (hCnt_atAll C.pin2)
    rfl
    rfl
    C.hLay
    C.hUA
    C.hJt
    shp
    lay₀
    C.hJl
    C.hWn
    C.hSec
    C.hAtt''
    C.hUH
    C.hWX
    cU
    C.hU
    C.hKw
    msR
    lay6
    num6
    rad6
    seatT
    C.hLaid6
    C.hCalls
    C.hJH
    C.hsub
    C.hPl'
    C.hElse
    C.hlk
    (by rw [P5J.LaidAt.atDepth h.scope h.laid, K13.Law.data_written h]; rfl)
    (fun _ => rfl)
    C.ht
    C.hT83
    C.h4
    C.hidle
    C.hheard2
    C.hquiet
    K13.Law.wMsgFull
    (W_hm_atAll h C.O C.pin1)
    (W_hcs_atAll h _)
    (radRec 81 (parWZ Zp K13.Law.wMsgFull))
    (W_hCond_atAll h C.O C.pin1)
    (W_h1_atAll h C.O C.pin1)
    (W_hpow_atAll h C.O C.pin1)
    W_rwD
    h.𝔇.mat13
    W_y₀
    (W_hNt_atAll h C.O C.pin1 C.pin2)
    (W_hNm_atAll h C.O C.pin1 C.pin2)
    (W_hFlC_atAll h)
    rfl
    C.W_hPl3
    (W_h4_atAll h C.O C.pin1 C.pin2 rfl rfl)
    (W_hplan_atAll h C.O C.pin1)
    (W_hsmp_atAll h C.O C.pin1 C.pin2)
    (fun _ => W_sits_atAll h C.O C.pin1 C.pin2)
    (W_hbase_atAll h C.O C.pin1 C.pin2)
    C.W_HP
    (W_hbaseT_atAll h C.O)
    (W_hsam_atAll h C.O C.pin1 C.pin2)
    (W_hpl_atAll h C.O C.pin1 C.pin2)
    C.W_hFacts
    (G_hU_atAll h C.O)
    G_X
    C.G_hX
    (G_hCond_atAll h C.O C.pin1)
    (G_h1_atAll h C.O C.pin1)
    (G_hpow_atAll h C.O C.pin1)
    G_rwD
    false
    h.𝔇.mat13
    (G_hNt_atAll h C.O C.pin1 C.pin2)
    (G_hNm_atAll h C.O C.pin1 C.pin2)
    (G_hFlC_atAll h)
    rfl
    C.G_hPlG
    (G_hplan_atAll h C.O G_X)
    (G_hSeats_atAll h C.O C.pin1 C.pin2 rfl rfl)
    (G_hft1_atAll h C.O C.pin1)
    (G_hdg_atAll h)
    (G_hreq_atAll h)
    (G_hdig_atAll h)
    (G_hhead_atAll h Bs.G₀ G_X)
    (G_hb0_atAll h C.O C.pin1 C.pin2)
    G_Y
    hGY
    hGYF
    (G_hownB_atAll h C.O C.pin1 C.pin2)
    C.G_HP
    (G_hbaseT_atAll h C.O)
    (G_hsam_atAll h C.O C.pin1 C.pin2)
    (G_hpl_atAll h C.O C.pin1 C.pin2)
    C.G_hFacts

end

end VerifiableInference.Desc.K1
