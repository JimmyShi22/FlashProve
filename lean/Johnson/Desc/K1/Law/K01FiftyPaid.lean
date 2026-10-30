-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01FiftyPaid.lean: K01_law's FIFTY LATER PLACES, IN THE SECOND FORM, AT mgAll Dm mgBase: k01_fifty_atBase AT xb := xbK Bs.G₀ J, WITH THE PAYERS THAT ARE GENERAL IN Dm CALLED BY NAME:
  xbK G₀ J s := «TablesOk G₀.W.hS G₀.W.HLy G₀.W.H s ∧ ArmOk J s», as a Bool: the two facts on reached states that the readers' law at (24, reads) and the exchange's arms want inside the wider promise. J: A LETTER (what the arms' leftovers want of a reached state in front of its reads).
  hxb ⟸ tablesOk_later · armOk_later (both ride over the fifty; the second with no premise)
  the ten tests on the table's numbers and the seats' list (TestsAtCounts.lean) ⟸ FIVE equations: hN · hseats · hCnt («the written counts») · hLk · hMk
  hRd ⟸ hRd_any (ReadersHeadReads.lean): 278 of 278 pairs (run, place): left: hlk (its hX and hXW are paid off hWX: headLink_open, ReadersPaid.lean)
  hArm ⟸ arm_at_reads_three (ArmHead.lean): all three halves of the exchange, which the files on the three sorts of segment (layers, attention, output head) bring, an entry at a time, behind the tie and ArmOk J: with hK6_of | hPl_of (ArmHeadPaid | ArmPlanesPaid.lean: KS · hSt from the scope; both hRd from J's clause NoTables): and hAtt_of (ArmAttPaid.lean: attention's eight fall to four, under J's clause TlIsPlan XV): left: hLay · hUA · hJt (J s → TlIsPlan XV s; TlIsPlan asks TlLike: NM · mats · ix · gtTree alone) · shp lay₀ hJl (J s → LiveIs shp lay₀ s) · hWn hSec (on letters) · hAtt'' (AttLeft2: hin hM) [hAtt_of2, ArmAttEntry.lean] · hUH · hWX · hJH (J s → JH …: NoTables ∧ JHead: hT hRun hlay hMats at the state in front alone) · hsub · cU hU hKw (on letters alone) · msR lay6 num6 rad6 seatT hLaid6 hCalls (lab_of_calls' own, Johnson/Desc/Kinds/Law/FourRunsTie.lean, on letters alone) · hPl' (PlanesLeft4: hlen hHostC) · hElse [hK6_of4 | hPl_of3: hArr · hwide · both hbare · hlab off the promise at 342 itself]
  hwtR ⟸ hwtR_of (WtBackAtReads.lean): left: hidle · hheard2 (at 342) · hquiet
  hTold ⟸ hTold_atD (ToldAtD.lean): left: eD (the data's first chain's rounds are the written lists': A SENTENCE ON THE DATA, so that it goes to threeCap) · eG · ht · hT83 (both closed: at the written lists) · h4
  hSortB ⟸ sortB_ground (AtSeats/SortAtOpen.lean: sortB X = true ↔ headLink X = 24) at hWX: nothing left
THE STATEMENT IS MADE BY PROGRAM OUT OF k01_fifty_atBase's AND THE PAYERS' OWN BINDERS.
What is not claimed. No premise is shown; NO EXAMPLE (nor, by report, is one shown elsewhere). hFacts' third clause (xbK at reached states at the two borders of each place) is owed by name. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.K01FiftyAtBase
import Johnson.Desc.K1.Law.TestsAtCounts
import Johnson.Desc.K1.Law.ArmHeadJ
import Johnson.Desc.K1.Law.ArmAttEntry
import Johnson.Desc.AtSeats.SortAtOpen
import Johnson.Desc.K1.Law.ReadersHeadReads
import Johnson.Desc.K1.Law.WtBackAtReads
import Johnson.Desc.K1.Law.ToldAtD

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ Stated smpNamed widen TiedAtR HandsOn doorsFitB MgData mgAll d13)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt readsOf uHeadK6 K6Name)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt OldKept plus13 cA13 FactsK13)
open VerifiableInference.Desc.K12.Door (K12Data toTree)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open k1Ix k1Reads k1Quiet)
open VerifiableInference.Desc.First.Att.P (uArm plannedK)
open OnBytes.Road.K4 (uLay)
open VerifiableInference.Desc.K9 (readersOfLink holesAt)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6 ColFour CallsSeated lab_of_calls)
open VerifiableInference.Desc.First.Look (sigListCalls)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Model.Verify (borderOf publicOf layerShape)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- The two facts on reached states that the payers want inside the wider promise, as one Bool. -/
noncomputable def xbK (G₀ : ProofFile.Ground) (J : S → Prop) : S → Bool := fun s =>
  @decide (TablesOk G₀.W.hS G₀.W.HLy G₀.W.H s ∧ ArmOk J s) (Classical.propDecidable _)

theorem xbK_iff (G₀ : ProofFile.Ground) (J : S → Prop) (s : S) :
    xbK G₀ J s = true ↔ TablesOk G₀.W.hS G₀.W.HLy G₀.W.H s ∧ ArmOk J s := by
  unfold xbK
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- **THE FIFTY, WITH THE PAYERS CALLED.** -/
theorem k01_fifty_paid {P : VerifierAndGoals.PublicFiles}
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
    (J : S → Prop)
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (seats : List (ℕ × ℕ))
    (c₀ : CellsQ rows cols)
    (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl}
    {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S)
      (Wit (CellsQ rows cols) Tok MsgT) ds}
    {r : Fmt.RoundView}
    (hc : Bs.G₀.first.codes = codesFull2)
    (hs : Bs.G₀.first.shape = shapeFull)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, (rest₁ (noL l d) [d₁, d₂]).err =
      Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hBlind : K13.Law.DecBlind Dm.decT)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z Bs.G₀ l d X arrs) x x' → Dm.H.req x' = Dm.H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr (headLink XV) p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Dm.headPart p i x' y' w → Dm.headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Dm.digitsPart m x' y' w → Dm.digitsPart m x y w)
    (Wp : OnBytes.Model.Verify.Public)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm) → Dm.wt 24 a' y' w → Dm.wt 24 a y w)
    (hheard : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull (flatPlacesOf linksFull true) (noL 24 true) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H)
    (hPlanR : ∀ l, l < 25 → ∀ d : Bool, PlanRest Dm.pubD.cs Dm.G Dm.ms (parL Z Bs.G₀ l d)
      (radRec (recL l d) (parL Z Bs.G₀ l d)) (baseL aN R₁ R₂ R₃ c l d) (Dm.N.sent l (momL d)))
    (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) dep 0 b₁ l₁ (dataOf aN R₁ R₂ R₃).ds₁ [r])
    (hDsh : Dm.shape = shapeFull)
    (hDlk : Dm.links = linksFull)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, Rch j a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
        FactsK13 (d13 Dm) dk (mgAll Dm mgBase) a.1 ∧
        (∀ L, a.1.2.link? = some L → L.check.frame.group = Dm.N.groupAt l ∧ L.check.frame.shape = (d13 Dm).shape) ∧
        (xbK Bs.G₀ J) a.1.2 = true)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) i)))
    (hsmp : Dm.smp = smpNamed Dm.cs seats)
    (hft : dk.ft = (gpOf Z).firstTree)
    -- WHAT THE PAYERS LEAVE
    {s : ReqShape} {links : List ModelPart}
    (hN : Dm.N = P5T.N0Full.atBlocks s links c.blocksInOrder)
    (hseats : seats = K13.Law.seatsFull)
    (hCnt : K13.Law.CountsAre (First.toldOf c.blocksInOrder))
    (hLk : dk.L = K13.Law.LFull) (hMk : dk.M = K13.Law.MFull)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hJt : ∀ s, J s → TlIsPlan XV s)
    (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout)
    (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hWn : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w))
    (hUH : Dm.uH = uHeadK6 XV)
    (hWX : Bs.G₀.W = XV)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hKw : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (msR : List Mem) (lay6 : OnBytes.Params.ReqLayout) (num6 : ℕ → ℕ → ℕ) (rad6 : OnBytes.OracleShape → ℕ)
    (seatT : Fin (sigListCalls Dm.sent rad6 24).length → ℕ × ℕ)
    (hLaid6 : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hCalls : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num6 Dm.sent rad6
      24 seatT)
    (hJH : ∀ s, J s → JH XV (Dm.N.sent 24 0) Dm.arr Dm.N num6 lay6 s)
    (hsub : ∀ x ∈ Dm.N.sent 24 0, x ∈ Dm.N.group 24)
    (hPl' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w))
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24))
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?)
    (eD : (dataOf aN R₁ R₂ R₃).ds₁ =
      (dataOf aN dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).ds₁)
    (eG : ∀ j, Dm.G.oracleAt j = F.oracleAt j)
    (ht : 83 ≤ Three.rootsIn dryProofFull.1)
    (hT83 : nTrees (dataOf aN dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).ds₁ ≤ 83)
    (h4 : ∀ l, l < 25 → ∀ d : Bool, ∀ n, n < (layOf (parL Z Bs.G₀ l d)).shapes.size →
      HashBuild.laidFull[nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d))) + n]? =
        some (((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).logN,
          ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).mainWidth +
            ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).maskWidth))
    (hidle : ∀ l, l ≠ 24 → ∀ a y w, Dm.wt l a y w)
    (hheard2 : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) linksFull (flatPlacesOf linksFull true) (noL 24 false) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H)
    (hquiet : ∀ X, Bs.G₀.built[24]? = some X → ∃ P, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head P) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ q, (T.p₁ :: T.l₁)[14 * l + k1Ix l d + 2]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (14 * l + k1Ix l d + 2)
        (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) (14 * l + k1Ix l d + 2))) :=
  k01_fifty_atBase Dm dk (xbK Bs.G₀ J) hS hR O hT seats c₀ tokOf hc hs hC hWr hCap hOk hRoots (hRows_at hN) (hBook_at hS hR O hN) (hFence_at hS hR O hN hCnt) (hSent_at hS hR O (fun b hb => (hOk b hb).1) hc hs hN hCnt) hBlind (hNd_at hseats) (hSeats_at hS hR O hc hs hWr hOk hRoots hN hCnt hseats)
    (hRd_any Dm Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) hS hR O hDlk hlk (hWX ▸ headLink_open hS hR O)
      (by subst hWX; exact ⟨rfl, rfl, rfl⟩)
     
    (fun l hl d => runsFit_mw1 Dm dk mgBase rfl l hl d)
      (fun _ _ hIn => ((xbK_iff _ _ _).1 (inAt_drop hIn).2).1)) hreq hhead hdig Wp hmono hheard (hAtA_at Dm hS hR O hc hs hDsh hN hCnt) hPlanR
    (hTold_atD Dm.G hS hR O hOk hWr hRoots eD eG ht hT83 h4) dep hFit hDsh hDlk (hP1_at hS hR O hc hs hN hCnt)
    (fun l hl X arrs hX x x' y y' w hy hIn hK ht =>
      arm_at_reads_three Dm dk J hS hR O hDlk aN R₁ R₂ R₃ hLay hUA
        (hAtt_of2 Dm dk J hS hR O hWX hJt shp lay₀ hJl aN R₁ R₂ R₃ hWn hSec hAtt'') hUH hWX
        (hK6_ofJ Dm dk J num6 lay6 hJH hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hKw msR rad6 seatT hLaid6 hCalls hsub)
        (hPl_of3 Dm dk J (fun s h => (hJH s h).1) hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hKw hPl')
        hElse l hl X arrs hX x x' y y' w hy
        (inAt_drop hIn).1 ((xbK_iff _ _ _).1 (inAt_drop hIn).2).2 hK ht)
    (hwtR_of Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) (xbK Bs.G₀ J)) Dm.wt Wp hidle hmono hheard2 hquiet) Rch
    (fun l _ d X arrs _ x x' hy h => by
      obtain ⟨_, rs, gs, _, hd⟩ := id hy
      exact (xbK_iff _ _ _).2 ⟨tablesOk_later Z Bs.G₀ l d X arrs _ _ _ _ hd ((xbK_iff _ _ _).1 h).1,
        armOk_later J Z Bs.G₀ l d X arrs x x' hy⟩) hFacts hHand hsmp (hidx_at hS hR O hN hCnt hseats) hft (hPlan3_at hS hR O hc hs hN hCnt hLk hMk) (hWX ▸ sortB_ground hS hR O)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_fifty_paid
