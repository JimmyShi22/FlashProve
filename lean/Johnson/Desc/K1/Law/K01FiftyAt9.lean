-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01FiftyAt9.lean: K01_law's FIFTY LATER PLACES, IN THE SECOND FORM OF THE CHAIN OF PROMISES, AT THE COMPOSED MEANING ITSELF: TiedAtR Dm.N (mgAll Dm Mg₀) …, GENERAL IN Dm · dk · Mg₀: k01_fiftyR (Johnson/Desc/K1/Law/K01FiftyR.lean) CALLED AT Dm's OWN LETTERS, WITH THE
PAYERS CALLED HERE BY NAME. THE STATEMENT IS MADE BY PROGRAM OUT OF k01_fiftyR's OWN BINDERS (each letter ↦ Dm's).
PAID HERE: hL (laidK1_mw1: LaidK1's ten fields; left: hsmp · hfB) · hB (boolsK1_mw1; left: hidx) · hIoIs (left: hio9: the composed meaning's "in order" reads the public part alone) · AND BY OTHER FILES OF THIS FOLDER (DoorFactsAtPlus13.lean · WoAtLater.lean · RestPointPlan.lean · SaidAtFifty.lean among them; under hM : Mg₀.more = {}):
hled · hnl · hkIn · hsIn · hD (the kernel at the closed door) · aWo (aWo_plus13) · hrest (hrest_point_plan: POINTWISE: hh · hK5 STAND HERE INSIDE mw1's PROMISE; beside them: hft · hPlan3 (one Bool: planThreeB); hSort ⟸ hSort_of under the Bool sortB XV) · hBase (baseP_plus13: the kernel at the closed door; left: hSaid: «where the table First.saysNone (Johnson/Desc/First/AllSaid.lean) says "no sentence is meant", the base meaning's pubP holds»: at mgBase by its make).
hpub (hpub_point: POINTWISE: its hshape off the promise [hshape_at], its hRd off the top's own hRd; left: the Bool hP1 and two equations on Dm's letters: hDsh · hDlk [hOwn1_scope · hAt_scope]).
aPile (aPile_plus13: under hM · hfB alone) · hmeet (hmeet_plus13; its hshape off the promise; left: the Bool hAtA : aheadAtB …).
hwt (hwt_whole, WtAt24.lean, over other files' legs: an item forms … "weights" is open in front of ONE of the fifty alone, (24, true) [kernel]; left: hmono · hheard).
hback (hback_sorts over hback_point: THE EXCHANGE AT THE 25 READS' PLACES, POINTWISE: its ReadersStay off the top's own hRd [formsInT_of_ins]; «pin l 0» and «constr l small» by the top's own arms; left: hArm (ArmCellIn at each run, AT THE ARM OF LINK l's OWN SORT, BEHIND «tie l» AT THIS w [the row opens it: tieOut_full]: the three sorts' halves) · hwtR (wt back over a reads' place)).
xb: A LETTER: ONE MORE TEST ON THE STATE INSIDE THE WIDER "in order" (liveX): it must ride over the fifty (hxb) and hold at reached states at the two borders of each place (hFacts' third clause): every binder that stands inside mw1's promise has it in hand (inAt_drop). MEANT: «where the output head's tables are laid, they are the reads' quiet step's own» (TablesOk, TablesOk.lean): without it the readers' law at (24, reads) may have no member.
What is not claimed. No premise is shown; NO EXAMPLE. Nothing at link 0's first place and at W's. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LaidMw1
import Johnson.Desc.K1.Law.DoorFactsAtPlus13
import Johnson.Desc.K1.Law.WoAtLater
import Johnson.Desc.K1.Law.SaidAtFifty
import Johnson.Desc.K1.Law.SortAtFifty
import Johnson.Desc.K1.Law.PlanThree
import Johnson.Desc.K1.Law.HpubMw1
import Johnson.Desc.K1.Law.AheadAtDigits
import Johnson.Desc.K1.Law.PileAtPlus13
import Johnson.Desc.K1.Law.WtAt24
import Johnson.Desc.K1.Law.RestPointPlan
import Johnson.Desc.K1.Law.TestsInScope
import Johnson.Desc.K1.Law.HbackMw1
import Johnson.Desc.K1.Law.ArmBySort

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
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt readsOf)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt OldKept plus13 cA13 FactsK13)
open VerifiableInference.Desc.K12.Door (K12Data toTree)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open k1Ix k1Reads)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- What "in order" says beside inOrderK13 at the wider meaning. -/
noncomputable abbrev io9 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (xb : S → Bool) : ProofFile.InstPub × S → Bool :=
  fun a => (mgAll Dm Mg₀).inOrder a && liveX Dm.N Dm.shape xb a.2

/-- The meaning beneath the lookups' part. -/
noncomputable abbrev mgP9 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT)) :
    Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT) :=
  First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀

/-- **THE FIFTY, AT THE COMPOSED MEANING.** -/
theorem k01_fifty_at9 {P : VerifierAndGoals.PublicFiles}
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
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (xb : S → Bool)
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
    (hSaid : ∀ q a, (First.saysNone q).isSome = true → Mg₀.pubP q a)
    (hc : Bs.G₀.first.codes = codesFull2)
    (hs : Bs.G₀.first.shape = shapeFull)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, (rest₁ (noL l d) [d₁, d₂]).err =
      Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hRows : First.eachOnce ((List.range 26).map fun m => (Dm.N.groupAt m, 0)) = true)
    (hBook : First.bookFit Dm.N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true)
    (hFence : First.fenceFit Dm.N linksFull (flatPlacesOf linksFull true) = true)
    (hSent : ∀ l, l < 25 → ∀ d : Bool, sentAtB Dm.N (toldBy c.blocksInOrder) (noL l d) l (momL d) = true)
    (hBlind : K13.Law.DecBlind Dm.decT)

    (hNd : seats.Nodup)
    (hSeats : ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? = some (seatOfMsg (parL Z Bs.G₀ l d) (baseL aN R₁ R₂ R₃ c l d) j.val))
    (hRd : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z Bs.G₀ l d X arrs) x x' → Dm.H.req x' = Dm.H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr (headLink XV) p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Dm.headPart p i x' y' w → Dm.headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Dm.digitsPart m x' y' w → Dm.digitsPart m x y w)
    (Wp : OnBytes.Model.Verify.Public)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm) → Dm.wt 24 a' y' w → Dm.wt 24 a y w)
    (hheard : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL 24 true) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H)
    (hAtA : ∀ l, l < 25 → aheadAtB Dm.shape (Dm.N.sent l) (parL Z Bs.G₀ l true) l
      (Dm.pubD.dS1.own l).size (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true)
    (hPlanR : ∀ l, l < 25 → ∀ d : Bool, PlanRest Dm.pubD.cs Dm.G Dm.ms (parL Z Bs.G₀ l d)
      (radRec (recL l d) (parL Z Bs.G₀ l d)) (baseL aN R₁ R₂ R₃ c l d) (Dm.N.sent l (momL d)))
    (hTold : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, Dm.G.oracleAt (baseL aN R₁ R₂ R₃ c l d + n) = some o →
        o.logLength = sh.a ∧ o.words = sh.W)
    (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) dep 0 b₁ l₁ (dataOf aN R₁ R₂ R₃).ds₁ [r])
    (hDsh : Dm.shape = shapeFull) (hDlk : Dm.links = linksFull)
    (hP1 : ∀ l, l < 25 → laterSeatsB Dm.N (parL Z Bs.G₀ l false) l 1
      (Dm.N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true)
    (hArm : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w)
        (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l))
    (hwtR : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → Dm.wt l x' y' w → Dm.wt l x y w)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hxb : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' : ProofFile.InstPub × S,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' → xb x.2 = true → xb x'.2 = true)
    (hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, Rch j a → onQ Dm.N (mgAll Dm Mg₀) linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
        FactsK13 (d13 Dm) dk (mgAll Dm Mg₀) a.1 ∧
        (∀ L, a.1.2.link? = some L → L.check.frame.group = Dm.N.groupAt l ∧ L.check.frame.shape = (d13 Dm).shape) ∧
        xb a.1.2 = true)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) i)))
    -- WHAT THE PAYERS LEAVE
    (hM : Mg₀.more = {}) (hsmp : Dm.smp = smpNamed Dm.cs seats)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hidx : ∀ l, l < 25 → ∀ d : Bool,
      ∀ u ∈ First.sampledIn Dm.N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
        seats.idxOf u < Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)
    (ioP : ProofFile.InstPub → Bool) (hio9 : ∀ a, (mgAll Dm Mg₀).inOrder a = ioP a.1)
    (hft : dk.ft = (gpOf Z).firstTree)
    (hPlan3 : planThreeB dk Dm.N Z Bs.G₀ = true)
    (hSortB : sortB XV = true)
    (hh : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l false) x y → HeardNone x'.2)
    (hK5 : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → k5At l q = true →
      (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb).pub q x = true → (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb).pub q x' = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ q, (T.p₁ :: T.l₁)[14 * l + k1Ix l d + 2]? = some q →
      TiedAtR Dm.N (mgAll Dm Mg₀) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (14 * l + k1Ix l d + 2)
        (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) (14 * l + k1Ix l d + 2))) :=
  k01_fiftyR hS hR O hT Dm.N (mgAll Dm Mg₀) (d13 Dm) dk xb Dm.pubD Dm.G Dm.arr Dm.smp Dm.ms Dm.decT Dm.shape
    Dm.layout (io9 Dm Mg₀ xb) (plus13 (d13 Dm) dk Mg₀).pub XV Dm.sent (mgP9 Dm Mg₀) Mg₀ seats Dm.St
    Dm.after Dm.wt Dm.rw (headLink XV) Dm.put Dm.H Dm.headPart Dm.digitsPart (.more none
    "K12.bookFits") Sound.bookFitsB c₀ tokOf (laidK1_mw1 Dm dk Mg₀ seats hsmp hfB xb) (boolsK1_mw1 Dm dk Mg₀ hM seats Z Bs.G₀ hidx xb) ⟨baseP_plus13 Dm dk Mg₀ hM hSaid⟩ hc hs hC hWr hCap hOk hRoots hRows hBook hFence hSent hBlind
    ioP (fun a => by show ((mgAll Dm Mg₀).inOrder a && liveX Dm.N Dm.shape xb a.2) = _; rw [hio9 a]) hxb (fun (l
    : ℕ) (_ : Bool) => l) (hled_plus13 Dm dk Mg₀ hM) (hnl_plus13 Dm dk Mg₀ hM) (fun l hl d X arrs hX x x' y y' w hy hIn hK hw =>
      aPile_plus13 Dm dk Mg₀ hM Z Bs hfB _ l hl d X arrs hX x x' y y' w hy (inAt_down _ _ _ _ _ _ _ _ _ hIn) hK hw) (fun l hl d X arrs hX x x' y y' w m hy hIn
    hK hi hw =>
          aWo_plus13 Dm dk Mg₀ hM Z Bs hfB _ l hl d X arrs hX x x' y y' w m hy (inAt_down _ _ _ _ _
    _ _ _ _ hIn) hK hi hw) hNd hSeats hRd (fun l hl d X arrs hX x x' y q hy hIn hq hq' h7 =>
      hrest_point_plan Dm dk Mg₀ hM Z Bs hfB hft hPlan3 hSortB l hl d X arrs hX x x' y q hy
        (inAt_down _ _ _ _ _ _ _ _ _ hIn)
        (by cases d with
          | true => exact trivial
          | false => exact hh l hl X arrs hX x x' y hy hIn)
        (hK5 l hl d X arrs hX x x' y q hy hIn) hq hq' h7) hreq hhead hdig  (hwt_whole Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) Dm.wt Wp hmono hheard) (fun l hl d X arrs hX x x' y m j r hy hIn hf p hp hah =>
      hmeet_plus13 Dm dk Mg₀ hM Z Bs hAtA l hl d X arrs hX x x' y m j r hy (inAt_down _ _ _ _ _ _ _ _ _ hIn)
        (hshape_at (laidK1_mw1 Dm dk Mg₀ seats hsmp hfB xb) _ _ _ x.1 x.2 y hIn) hf p hp hah) hPlanR hTold dep hFit (fun l hl d d₁ d₂ _ _ _ X arrs hX c' hu z a τ x ha hm hx q hq => by
      cases d with
      | true => exact absurd hq (tiedL_true_none Dm dk Mg₀ hM l hl q)
      | false =>
        exact hpub_point Dm dk Mg₀ hM Z Bs (hOwn1_scope Dm hDsh hDlk Z Bs.G₀ hs) hP1 (hAt_scope Dm hDsh Z Bs.G₀ hs) l hl false _ d₁ d₂ _ _ X arrs hX c' hu z a τ x
          (inAt_down _ _ _ _ _ _ _ _ _ ⟨ha, hm⟩).1 hm hx
          (hshape_at (laidK1_mw1 Dm dk Mg₀ seats hsmp hfB xb) _ _ _ z a.1 _ ⟨ha, hm⟩)
          (fun j r ho => hRd l hl false X arrs hX (z, a.1) (z, x.1) _ l j r
            (yesOf_of_piece _ c' hu _ d₁ d₂ _ _ z a τ x hx) ⟨ha, hm⟩
            (Or.inr (List.mem_append_right _ ho))) q hq) (fun l hl d e d₁ d₂ _ _ _ X arrs hX c' hu z a τ x w ha hm hx hPin hCon hout => by
      subst e
      have hy := yesOf_of_piece (W := Wit (CellsQ rows cols) Tok MsgT) (blkL Z Bs.G₀ l false X arrs) c' hu _ d₁ d₂ _ _ z a τ x hx
      exact hback_sorts Dm dk Mg₀ hM hDlk Z Bs l hl _ d₁ d₂ _ _ X arrs hX c' hu z a τ x w
        (inAt_down _ _ _ _ _ _ _ _ _ ⟨ha, hm⟩).1 hm hx
        (fun j n hi => hRd l hl false X arrs hX (z, a.1) (z, x.1) _ l j n hy ⟨ha, hm⟩
          (Or.inr (List.mem_append_right _ (formsInT_of_ins l hl j n hi))))
        (fun j n hi p hp A B hA hB => hArm l hl X arrs hX (z, a.1) (z, x.1) _ _ w hy ⟨ha, hm⟩ (keptBelow_out _ hx)
          (hout (.tie l) (List.mem_append_left _ (List.mem_append_left _ (tieOut_full l hl)))) j n hi p hp A B hA hB)
        (hwtR l hl X arrs hX (z, a.1) (z, x.1) _ _ w hy ⟨ha, hm⟩ (keptBelow_out _ hx))
        hPin hCon hout) Rch (hD_plus13
    Dm dk Mg₀ hM) hFacts hHand

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_fifty_at9
