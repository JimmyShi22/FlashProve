-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01FiftyAtBase.lean: K01_law's FIFTY LATER PLACES, IN THE SECOND FORM, AT mgAll Dm mgBase (the composed meaning over the base meaning mgBase, Johnson/Desc/Sound/MgBase.lean): k01_fifty_at9 AT Mg₀ := mgBase: THREE PREMISES FALL BY THE BASE's OWN MAKE: hM (its door is empty: rfl) · hSaid (its pubP IS
«the table says "no sentence is meant"»: First.saysNone, Johnson/Desc/First/AllSaid.lean) · hio9 ("in order" reads the public part alone: the written request can be read back). AND hfB IS bookFitsB_iff (Johnson/Desc/Sound/BookTestsLaw.lean). hh AND hK5 FALL WHOLE (heardNone_at_reads, Johnson/Desc/K1/Law/HeardAtReads.lean: from the top's own binder O · k5_at_later, Johnson/Desc/K1/Law/K5AtLater.lean: no premise). THE STATEMENT IS MADE BY PROGRAM.
What is not claimed. No premise is shown; NO EXAMPLE. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.K01FiftyAt9
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.K1.Law.HeardAtReads
import Johnson.Desc.K1.Law.K5AtLater

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

/-- **THE FIFTY, AT THE COMPOSED MEANING OVER THE BASE.** -/
theorem k01_fifty_atBase {P : VerifierAndGoals.PublicFiles}
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
    (hRows : First.eachOnce ((List.range 26).map fun m => (Dm.N.groupAt m, 0)) = true)
    (hBook : First.bookFit Dm.N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true)
    (hFence : First.fenceFit Dm.N linksFull (flatPlacesOf linksFull true) = true)
    (hSent : ∀ l, l < 25 → ∀ d : Bool, sentAtB Dm.N (toldBy c.blocksInOrder) (noL l d) l (momL d) = true)
    (hBlind : K13.Law.DecBlind Dm.decT)
    (hNd : seats.Nodup)
    (hSeats : ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? = some (seatOfMsg (parL Z Bs.G₀ l d) (baseL aN R₁ R₂ R₃ c l d) j.val))
    (hRd : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z Bs.G₀ l d X arrs) x x' → Dm.H.req x' = Dm.H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr (headLink XV) p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Dm.headPart p i x' y' w → Dm.headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Dm.digitsPart m x' y' w → Dm.digitsPart m x y w)
    (Wp : OnBytes.Model.Verify.Public)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm) → Dm.wt 24 a' y' w → Dm.wt 24 a y w)
    (hheard : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL 24 true) x y →
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
    (hDsh : Dm.shape = shapeFull)
    (hDlk : Dm.links = linksFull)
    (hP1 : ∀ l, l < 25 → laterSeatsB Dm.N (parL Z Bs.G₀ l false) l 1
      (Dm.N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true)
    (hArm : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w)
        (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l))
    (hwtR : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → Dm.wt l x' y' w → Dm.wt l x y w)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hxb : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' : ProofFile.InstPub × S,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' → xb x.2 = true → xb x'.2 = true)
    (hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, Rch j a → onQ Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
        FactsK13 (d13 Dm) dk (mgAll Dm mgBase) a.1 ∧
        (∀ L, a.1.2.link? = some L → L.check.frame.group = Dm.N.groupAt l ∧ L.check.frame.shape = (d13 Dm).shape) ∧
        xb a.1.2 = true)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) i)))
    (hsmp : Dm.smp = smpNamed Dm.cs seats)
    (hidx : ∀ l, l < 25 → ∀ d : Bool,
      ∀ u ∈ First.sampledIn Dm.N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
        seats.idxOf u < Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)
    (hft : dk.ft = (gpOf Z).firstTree)
    (hPlan3 : planThreeB dk Dm.N Z Bs.G₀ = true)
    (hSortB : sortB XV = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ q, (T.p₁ :: T.l₁)[14 * l + k1Ix l d + 2]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (14 * l + k1Ix l d + 2)
        (q.withMap ((fun k => extQAt Dm.pubD.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) (14 * l + k1Ix l d + 2))) :=
  k01_fifty_at9 Dm dk mgBase xb hS hR O hT seats c₀ tokOf (fun _ _ h => h) hc hs hC hWr hCap hOk hRoots hRows
    hBook hFence hSent hBlind hNd hSeats hRd hreq hhead hdig Wp hmono hheard hAtA hPlanR hTold dep
    hFit hDsh hDlk hP1 hArm hwtR Rch hxb hFacts hHand rfl hsmp Sound.bookFitsB_iff hidx (fun z =>
    (_root_.Meaning.backReq (Dm.reqB z)).isSome) (fun _ => Bool.true_and _) hft hPlan3 hSortB (fun l
    hl X arrs hX x x' y hy hIn => heardNone_at_reads Dm dk O l hl X arrs hX x x' y hy (inAt_drop
    hIn).1) (fun l hl d X arrs hX x x' y q hy hIn hk hp => k5_at_later Dm dk Z Bs l hl d X arrs hX x
    x' y q hy (inAt_drop hIn).1 hk hp)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_fifty_atBase
