-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01LawWhole.lean: K01_law, ALL 52 PLACES DOWN TO NAMED PREMISES: the top k01_law (Johnson/Desc/K1/Law/K01Law.lean) with its two binders H0 | HW (the whole ties at link 0's first place, flat number 2, and at W's place, 356) DISCHARGED BY NAME:
H0_of | HW_of (Johnson/Desc/K1/Law/H0Of.lean · HWOf.lean: over first_tied_seat | w_tied_seat, letters_at_flat, tiedAt_err, sendErr_le_cap_port, extQAt_two | extQAt_w). THE STATEMENT IS MADE BY PROGRAM OUT OF THE THREE STATEMENTS' OWN BINDERS:
a binder of H0_of bears the mark 0, one of HW_of the mark W. hCap IS ONE BINDER FOR ALL 52: «the maker's rest's error bounds at a stretch of two rounds are the cap». At link 0's first place the radii are the written list's (radRec 0) and
condPort · one seed · powB 128 are PAID (PaidAt, Johnson/Desc/K1/Law/RoundsLit.lean: k01_paid_first_chain, Johnson/Desc/K1/Law/Paid.lean, under hc · hs).
What is not claimed. No premise is shown. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.K01Law
import Johnson.Desc.K1.Law.H0Of

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ Stated smpNamed)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (openAt OldKept RowG FillG RowM4 FillM4 wSitsItem wSitsB planSitsB
  planSeatB)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open Johnson.Desc.First.Walk (LayPar)
open ProofFile (Cl)
open IM (Open k1Ix k1Reads)

/-- **K01_law, ALL 52 PLACES.** -/
theorem k01_law_whole {P : VerifierAndGoals.PublicFiles}
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
    {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {XV : Model.Verify.Public}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hT : OfDesc _ T)
    (N : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (Dp : First.PubData)
    (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf Dp.cs s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option (CellsQ rows cols))
    (shape : Params.ReqShape)
    (layout : Params.ReqLayout)
    (io0 : ProofFile.InstPub × S → Bool)
    (base : Pub → ProofFile.InstPub × S → Bool)
    (X3 : OnBytes.Model.Verify.Public)
    (D3 : First.Look.Sent)
    (MgP Mg0 : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (seats : List (ℕ × ℕ))
    (St : Stated)
    (after : ℕ → S → Except String S)
    (wt : ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (rwB : ℕ → S → Bool)
    (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt XV ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT) rows cols)
    (headPart : P5J.TPart → Sound.IdxQ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (digitsPart : ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (fI : Pub)
    (fB : TreeBook → Bool)
    (c₀ : CellsQ rows cols)
    (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl}
    {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S)
      (Wit (CellsQ rows cols) Tok MsgT) ds}
    {r : Fmt.RoundView}
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 base X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (hB : BoolsK1 N Dp seats Z Bs.G₀ Mg.more fI)
    (hBase : BaseK1 Mg.more MgP)
    (hc : Bs.G₀.first.codes = codesFull2)
    (hs : Bs.G₀.first.shape = shapeFull)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ (k : ℕ) (d₁ d₂ : RDT), (rest₁ k [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hRows : First.eachOnce ((List.range 26).map fun m => (N.groupAt m, 0)) = true)
    (hBook : First.bookFit N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true)
    (hFence : First.fenceFit N linksFull (flatPlacesOf linksFull true) = true)
    (hSent : ∀ l, l < 25 → ∀ d : Bool, sentAtB N (toldBy c.blocksInOrder) (noL l d) l (momL d) = true)
    (hBlind : K13.Law.DecBlind decT)
    (ioP : ProofFile.InstPub → Bool)
    (xb : S → Bool) (hIoIs : ∀ a, io0 a = (ioP a.1 && liveX N shape xb a.2))
    (hxb : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' : ProofFile.InstPub × S,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' → xb x.2 = true → xb x'.2 = true)
    (mLed : ℕ → Bool → ℕ)
    (hled : ∀ l, l < 25 → ∀ d : Bool, Pub.ledger (mLed l d) ∈
      (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (hnl : ∀ l, l < 25 → ∀ d : Bool, ∀ m, Pub.left m ∉
      (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (aPile : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w, YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' → Mg.pile x' y' w → Mg.pile x y w)
    (aWo : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.wo m ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → Mg.wo m x' y' w → Mg.wo m x y w)
    (hNd : seats.Nodup)
    (hSeats : ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? = some (seatOfMsg (parL Z Bs.G₀ l d) (baseL aN R₁ R₂ R₃ c l d) j.val))
    (hRd : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dp D3) m j r x.2 x'.2)
    (hrest : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) → q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → Mg.pub q x' = true)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z Bs.G₀ l d X arrs) x x' → H.req x' = H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr hd p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → headPart p i x' y' w → headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → digitsPart m x' y' w → digitsPart m x y w)
    (hwt : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m j, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → wt m x' y' w → wt m x y w)
    (hmeet : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      Item.forms m j r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → ∀ p ∈ Dp.runs m j r, Dp.ah p.1 p.2 = true →
      AheadMeets (N.sent m) (N.group m) (idsOf (parL Z Bs.G₀ l d) x.2.st.oracles.size).toList x.2 x'.2)
    (hPlanR : ∀ l, l < 25 → ∀ d : Bool, PlanRest Dp.cs G ms (parL Z Bs.G₀ l d)
      (radRec (recL l d) (parL Z Bs.G₀ l d)) (baseL aN R₁ R₂ R₃ c l d) (N.sent l (momL d)))
    (hTold : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, G.oracleAt (baseL aN R₁ R₂ R₃ c l d + n) = some o →
        o.logLength = sh.a ∧ o.words = sh.W)
    (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) dep 0 b₁ l₁ (dataOf aN R₁ R₂ R₃).ds₁ [r])
    (hpub : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (c' : Block S Cl),
      c'.UnderR ((blkL Z Bs.G₀ l d X arrs).retype : Block S Cl) → ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (baseL aN R₁ R₂ R₃ c l d) d₁ d₂ (parL Z Bs.G₀ l d).coordinates (errPort (parL Z Bs.G₀ l d) (radRec (recL l d) (parL Z Bs.G₀ l d)))).ior.red.out a τ = some x → ∀ q ∈ tiedL Mg.more l d, Mg.pub q (z, x.1) = true)
    (hback : ∀ l, l < 25 → ∀ d : Bool, d = false → ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (c' : Block S Cl),
      c'.UnderR ((blkL Z Bs.G₀ l d X arrs).retype : Block S Cl) → ∀ (z : ProofFile.InstPub) a τ x w,
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (baseL aN R₁ R₂ R₃ c l d) d₁ d₂ (parL Z Bs.G₀ l d).coordinates (errPort (parL Z Bs.G₀ l d) (radRec (recL l d) (parL Z Bs.G₀ l d)))).ior.red.out a τ = some x →
      ((Item.pin l 0).holds N Mg (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) w →
        (Item.pin l 0).holds N Mg (z, a.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) a.2) w) →
      (Mg.constr l .small (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) w →
        Mg.constr l .small (z, a.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) a.2) w) →
      relAt (meansQ N Mg fun s : S => (z, s)) (outsQ linksFull (flatPlacesOf linksFull true) (noL l d)) x w →
      relAt (meansQ N Mg fun s : S => (z, s)) (insQ linksFull (flatPlacesOf linksFull true) (noL l d)) a w)
    -- AT LINK 0's FIRST PLACE
    (hU : ∃ (e : Block S Cl) (nm : String) (X0 : LayPar), c.blocksInOrder[2]? = some e ∧
      Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X0 ∧
      e.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X0
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl))
    (X0 : LayPar)
    (hX0 : Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X0)
    (mk0 : List Pub)
    (hRow0 : RowG N Mg.more Sound.linksFull psF 2 (layOf (firstPar Bs.G₀.first (gpOf Z))).shapes.size
      (firstPar Bs.G₀.first (gpOf Z)).sent.size mk0)
    (hF0 : ∀ nm : String, FillG Cl Bs.G₀.first (gpOf Z) nm X0
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol N Mg
      ((First.pubSets Mg.more Sound.linksFull psF)[2]?.getD []) psF[2]? mk0)
    (hgroups0 : ∀ x, Mg.pub .noneSent x = true → N.groupAt 0 = x.2.st.groups.size)
    (hown0 : ∀ x, Mg.inOrder x = true → First.bookAt N psF[2]? x.2 = true →
      ownSeatsB N (openAt Sound.linksFull psF (2 + 1)) (firstPar Bs.G₀.first (gpOf Z))
        (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true)
    (hNew0 : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val)).Str),
      ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X0
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol) →
      (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.red.out a τ = some x →
      (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j →
        Sealed (firstPar Bs.G₀.first (gpOf Z)).codes
          (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val)) →
      ∀ t ∈ First.sampledIn N (openAt Sound.linksFull psF (2 + 1)),
        Mg.held t.1 t.2 (z, x.1) = true ∧
          Mg.shown t.1 t.2
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) ∧
          Mg.noColl t.1 t.2 (z, x.1)
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    -- AT W's PLACE
    (msgW : Array OracleNotice)
    (hmW : linMessageW Z.first.lin = some msgW)
    (radW : ℕ → ℕ)
    (hCondW : condPort (parWZ Z msgW) radW = true)
    (h1W : (parWZ Z msgW).seeds = 1)
    (hpowW : powB (parWZ Z msgW) radW 128 = true)
    (hRowW : RowM4 N Mg.more Sound.linksFull psF 356 (layOf (parWZ Z msgW)).shapes.size
      (parWZ Z msgW).sent.size)
    (hFW : FillM4 Cl (whereOf Z) (parWZ Z msgW) N Mg
      ((First.pubSets Mg.more Sound.linksFull psF)[356]?.getD []) psF[356]?)
    (hPlW : wSitsItem ∈ (First.pubSets Mg.more Sound.linksFull psF)[356 + 1]?.getD [] →
      planSitsB (whereOf Z) (parWZ Z msgW) = true ∧ planSeatB N psF[356]? (parWZ Z msgW) = true)
    (hbaseW : N.index.1 < nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
    (hNewW : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val)).Str),
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      (∀ j, sampledAt (parWZ Z msgW) j →
        Sealed (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length + j.val)) →
      (wSitsItem ∈ (First.pubSets Mg.more Sound.linksFull psF)[356 + 1]?.getD [] →
        wSitsB (parWZ Z msgW).codes (whereOf Z) x.1 = true ∧
          x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length]? = some N.w) →
      Mg.held N.w.1 N.w.2 (z, x.1) = true ∧
        Mg.noColl N.w.1 N.w.2 (z, x.1)
          (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    (hshownW : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      Mg.shown N.w.1 N.w.2
        (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2)) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) (fun k => extQAt Dp.cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k)
      (T.p₁ :: T.l₁) KindName.K1 := by
  have hp0 : PaidAt (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) :=
    paid_radRec (k01_paid_first_chain Bs.G₀.first (gpOf Z) hc hs).1
  exact k01_law hS hR O hT N Mg Dp G arr smp ms decT shape layout io0 base X3 D3 MgP Mg0 seats St after wt rwB
    hd put H headPart digitsPart fI fB c₀ tokOf hL hB hBase hc hs hC hWr (fun l _ d => hCap (noL l
    d)) hOk hRoots hRows hBook hFence hSent hBlind ioP xb hIoIs hxb mLed hled hnl aPile aWo
    hNd hSeats hRd hrest hreq hhead hdig  hwt hmeet hPlanR hTold dep hFit hpub hback (H0_of hS hR O hT N Mg
    Dp.cs G arr smp ms decT c₀ tokOf hC hWr hU (hCap 2) X0 hX0 mk0 _ hp0.1 hp0.2.1
          hp0.2.2.2.1 hRow0 hF0 hgroups0 hown0 hNew0) (HW_of hS hR O hT N Mg Dp.cs G arr smp ms decT
    c₀ tokOf hC hWr (hCap 356) msgW hmW radW hCondW h1W hpowW
          hRowW hFW hPlW hbaseW hNewW hshownW)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_law_whole
