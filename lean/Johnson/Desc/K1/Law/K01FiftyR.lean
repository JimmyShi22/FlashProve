-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01FiftyR.lean: K01_law's FIFTY LATER PLACES IN THE SECOND FORM OF THE CHAIN OF PROMISES (TiedAtR, Johnson/Desc/Sound/ChainOfPromisesR.lean), AT A MEANING M9 FROM WHICH THE EIGHT NAMES THAT ONLY CARRY A FACT ON THE VERIFIER's STATE, AND K1's FILES'
CONJUNCT OF "in order", HAVE BEEN STRUCK. k01_fifty (Johnson/Desc/K1/Law/K01Law.lean) is taken AS IT STANDS at the wider meaning
  mw1 N D13 dk M9 := M9 with plus13's door and public tests, and "in order" := plus13's && liveB N D13.shape (where a link is open, its frame's group number and its frame's shape are the plan's)
and carried down by the kind-free bridge tiedAtR_of_classA (Johnson/Desc/Sound/PlusDoorA.lean). THE STATEMENT IS MADE BY PROGRAM OUT OF k01_fifty's OWN BINDERS (Mg ↦ mw1 N D13 dk M9).
PREMISES THAT COME BESIDE k01_fifty's: hD (the test on the two doors at every border: a Bool with code) · hFacts (AT THE TWO BORDERS OF THE PLACE ALONE, IN FoldFacts' OWN TERMS: Rch gives, at a state without a mark: FactsK13; and of the open link's copy: its frame's group is N.groupAt l [FoldFacts.groupIs] and its frame's shape the plan's [liveShape]:
liveB, which names the open link's own number, is had from these WITH THE NARROW PROMISE's shapeAt: no field of FoldFacts says the open link's number) · hHand (Rch is handed on at each piece: rchAt_hand).
What is not claimed. No premise is shown. Nothing at link 0's first place and at W's (left to other files). Nothing on soundness.

-/
import Johnson.Desc.K1.Law.K01Law
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ Stated smpNamed widen TiedAtR HandsOn doorsFitB tiedAtR_of_widen onQ_down_A onQ_up_A FactsAt)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt OldKept plus13 cA13 FactsK13 plus13_hand plus13_io plus13_class)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open k1Ix k1Reads)

/-- **The wider meaning for K1's later sendings.** -/
def mw1 {Pp W : Type} {nR : ℕ} (N : Numbers) (D : K13.Law.DataK13 Pp W nR) (dk : K12.Door.K12Data)
    (M9 : Meaning Pp W) (xb : S → Bool := fun _ => true) : Meaning Pp W :=
  widen M9 (plus13 D dk M9).more (plus13 D dk M9).pub
    fun x => (plus13 D dk M9).inOrder x && liveX N D.shape xb x.2

/-- The test: the places in front of and behind each of the fifty later sendings are places of that link. -/
def linkTwoB : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    ((flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]?.bind (·.link)) == some l &&
      ((flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2 + 1]?.bind (·.link)) == some l

set_option maxRecDepth 1000000 in
theorem linkTwoB_true : linkTwoB = true := by decide +kernel

theorem link_two (l : ℕ) (hl : l < 25) (d : Bool) (j : ℕ)
    (hj : j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) :
    ∃ p, (flatPlacesOf linksFull true)[j]? = some p ∧ p.link = some l := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 linkTwoB_true l (List.mem_range.2 hl)) d
    (by cases d <;> simp)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  rcases hj with rfl | rfl
  · obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.1 h.1
    exact ⟨p, hp, hpl⟩
  · obtain ⟨p, hp, hpl⟩ := Option.bind_eq_some_iff.1 h.2
    exact ⟨p, hp, hpl⟩

/-- **THE FIFTY, IN THE SECOND FORM.** -/
theorem k01_fiftyR {P : VerifierAndGoals.PublicFiles}
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
    (M9 : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT)) {nD : ℕ}
    (D13 : K13.Law.DataK13 ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT) nD) (dk : K12.Door.K12Data)
    (xb : S → Bool)
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
      headPart digitsPart fI fB Mg0 (mw1 N D13 dk M9 xb))
    (hB : BoolsK1 N Dp seats Z Bs.G₀ (mw1 N D13 dk M9 xb).more fI)
    (hBase : BaseK1 (mw1 N D13 dk M9 xb).more MgP)
    (hc : Bs.G₀.first.codes = codesFull2)
    (hs : Bs.G₀.first.shape = shapeFull)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hCap : ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, (rest₁ (noL l d) [d₁, d₂]).err =
      Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hRows : First.eachOnce ((List.range 26).map fun m => (N.groupAt m, 0)) = true)
    (hBook : First.bookFit N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true)
    (hFence : First.fenceFit N linksFull (flatPlacesOf linksFull true) = true)
    (hSent : ∀ l, l < 25 → ∀ d : Bool, sentAtB N (toldBy c.blocksInOrder) (noL l d) l (momL d) = true)
    (hBlind : K13.Law.DecBlind decT)
    (ioP : ProofFile.InstPub → Bool) (hIoIs : ∀ a, io0 a = (ioP a.1 && liveX N shape xb a.2))
    (hxb : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' : ProofFile.InstPub × S,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' → xb x.2 = true → xb x'.2 = true)
    (mLed : ℕ → Bool → ℕ)
    (hled : ∀ l, l < 25 → ∀ d : Bool, Pub.ledger (mLed l d) ∈
      (First.pubSets (mw1 N D13 dk M9 xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (hnl : ∀ l, l < 25 → ∀ d : Bool, ∀ m, Pub.left m ∉
      (First.pubSets (mw1 N D13 dk M9 xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (aPile : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w, YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' → (mw1 N D13 dk M9 xb).pile x' y' w → (mw1 N D13 dk M9 xb).pile x y w)
    (aWo : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.wo m ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → (mw1 N D13 dk M9 xb).wo m x' y' w → (mw1 N D13 dk M9 xb).wo m x y w)
    (hNd : seats.Nodup)
    (hSeats : ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? = some (seatOfMsg (parL Z Bs.G₀ l d) (baseL aN R₁ R₂ R₃ c l d) j.val))
    (hRd : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈ (First.pubSets (mw1 N D13 dk M9 xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 N D13 dk M9 xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dp D3) m j r x.2 x'.2)
    (hrest : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → q ∈ (First.pubSets (mw1 N D13 dk M9 xb).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) → q ∈ (First.pubSets (mw1 N D13 dk M9 xb).more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → (mw1 N D13 dk M9 xb).pub q x' = true)
    (hreq : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x', YesOf (blkL Z Bs.G₀ l d X arrs) x x' → H.req x' = H.req x)
    (hhead : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w p i, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr hd p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → headPart p i x' y' w → headPart p i x y w)
    (hdig : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → digitsPart m x' y' w → digitsPart m x y w)
    (hwt : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m j, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → wt m x' y' w → wt m x y w)
    (hmeet : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (noL l d) x y →
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
      onQ N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (baseL aN R₁ R₂ R₃ c l d) d₁ d₂ (parL Z Bs.G₀ l d).coordinates (errPort (parL Z Bs.G₀ l d) (radRec (recL l d) (parL Z Bs.G₀ l d)))).ior.red.out a τ = some x → ∀ q ∈ tiedL (mw1 N D13 dk M9 xb).more l d, (mw1 N D13 dk M9 xb).pub q (z, x.1) = true)
    (hback : ∀ l, l < 25 → ∀ d : Bool, d = false → ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (c' : Block S Cl),
      c'.UnderR ((blkL Z Bs.G₀ l d X arrs).retype : Block S Cl) → ∀ (z : ProofFile.InstPub) a τ x w,
      onQ N (mw1 N D13 dk M9 xb) linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c' (baseL aN R₁ R₂ R₃ c l d) d₁ d₂ (parL Z Bs.G₀ l d).coordinates (errPort (parL Z Bs.G₀ l d) (radRec (recL l d) (parL Z Bs.G₀ l d)))).ior.red.out a τ = some x →
      ((Item.pin l 0).holds N (mw1 N D13 dk M9 xb) (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) w →
        (Item.pin l 0).holds N (mw1 N D13 dk M9 xb) (z, a.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) a.2) w) →
      ((mw1 N D13 dk M9 xb).constr l .small (z, x.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) w →
        (mw1 N D13 dk M9 xb).constr l .small (z, a.1) (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) a.2) w) →
      relAt (meansQ N (mw1 N D13 dk M9 xb) fun s : S => (z, s)) (outsQ linksFull (flatPlacesOf linksFull true) (noL l d)) x w →
      relAt (meansQ N (mw1 N D13 dk M9 xb) fun s : S => (z, s)) (insQ linksFull (flatPlacesOf linksFull true) (noL l d)) a w)
    -- THE BRIDGE's
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (hD : ∀ i, doorsFitB M9.more (plus13 D13 dk M9).more cA13 linksFull (flatPlacesOf linksFull true) i = true)
    (hFacts : ∀ l, l < 25 → ∀ d : Bool, ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, Rch j a → onQ N M9 linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
        FactsK13 D13 dk M9 a.1 ∧
        (∀ L, a.1.2.link? = some L → L.check.frame.group = N.groupAt l ∧ L.check.frame.shape = D13.shape) ∧ xb a.1.2 = true)
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt Dp.cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) i))) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ q, (T.p₁ :: T.l₁)[14 * l + k1Ix l d + 2]? = some q →
      TiedAtR N M9 linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (14 * l + k1Ix l d + 2)
        (q.withMap ((fun k => extQAt Dp.cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true)
        (fun a => a) k) (14 * l + k1Ix l d + 2))) := by
  intro l hl d q hq
  have facts : ∀ j, (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) → ∀ a, Rch j a →
      onQ N M9 linksFull (flatPlacesOf linksFull true) (fun a => a) j a →
      FactsAt M9 (plus13 D13 dk M9).more (plus13 D13 dk M9).pub
        (fun x => (plus13 D13 dk M9).inOrder x && liveX N D13.shape xb x.2) cA13 linksFull (flatPlacesOf linksFull true) (fun a => a) j a := by
    intro j hj a hr hon hm
    obtain ⟨hF, hG, hXb⟩ := hFacts l hl d j hj a hr hon hm
    refine ⟨fun h0 => ?_, fun i _ hc => ⟨plus13_class D13 dk M9 _ hF i hc, hF.quiet i hc⟩⟩
    have h1 : (plus13 D13 dk M9).inOrder a.1 = true := by
      show (M9.inOrder a.1 && K13.Law.inOrderK13 D13.codes D13.shape D13.layout a.1.2) = true
      rw [h0, hF.order]
      rfl
    have hlv : liveB N D13.shape a.1.2 = true := by
      obtain ⟨p, hp, hpl⟩ := link_two l hl d j hj
      obtain ⟨_, hq'⟩ := hon
      rcases hq' with hx | ⟨h2, _, _, _⟩
      · exact absurd hm hx
      simp only [Bool.and_eq_true] at h2
      have hsh : First.shapeAt linksFull (flatPlacesOf linksFull true)[j]? a.1.2 = true := h2.1.1.1.1.1
      rw [hp] at hsh
      unfold First.shapeAt at hsh
      simp only [Bool.and_eq_true] at hsh
      have a1 := hsh.2
      unfold liveB groupAllB liveShapeB
      cases hL : a.1.2.link? with
      | none => rfl
      | some L =>
        rw [hL, Option.all_some] at a1
        have e3 : L.link = l := Option.some.inj ((eq_of_beq a1).symm.trans hpl)
        obtain ⟨g1, g2⟩ := hG L hL
        rw [Option.all_some, Option.all_some, g1, g2, e3]
        simp
    show ((plus13 D13 dk M9).inOrder a.1 && liveX N D13.shape xb a.1.2) = true
    unfold liveX
    rw [h1, hlv, hXb]
    rfl
  refine tiedAtR_of_widen N M9 (plus13 D13 dk M9).more (plus13 D13 dk M9).pub
    (fun x => (plus13 D13 dk M9).inOrder x && liveX N D13.shape xb x.2) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch _ _
    (fun b => onQ_down_A N M9 _ _ _ cA13 linksFull (flatPlacesOf linksFull true) (fun a => a) _ b (plus13_hand D13 dk M9)
      (fun x h => plus13_io D13 dk M9 x ((Bool.and_eq_true _ _ ▸ h).1)) (hD _))
    (fun a hr h => onQ_up_A N M9 _ _ _ cA13 linksFull (flatPlacesOf linksFull true) (fun a => a) _ a (plus13_hand D13 dk M9) (hD _)
      (facts _ (Or.inl rfl) a hr h) h)
    (fun b hr h => onQ_up_A N M9 _ _ _ cA13 linksFull (flatPlacesOf linksFull true) (fun a => a) _ b (plus13_hand D13 dk M9) (hD _)
      (facts _ (Or.inr rfl) b hr h) h)
    (hHand _ q hq) ?_
  · exact k01_fifty hS hR O hT N (mw1 N D13 dk M9 xb) Dp G arr smp ms decT shape layout io0 base X3 D3 MgP Mg0 seats St
      after wt rwB hd put H headPart digitsPart fI fB c₀ tokOf hL hB hBase hc hs hC hWr hCap hOk
      hRoots hRows hBook hFence hSent hBlind ioP xb hIoIs hxb mLed hled hnl aPile aWo hNd hSeats hRd hrest hreq hhead hdig
       hwt hmeet hPlanR hTold dep hFit hpub hback l hl d q hq

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_fiftyR
