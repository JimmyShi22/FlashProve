--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/More/MadeEleven.lean: BEHIND AN ACCEPT OF K4's SUB-PROTOCOL ELEVEN PUBLIC ITEMS'
TESTS ACCEPT, FROM FIFTEEN PUBLIC ITEMS' TESTS, ONE EQUATION (the statement's codes), ONE LINE ON
WHAT THE LOOKUP HEARD AND TWO TESTS OF THE BOOK-KEEPING AT THE STATE IN FRONT: AT A MEANING WITH THE
STRUCTURE OF EQUATIONS `K4Means`: NO PROMISE, NO PIECE, NO STRING, NO WITNESS. One structure, one
statement with its proof: calls.

  `frontAsks m`: the fifteen items. `k4Eleven m`: the eleven: lookOut m 2 · formsInT m 2 "objects" ·
    ledger m · freeAbove m · "ledger.treesAre" m (kept) · lookIn m 7 · leftOn m · formsInT m 3 "own"
    · formsInT m 2 "planes" · formsInT m 2 "join" · hasRow m (made).
  `PubFront`: what is asked of the state in front: the fifteen tests accept · the statement's codes
    are the data's · what the lookup heard has the public parameters' shape · the state has the
    shape of K4's place · the book has the plan's counts.
  **`made_eleven`**: `K4Means Mg D` · `AtK4` · `K4RowPlan` (at hp := par.hp) · `K4Seats` · `KeptAtS
  par s s'` · `PubFront` at s ⟹ ∀ q ∈ k4Eleven m, Mg.pub q (Z, s') = true.

WHY. The rows of the first table that speak of the public tests alone have no promise in hand.

Limits. `K4Means` HOLDS AT THE WIDER MEANING, NOT AT THE COMPOSED ONE: four of the fifteen
("pile.room" · "frame.liveIs" · "K12.seatsCarried" · "K12.msgShapes") have left the composed
meaning's door. Every premise stands. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.More.OwnAtState
import Johnson.Road.K4.More.KeptAtStates
import Johnson.Road.K4.K4RowOfMeans
import Johnson.Road.K4.K4KeepKeeper

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.More

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.Rec (recPlanOf recMeans_of_means)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning shapeAt bookAt)
open VerifiableInference.Desc.First.Look (liveItem)
open OnBytes.Road.K4.Riders (placeAt_link)
open VerifiableInference.Desc.Sound (MsgT)

/-- The fifteen public items whose tests are spent at the state in front. -/
def frontAsks (m : ℕ) : List Pub :=
  [.ledger m, .freeAbove m, .look m, .linkFresh m, .callerIn m, .lookOut m 2,
   .more (some m) "K4.lookLeft", .more (some m) "K4.rowsBare", .more (some m) "frame.sentIs",
   .more (some m) "ledger.treesAre", .formsInT m 2 "objects", .more (some m) "pile.room",
   liveItem m, .more none "K12.seatsCarried", .more none "K12.msgShapes"]

/-- The eleven public items whose tests accept behind. -/
def k4Eleven (m : ℕ) : List Pub :=
  [.lookOut m 2, .formsInT m 2 "objects", .lookIn m 7, .leftOn m, .formsInT m 3 "own",
   .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m, .ledger m, .freeAbove m,
   .more (some m) "ledger.treesAre"]

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X}

/-- **What is asked of the state in front.** -/
structure PubFront (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT))
    (D : K4Data Xi P Tok rows cols nR kC X) (Z : P) (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (pl : Place) (s : S) : Prop where
  asks : ∀ q ∈ frontAsks m, Mg.pub q (Z, s) = true
  codes : s.st.codes = D.cs
  heard : ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = X.y.fo
  shape : shapeAt links (some pl) s = true
  book : bookAt D.N ps[k]? s = true

/-- **The eleven behind an accept.** -/
theorem made_eleven (E : K4Means Mg D) {rest : Option ℕ → String → Bool} {Z : P}
    {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place} {par : Par}
    {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
    {layout : Option ByteArray} {n : ℕ} (H : AtK4 links ps k m pl)
    (Pl : K4RowPlan D rest links ps k m pl par told pol KL layout par.hp n)
    {Hh : K9.LinkHoles} {l : Link S Claim} {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (Se : K4Seats D m par Hh l nO nG runO runG) {s s' : S} (K : KeptAtS par s s')
    (F : PubFront Mg D Z links ps k m pl s) : ∀ q ∈ k4Eleven m, Mg.pub q (Z, s') = true := by
  have hl : VerifiableInference.Desc.First.FillK4.isLay D.links m = true := by
    rw [Pl.linksIs]
    unfold VerifiableInference.Desc.First.FillK4.isLay
    rw [H.sub]
    rfl
  have RM := recMeans_of_means E D.sd E.sentIs E.treesAre
  have f1 := F.asks (.ledger m) (by simp [frontAsks])
  have f2 := F.asks (.freeAbove m) (by simp [frontAsks])
  have f3 := F.asks (.look m) (by simp [frontAsks])
  have f4 := F.asks (.linkFresh m) (by simp [frontAsks])
  have f5 := F.asks (.callerIn m) (by simp [frontAsks])
  have f6 := F.asks (.lookOut m 2) (by simp [frontAsks])
  have f7 := F.asks (.more (some m) "K4.lookLeft") (by simp [frontAsks])
  have f8 := F.asks (.more (some m) "K4.rowsBare") (by simp [frontAsks])
  have f9 := F.asks (.more (some m) "frame.sentIs") (by simp [frontAsks])
  have f10 := F.asks (.more (some m) "ledger.treesAre") (by simp [frontAsks])
  have f11 := F.asks (.formsInT m 2 "objects") (by simp [frontAsks])
  have f12 := F.asks (.more (some m) "pile.room") (by simp [frontAsks])
  have f13 := F.asks (liveItem m) (by simp [frontAsks])
  have f14 := F.asks (.more none "K12.seatsCarried") (by simp [frontAsks])
  have f15 := F.asks (.more none "K12.msgShapes") (by simp [frontAsks])
  have g4 := f4
  rw [E.ledger] at f1
  rw [E.freeAbove, Pl.nsOf] at f2
  have f2' : VerifiableInference.Desc.First.freeAboveB par.hp.ns s = true := by simpa using f2
  rw [E.look m _ hl] at f3
  rw [E.linkFresh] at f4
  rw [RM.fresh] at g4
  rw [E.callerIn m _ hl, Pl.nextOf] at f5
  have f5' : VerifiableInference.Desc.First.FillK4.callerInLayB n s = true := by simpa using f5
  rw [← Pl.pc2, E.lookOut] at f6
  rw [E.lookLeft m _ hl] at f7
  rw [E.rowsBare m _ hl] at f8
  rw [E.sentIs] at f9
  rw [E.treesAre] at f10
  rw [E.formsInT, Pl.runsObj, Se.Rd] at f11
  rw [E.room] at f12
  have g13 : Mg.pub (.more (some m) "frame.liveIs") (Z, s) = true := f13
  rw [RM.live] at g13
  rw [E.seatsCarried] at f14
  rw [E.msgShapes] at f15
  have hb := F.book
  simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hb
  have OF : OwnFront par (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m par.hp.ns s :=
    { ledger := f1
      free := f2'
      look := f3
      lookLeft := f7
      live := g13
      fresh := g4
      seats := f14
      shapes := f15
      sent := f9
      trees := f10
      codes := F.codes
      places := hb.1.2.trans hb.2
      msgs := hb.2
      heard := Pl.shape ▸ F.heard }
  intro q hq
  simp only [k4Eleven, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← Pl.pc2, E.lookOut]
    exact lookOut_at K f6
  · rw [E.formsInT, Pl.runsObj, Se.Rd]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at f11
    exact objects_at K Se.fO Se.oRun Se.fG Se.gRun f3 f8 f1 f2' f11.1
  · rw [← Pl.pc7, E.lookIn]
    exact lookIn_at K Pl.lookIn f1 f2' f4 f5' H F.shape fun _ hp => placeAt_link hp
  · exact E.leftOnB m _
  · rw [E.formsInT, Pl.runsOwn, Se.Rd]
    exact own_at K OF Pl.front Pl.maskP Pl.readsP Se.st
  · rw [E.formsInT, Pl.runsPl]
    rfl
  · rw [E.formsInT, Pl.runsJo]
    rfl
  · rw [E.hasRow, Pl.lay, Pl.ncl]
    exact hasRow_at K Pl.row Pl.room1 f12
  · rw [E.ledger]
    exact ledgerB_kept K f1
  · rw [E.freeAbove, Pl.nsOf]
    simpa using freeAboveB_kept K f1 f2'
  · rw [E.treesAre, Riders.treesAreB_kept K f1]
    exact f10

end OnBytes.Road.K4.More

#print axioms OnBytes.Road.K4.More.made_eleven
