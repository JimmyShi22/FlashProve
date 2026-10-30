-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsAtSeat.lean: THE KEY FILE: ROWS 2.3 · 2.6 · 2.8 · 3.0 WHOLE AT THE SEAT: the tables' Keeps, from border k to k + 1, AT A PIECE THAT HOLDS «held» OF THE DESCRIPTION's OWN BLOCK. Four theorems; no definition.

OBJECT. pc.ior.red.Keeps (on k) (on (k + 1)) (L k) (L (k + 1)) pc.err at pc.b = held b, b := (Key.descriptionFromSource X N P).shared.blocksInOrder[3 | 6 | 8] | .second.blocksInOrder[0]; at the shared chain AT THE TABLES' OWN READING T.h₂ (every T : BaseSt); at the last chain at a letter G₃.
USER. The fields r2_3 · r2_6 · r2_8 · r3_0 of the key file's twenty-one laws, through the frame's keepsAt_of_law₂ | ₃.
LETTERS. S is the sized key's shape ((p14At X P).S = (thirdPar X.chains).S by rfl: shape_one). All others free.

THE CAUTION: UNTIL A MEMBER IS SHOWN, EVERY LAW THAT HAS PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING. THESE FOUR ARE SUCH LAWS.
IS IT EMPTY HERE? Keeps speaks of the statements that lie in on k. OF on₂ k | on₃ k AS WHOLES NO MEMBER IS SHOWN BY ANYBODY. What is known, by evaluation at two stored key files (made-up weights; our walks): the four blocks say yes on the honest file; every Bool on the state of the promise says yes at every border. The reading's, the strings' and the collision letter's side: nobody's yet.

HOW. Each is the GENERAL wrap (keeps₂_of_row | keeps₃_of_row: Johnson/RunOne/KeyWrap23.lean) handed its premise «row»: held_decide (the held block's yes is the block's) · our bridge (the block's yes gives the plain facts: Johnson/RunOne/KeyBridges23.lean) · our row at two records (KeyRow23 | 26 | 28 | 30) · at the shared chain our pins_rec | pins_joined | pins_split (KeyPinsAtBase.lean). No round's content is spent: none of the four draws.

WHAT IS LEFT AS A PREMISE, EACH WITH WHOSE IT IS.
  h · hS        K14.blocks (p14At X P) returns these eight · the shape splits. PUBLIC, on the plan. Evaluated true at both stored key files; by k14_sits_plan's kind they follow from planOk: not called here.
  hb · hpb      b is the description's block at that place · the piece holds held b. The frame's cut's (rowAt₂ | ₃).
  hbase         every open pin's tree lies in front of the piece's base. PUBLIC: the piece's base.
  hc            CellOnly coll: the collision letter reads the stored cells alone. Whoever fills coll.
  hsame         (2.3 · 2.8 · 3.0) R.same is «ρ x = ρ y» for a reading ρ of words in a FIELD. Whoever fills KRead.
  hg | hr       (2.3 · 2.6 | 2.8) T.SmGroups | T.SmReads: the letter sm reads neither a message's list «groups» nor its ledger. Whoever fills sm; SmOnly gives both (smGroups_of_only | smReads_of_only: Johnson/RunOne/KeySmOnly.lean: by reading; not imported here).
  3.0 alone     planLin · planNum · atOk: PUBLIC, no record read (of atOk a member is proved) · hp: PinsStay G₃ at_ [0, 2, 4] across the block, ASKED UNDER Laid AND THE PROMISE IN FRONT: THE ONE PREMISE OF SUBSTANCE: at the tables' T.h₃ Omega's seat is read in the border's copy in front and in the own statement behind: Johnson/RunOne/KeyPinsAtBase3.lean has it there, under one condition on sm.
NO BARE ∀ OVER RECORDS IS LEFT BUT hp, which is guarded.

Limits. Err.le to the cap and the tie of the maker's pieces to these pieces are the frame's files' to show. Nothing on chance: none of the four draws. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.RunOne.KeyWrap23
import Johnson.RunOne.KeyBridges23
import Johnson.RunOne.KeyPinsAtBase
import Johnson.RunOne.KeyRow26
import Johnson.RunOne.KeyRow30

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState)

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (T : BaseSt Cells M Smp Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  {K : Type} [Field K] (ρ : Model.Reading K)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

/-- **ROW 2.3, WHOLE AT THE SEAT.** -/
theorem r2_3_seat (pc : Piece C Fr₂ (P₂ × St₂) Claim W)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[3]? = some b) (hpb : pc.b = held b)
    (hbase : ∀ j ∈ pinned (open₂ 3), (at_ j).1 < pc.base) (hc : CellOnly coll)
    (hsame : R.same = fun x y => ρ.val x = ρ.val y) (hg : T.SmGroups) :
    pc.ior.red.Keeps (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 3) (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 4)
      (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 3) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 4) pc.err :=
  keeps₂_of_row F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ pc 3 hbase (by decide) hc
    fun z rs gs z' y _ hd hon => by
      rw [hpb] at hd
      obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
      obtain ⟨GU, rows, L⟩ := recLaid_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h b hb z.2 _ gs z'.2 e2
      have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
      rw [ez]
      exact row23 F T.h₂ at_ (p14At X P).par K₁ R enc rad a coll last₁ off₂ ρ z.1 z.2 z'.2 y L
        ⟨hsame, pins_rec T at_ _ z.1 z.2 z'.2 hg L⟩ hon

/-- **ROW 2.6, WHOLE AT THE SEAT.** -/
theorem r2_6_seat (hS : (p14At X P).S.sharedSplitNeeded = true) (pc : Piece C Fr₂ (P₂ × St₂) Claim W)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[6]? = some b) (hpb : pc.b = held b)
    (hbase : ∀ j ∈ pinned (open₂ 6), (at_ j).1 < pc.base) (hc : CellOnly coll) (hg : T.SmGroups) :
    pc.ior.red.Keeps (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 6) (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 7)
      (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 6) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 7) pc.err :=
  keeps₂_of_row F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ pc 6 hbase (by decide) hc
    fun z rs gs z' y _ hd hon => by
      rw [hpb] at hd
      obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
      obtain ⟨GU, GO, J⟩ := joined_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h hS b hb z.2 _ gs z'.2 e2
      have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
      rw [ez]
      exact row26 F T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ z.1 z.2 z'.2 y J
        (pins_joined T at_ _ z.1 z.2 z'.2 hg J) hon

/-- **ROW 2.8, WHOLE AT THE SEAT.** -/
theorem r2_8_seat (hS : (p14At X P).S.sharedSplitNeeded = true) (pc : Piece C Fr₂ (P₂ × St₂) Claim W)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[8]? = some b) (hpb : pc.b = held b)
    (hbase : ∀ j ∈ pinned (open₂ 8), (at_ j).1 < pc.base) (hc : CellOnly coll)
    (hsame : R.same = fun x y => ρ.val x = ρ.val y) (hr : T.SmReads) :
    pc.ior.red.Keeps (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 8) (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 9)
      (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 8) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 9) pc.err :=
  keeps₂_of_row F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ pc 8 hbase (by decide) hc
    fun z rs gs z' y _ hd hon => by
      rw [hpb] at hd
      obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
      obtain ⟨GU, GO, x, l, n, row, mu, L⟩ :=
        splitLaid_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h hS b hb z.2 _ gs z'.2 e2
      have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
      rw [ez]
      exact row28 F T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ ρ z.1 z.2 z'.2 y L
        ⟨hsame, pins_split T at_ _ z.1 z.2 z'.2 hr L⟩ hon

end

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr₃ : Frame)
  (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)
  {K : Type} [Field K] (ρ : Model.Reading K)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **ROW 3.0, WHOLE AT THE SEAT.** -/
theorem r3_0_seat (pc : Piece C Fr₃ (P₃ × St₃) Claim W)
    (b : Block VerifiableInference.Desc.Third.S₃ Claim) (hb : (descriptionFromSource X N P).second.blocksInOrder[0]? = some b) (hpb : pc.b = held b)
    (hbase : ∀ j ∈ pinned (open₃ 0), (at_ j).1 < pc.base) (hc : CellOnly coll)
    (hsame : R.same = fun x y => ρ.val x = ρ.val y) (hlin : K₁.lin = (thirdPar X.chains).S)
    (hnum : ∀ o, K₁.orc 2 = some o → K₁.num o = some 2) (hat : AtOk at_ off₂ off₃ t₁)
    (hp : ∀ (z : P₃) (s s' : St₃) (y : Strs) bd yO G dot, VerifiableInference.Desc.Third.Laid (thirdPar X.chains).S s s' bd yO G dot →
      onAt F G₃ at_ (meaning₃ (thirdPar X.chains).S K₁ R) (shapeB₃ (thirdPar X.chains).S K₁ a idx src t₁ 0) (Free₃ F G₃ at_ (thirdPar X.chains).S K₁ R coll off₂ off₃ 0) (open₃ 0) (z, s) y →
      PinsStay G₃ at_ [0, 2, 4] (z, s) (z, s')) :
    pc.ior.red.Keeps (on₃ F Fr₃ G₃ at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ 0) (on₃ F Fr₃ G₃ at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ 1)
      (L₃ F Fr₃ G₃ at_ (thirdPar X.chains).S K₁ R 0) (L₃ F Fr₃ G₃ at_ (thirdPar X.chains).S K₁ R 1) pc.err :=
  keeps₃_of_row F Fr₃ G₃ at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ pc 0 hbase (by decide) (by decide) hc
    fun z rs gs z' y _ hd hon => by
      rw [hpb] at hd
      obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
      obtain ⟨bd, yO, G, dot, L⟩ := laid_at_desc X N P b hb z.2 _ gs z'.2 e2
      have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
      rw [ez]
      exact row30 F G₃ at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ ρ z.1 z.2 z'.2 y L
        ⟨hsame, hlin, hnum, hp z.1 z.2 z'.2 y bd yO G dot L hon, hat⟩ hon

end

end Johnson.RunOne.KeyRows23
