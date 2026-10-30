-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersFill.lean: THE TABLE OF JOINTS' SIX LETTERS ON THE READING OF THE
ORACLES, FILLED BY THE LIBRARY's OWN NOTIONS, CALLED; and THE TABLE's ONE EXTRACTOR. Definitions,
and small lemmas.

What is said. `meaningSig`: a meaning of the items (`Meaning`, Johnson/Desc/First/Borders.lean)
whose fields pin · noColl · shown · held · pinW · decodes are those of
Johnson/Desc/Sound/MeaningSig.lean and Johnson/Desc/SmpRows.lean (over the library's signature of a
sending: its decoder with a sample, its collision). `mineAt`: the row's own members: those that sit
at the seats whose pins the row closes. `minePadAt`: those whose pads alone it lays (a switch: the
copies that the group in front has kept). `extQ`: THE EXTRACTOR OF THE BLOCK AT A PLACE: the witness
behind the block with the row's own members' messages and pads, and the pads alone of the others,
set to what they decode to AT THE STATEMENT IN FRONT, and, at the reply's block, the token set to
what the record BEHIND has heard (Johnson/Desc/Sound/World.lean, `extAt`). `extQAt`: the same at
block number k, as a function of the block's two statements and the witness behind. `EachExtQ`:
every piece of a row has that extractor, wherever its block says yes. `extQ_lays_heard_token`,
`extQ_keeps_token`, `laysTok_only_K7`: THE TOKEN: the reply's row lays what is read off the record
behind; no other row lays it. (THE THIRD FACT, that what the record holds of the reply is the same
behind as in front at every other block, is the blocks' texts': not here.) `extQ_id`: at a row that
lays nothing it is the identity. `seatTab`: THE WITNESS's TABLE AT A SEAT: the one accessor for
every reader of a message at the table. `segMsg`: a segment's messages off the witness, through it.

Limits. (1) The letters beneath (the codes, the sendings' members ms, arr, smp, decT, the token's
reader) are letters still. decT IS MEANT AS THE TOP's GUARDED DECODER (nothing where two members of
the stored table's list have the record's answers), NOT AS A DECODER WITHOUT THE GUARD: at that one
"decodes" does not give "no collision", and the joint with the shared chain has a premise that
nobody can pay. (2) The library's sample holds the SEED, which is no field of the carried
record: the filling that is meant (Johnson/Desc/Sound/Seed.lean) reads it back off the record's
sample rows; that reading has run at both sizes; at `smp := nothing` every pin holds of nothing. (3)
`EachExtQ` is a form of a premise: whoever makes the pieces meets it by rfl.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers laysSeats laysPads laysTok)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)

/-- **The six letters, filled.** -/
def meaningSig (Mg : Meaning P (Wit Cells Tok MsgT)) : Meaning P (Wit Cells Tok MsgT) :=
  { Mg with
    pin := pinJT cs G arr smp ms
    noColl := noCollJT cs G smp ms
    shown := shownJT cs G ms
    held := fun j t a => smpHeld a.2.st a.2.book j t
    pinW := pinWOf decT
    decodes := decodesOf decT }

/-- **THE WITNESS's TABLE AT A SEAT** (tree, tenant): the one accessor (`memTab`, World.lean), at
the member of ms that sits there: its own shape, number and seat: so it cannot be called at a number
or a shape that is not the seat's. AT A SEAT THAT IS NO MEMBER's IT IS THE ZERO MESSAGE, IN SILENCE:
whoever reads it asks that the seat is a member's (a test on the plan: it has run at both plans for
the seats that a row lays). -/
def seatTab (w : Wit Cells Tok MsgT) (x : ℕ × ℕ) : MsgT :=
  match ms.find? fun y => decide (seatOf y = x) with
  | some y => memTab cs arr w y
  | none => fun _ _ _ => 0

/-- **THE WITNESS's SIDE OF "what the prover hides"**: message number k of segment m's own list (its
sampled tenants, moment by moment, in the order of sending), as the witness names it: mask row or
main row, row, place ↦ a field element. WHERE arr GIVES A KEPT MESSAGE's TWO TENANTS ONE NUMBER the
copy in segment m + 1's list and the original in segment m's are one function OUTSIDE THEIR PADS.
BEYOND THE LIST's END IT IS THE ZERO MESSAGE, IN SILENCE: whoever reads it asks k below the list's
length. -/
def segMsg (N : Numbers) (w : Wit Cells Tok MsgT) (m k : ℕ) : MsgT :=
  match (N.group m)[k]? with
  | some x => seatTab cs arr ms w x
  | none => fun _ _ _ => 0

/-- The row's own members. -/
def mineAt (N : Numbers) (links : List ModelPart) (p : Place) : List Mem :=
  ms.filter fun x => (laysSeats N links p).contains (x.1.seat x.2)

/-- The members whose pads alone the row lays. -/
def minePadAt (N : Numbers) (links : List ModelPart) (p : Place) : List Mem :=
  ms.filter fun x => (laysPads N links p).contains (x.1.seat x.2)

variable (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **The extractor of the block at a place.** behind: the record that the block puts out. -/
def extQ (N : Numbers) (links : List ModelPart) (p : Place) (a : P × First.S) (y : Strs)
    (behind : Option (P × First.S)) (w : Wit Cells Tok MsgT) : Wit Cells Tok MsgT :=
  extAt cs G arr smp decT c₀ (mineAt ms N links p) (minePadAt ms N links p) false
    (if laysTok links p then behind.map tokOf else none) a y w

/-- **The table's extractor at block number k, as a function of the block's two statements and the
witness behind**: no transcript is read. Beyond the index: the identity. -/
def extQAt {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    Wit Cells Tok MsgT :=
  match ps[k]? with
  | some p =>
    extQ cs G arr smp ms decT c₀ tokOf N links p (get a.1) (strsOf Fr a.2) (some (get b.1)) w
  | none => w

/-- Every piece of a row has the table's extractor, wherever its block says yes. -/
def EachExtQ {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) :
    ℕ → List (Piece C Fr A Cl (Wit Cells Tok MsgT)) → Prop
  | _, [] => True
  | k, q :: l =>
    (∀ a τ b w, q.ior.red.out a τ = some b →
      q.ext a τ w = extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w) ∧
      EachExtQ N links ps get (k + 1) l

/-- **THE TOKEN (1): at the row that lays it, the extractor's value bears the token that is read off
the record BEHIND the block**, whatever the witness behind. -/
theorem extQ_lays_heard_token (N : Numbers) (links : List ModelPart) (p : Place)
    (h : laysTok links p = true) (a b : P × First.S) (y : Strs) (w : Wit Cells Tok MsgT) :
    (extQ cs G arr smp ms decT c₀ tokOf N links p a y (some b) w).tok = tokOf b := by
  unfold extQ
  rw [h]
  rfl

/-- **THE TOKEN (2): no other row lays it**: there the extractor's value has the token of the
witness behind. -/
theorem extQ_keeps_token (N : Numbers) (links : List ModelPart) (p : Place)
    (h : laysTok links p = false) (a : P × First.S) (y : Strs) (behind : Option (P × First.S))
    (w : Wit Cells Tok MsgT) :
    (extQ cs G arr smp ms decT c₀ tokOf N links p a y behind w).tok = w.tok := by
  unfold extQ
  rw [h]
  rfl

/-- **THE TOKEN (2'): the rows that lay it are of the reply's kind alone.** -/
theorem laysTok_only_K7 (links : List ModelPart) (p : Place) (h : laysTok links p = true) :
    p.kind = .K7 := by
  unfold laysTok at h
  exact eq_of_beq (Eq.mp (Bool.and_eq_true _ _) h).2

/-- At a row that lays nothing the table's extractor is the identity. -/
theorem extQ_id (N : Numbers) (links : List ModelPart) (p : Place)
    (h : (First.rowOf links p).lays = false) (a : P × First.S) (y : Strs)
    (behind : Option (P × First.S)) (w : Wit Cells Tok MsgT) :
    extQ cs G arr smp ms decT c₀ tokOf N links p a y behind w = w := by
  have h1 : laysSeats N links p = [] := by
    unfold laysSeats
    rw [h]
    rfl
  have h2 : laysTok links p = false := by
    unfold laysTok
    rw [h]
    rfl
  have h1' : laysPads N links p = [] := by
    unfold laysPads
    rw [h]
    rfl
  have h3 : mineAt ms N links p = [] := by
    unfold mineAt
    rw [h1]
    exact List.filter_eq_nil_iff.2 fun _ _ => by simp
  have h3' : minePadAt ms N links p = [] := by
    unfold minePadAt
    rw [h1']
    exact List.filter_eq_nil_iff.2 fun _ _ => by simp
  unfold extQ
  rw [h2, h3, h3']
  exact extAt_none cs G arr smp decT c₀ a y w

end

end VerifiableInference.Desc.Sound
