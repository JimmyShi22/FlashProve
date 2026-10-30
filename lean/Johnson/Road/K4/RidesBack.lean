-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RidesBack.lean: WHAT A `Yes` (CarriageHeard.lean) LEAVES FOR A READER OF THE
STATEMENT, AND THAT A READER WHICH READS THIS ALONE READS THE SAME BEHIND THE YES AS IN FRONT. For
the road's two letters dec (the reader of the pinned part) and ctx0 (what the row
reads and leaves open): so that whoever fills them owes only "my reader reads these fields alone".
A record, statements and proofs, at the seat `seatS`: calls, no new argument.

  `SameRead base x y`: of the carried record: `Rest x.1 y.1` (Johnson/Desc/First/K4/ReadsAtS.lean:
    st, book, roots, failed, check, out, req the same; link?, tl?, look?, lookHeard? find the same;
    a layers' link stays one, with its context and what it holds of the lookups;
    NOT the ledger, NOT what K4 heard, NOT the debt of rows: these the seat's three setters lay); of
    the strings: the stored table is the same; and each entry that `posL` finds for a tree whose
    number is below base holds the same column.
  **`sameRead_of_yes`**: `Yes seatS par pc a τ fo o G → SameRead pc.base a (behindOf seatS pc a τ o
    G)`: the record by `rest_of_yes` (KeptOfYes.lean); the table by `behindOf`'s definition; the
    trees sent in front of the stretch by `left_below` (Johnson/Desc/Sound/PieceYes.lean).
  **`dec_rides`**: if dec reads the same at any two statements with `SameRead pc.base`, then at a
    yes dec reads the same behind as in front, at any promise `on`.
  **`ctx_rides`**: if ctx0 goes from y back to x wherever `SameRead pc.base x y`, then at a yes ctx0
    rides back from behind to in front. ONE WAY: nothing here carries
    ctx0 forward.
  `strs_same`: under `left_all`'s three premises the strings behind are the strings in front,
    whole.

Limits. dec AND ctx0 STAY LETTERS: THAT A REAL READER READS THESE FIELDS ALONE IS THE FILLER's TO
SHOW (hdec, hctx are premises). «A YES OF THE PIECE» IS HERE THE RECORD `Yes` (CarriageHeard.lean)
AT A PIECE pc THAT IS A LETTER: nothing in this file ties pc to K4's block. From a yes of a piece's
verifier to a `Yes` goes `yes_of_out`, under three premises: the piece holds `below bk`; bk hears as
K4's own block at the seat (`HearsAs`); the piece puts no round behind (pc.back = []). OF THE TREES
`SameRead` SPEAKS OF NUMBERS BELOW base ALONE, at entries that `posL` finds: at a tree whose number
is not below base, inside the stretch or behind it, the stage lays what the stretch's transcript
holds there, and the empty column where it holds none, whatever stood in front: so a reader of a
tree that is sent LATER is served by `strs_same` alone, under its premise hE, which nobody pays. A
reader of the ledger, of what was heard or of the debt is not served. ONE DIRECTION, FROM A YES.
Nothing on soundness.
-/
import Johnson.Road.K4.KeptOfYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS Rest)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece left_below left_all)

variable {Wt Cl Mm : Type} {Fr : Frame}

/-- What a yes of K4's piece leaves for a reader of the statement. -/
structure SameRead (base : ℕ) (x y : S × Fr.E.Str) : Prop where
  /-- of the carried record: all but what the seat's three setters lay -/
  rest : Rest x.1 y.1
  /-- the stored table -/
  table : y.2.1 = x.2.1
  /-- the trees that were sent in front of the stretch -/
  trees : ∀ (j l : ℕ) (q : PosL Fr.all), posL Fr.all j l = some q → j < base → y.2.2 q = x.2.2 q

variable {par : Par} {pc : Piece (ckP .two) Fr S Cl Wt}

/-- **A yes leaves all that.** -/
theorem sameRead_of_yes {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard}
    {o : Own} {G : Fork} (y : Yes seatS par pc a τ fo o G) :
    SameRead pc.base a (behindOf seatS pc a τ o G) :=
  ⟨(rest_of_yes y).1, rfl, fun j l q hq hj => left_below pc a.2 τ j l q hq hj⟩

/-- **A reader of these fields alone reads the same behind a yes as in front.** -/
theorem dec_rides (on : S × Fr.E.Str → Prop) {dec : S × Fr.E.Str → Mm}
    (hdec : ∀ x y : S × Fr.E.Str, SameRead pc.base x y → dec y = dec x) :
    ∀ a τ fo o G, on a → Yes seatS par pc a τ fo o G →
      dec (behindOf seatS pc a τ o G) = dec a :=
  fun _ _ _ _ _ _ y => hdec _ _ (sameRead_of_yes y)

/-- **A condition on these fields alone rides back from behind a yes.** -/
theorem ctx_rides (on : S × Fr.E.Str → Prop) {ctx0 : S × Fr.E.Str → Wt → Prop}
    (hctx : ∀ (x y : S × Fr.E.Str) w, SameRead pc.base x y → ctx0 y w → ctx0 x w) :
    ∀ a τ fo o G w, on a → Yes seatS par pc a τ fo o G →
      ctx0 (behindOf seatS pc a τ o G) w → ctx0 a w :=
  fun _ _ _ _ _ w _ y h => hctx _ _ w (sameRead_of_yes y) h

/-- Under the three premises of `left_all` the strings behind are the strings in front. -/
theorem strs_same (a : S × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) (o : Own) (G : Fork)
    (hT : ∀ d ∈ pc.ds, d.trees = [])
    (hD : ∀ q : PosL Fr.all, posL Fr.all (Fr.all.get q.1).no q.2.val = some q)
    (hE : ∀ q : PosL Fr.all, pc.base ≤ (Fr.all.get q.1).no → a.2.2 q = []) :
    (behindOf seatS pc a τ o G).2 = a.2 :=
  left_all pc a.2 τ hT hD hE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sameRead_of_yes
#print axioms OnBytes.Road.K4.dec_rides
#print axioms OnBytes.Road.K4.ctx_rides
#print axioms OnBytes.Road.K4.strs_same
