-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RidesFenced.lean: WHAT RIDES PAST K4's BLOCK AT THE TABLE OF JOINTS, IN THE FENCED
FORM IN WHICH THE TABLE's TIE ASKS IT OF A KIND AT A SEAT: an item that is open at the border in
front of the block and that the block's row does not close, and that holds behind a yes (with all
that is open there), at a witness w, HOLDS IN FRONT OF THE YES AT THE SAME w. A record of two lines,
one statement with its proof. GLUE: no draw, no count.

  `K4Riders`: TWO LINES ON THE MEANING: same: every such item BUT formsT m 2 "objects" goes from y
    back to x wherever `SameIn … q.base x y` (K4PromiseBehind.lean: x inside the promise in front,
    without a mark, and `SameRead q.base x y`, RidesBack.lean): its meaning reads only what a yes of
    K4's leaves: the record but for the ledger, what K4 heard and the debt of rows; the stored
    table; the trees below the stretch's base · objects: formsT m 2 "objects" (the lookup's own
    claims, opened at piece 2, closed by the sending at piece 4) goes back from behind a `Yes` to in
    front of it: ITS MEANING READS THE LEDGER, WHICH K4's YES TURNS: so it is asked at a `Yes`,
    inside the promise, not from `SameRead`.
  **`k4_rides_fenced`**: UNDER `K4Riders`, at a piece that holds `below bk`, bk hearing as K4's own
    block, no round behind: the clause, in its own letters (`onQ` on both sides, no mark, `relQ (k +
    1) b w`, `openAfter … k i`, `¬ insQ links ps k i`: `meansQ … i a w`).

Limits. `K4Riders` IS A PREMISE: no filling of `Meaning` is shown to meet it. BY READING the table's
rows, the riders at a layers' piece 3 are the constraints of this and of later segments (the witness
alone), the segment's rows (the statement's groups: st), the pile, and formsT m 2 "objects": NO PIN
RIDES THERE: pin m 0, pinW and pinI stand in what the row reads, which `insQ` holds. Should a pin
ride, same hangs for it on two lines that nobody pays here: it sits in a tree below q.base (a line
on the numbers and the plan), and the sample's reader gives one thing at the two records (hs of
SameReadSig.lean, whose `pin_iff` then pays it). objects wants that the lookup's claims name slots
that are filled in the ledger in front already (K4's yes leaves what lies under a filled slot:
`KeptAtS`). The promise behind and the fence are not spent. Nothing on soundness.
-/
import Johnson.Road.K4.K4PromiseBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start)
open VerifiableInference.Desc.Sound (Frame Piece below onQ relQ meansQ insQ outsQ openAfter)
open VerifiableInference.Desc.Plain.K04 (HearsAs)

variable {P W Cl : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (Z : P)

/-- The two lines on the meaning. -/
structure K4Riders (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (q : Piece (ckP .two) Fr S Cl W) (par : Par) : Prop where
  /-- every rider but the lookup's own claims reads only what a yes of K4's leaves: ASKED INSIDE THE
  FENCE (`SameIn`: x inside the promise in front, without a mark): outside a layers' link `SameRead`
  lets the open part differ, and there the line is false at a pile that is read off that part -/
  same : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
    ¬ insQ links ps k i → i ≠ .formsT m 2 "objects" → ∀ (x y : S × Fr.E.Str) (w : W),
    SameIn N Mg Z links ps k q.base x y → meansQ N Mg (fun s => (Z, s)) i y w →
    meansQ N Mg (fun s => (Z, s)) i x w
  /-- the lookup's own claims, whose meaning reads the ledger -/
  objects : ∀ a τ fo o G w, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
    Yes seatS par q a τ fo o G →
    meansQ N Mg (fun s => (Z, s)) (.formsT m 2 "objects") (behindOf seatS q a τ o G) w →
    meansQ N Mg (fun s => (Z, s)) (.formsT m 2 "objects") a w

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {q : Piece (ckP .two) Fr S Cl W}
  {par : Par} {bk : Block S Cl}

/-- **UNDER `K4Riders` (A PREMISE): what rides past K4's block, in the tie's fenced form.** -/
theorem k4_rides_fenced (R : K4Riders N Mg Z links ps k m q par) (hb : q.b = below bk)
    (hh : HearsAs seatS par bk) (hback : q.back = []) (a : S × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) q.ds)) (b : S × Fr.E.Str) (w : W) (i : Item)
    (ha : onQ N Mg links ps (fun s => (Z, s)) k a) (hu : ¬ a.1.failed ≠ none)
    (h : q.ior.red.out a τ = some b) (_hb' : onQ N Mg links ps (fun s => (Z, s)) (k + 1) b)
    (hr : relQ N Mg links ps (fun s => (Z, s)) (k + 1) b w)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i)
    (hi : ¬ insQ links ps k i) : meansQ N Mg (fun s => (Z, s)) i a w := by
  obtain ⟨_, fo, o, G, y, rfl⟩ := yes_of_out seatS hh hb hback a b τ h
  have hm : meansQ N Mg (fun s => (Z, s)) i (behindOf seatS q a τ o G) w := hr i (Or.inl ⟨ho, hi⟩)
  by_cases e : i = .formsT m 2 "objects"
  · subst e
    exact R.objects a τ fo o G w ha (Classical.not_not.mp hu) y hm
  · exact R.same i ho hi e _ _ w ⟨ha, Classical.not_not.mp hu, sameRead_of_yes y⟩ hm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_rides_fenced
