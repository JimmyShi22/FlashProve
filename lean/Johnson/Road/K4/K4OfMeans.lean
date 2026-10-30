-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4OfMeans.lean: K4's ROW's TWO STRUCTURES OF LINES `K4Riders` (K4RidesFenced.lean)
AND `K4Keeps` (K4PromiseBehind.lean) OUT OF THE TWO STRUCTURES ON THE MEANING AND ITS LETTERS,
`K4Means` (equations) AND `K4Reads` (what the letters read across an accept), WITH TESTS ON THE
PUBLIC PARAMETERS AND WHAT IS STILL OWED BY NAME. Statements and proofs: calls.

  **`k4Riders_of_means`**: `K4Means` · `K4Reads` · hsort (what rides has `riderSort`: `riders_are`
    under three tests; `riders_full` at the full lists) · hobj (the line objects) ⟹ `K4Riders`.
  **`k4Keeps_of_means`**: `K4Means` · `K4Reads` · `K4Kept` · `K4Front` · TESTS ON THE PUBLIC
    PARAMETERS (k4NextFit · k4ToldFit · bookFit · fenceFit · k4PubFit · k4TiedFit; the door's
    filling read off the data: D.moreL) · D.links = links · hpc (the lookup on the calls stands at
    piece 2) · hbase · only · hObj (formsInT m 2 "objects" rides) · make ⟹ there is a place pl' with
    `K4Keeps`.

Limits. (AND hDoorP: the sentences without a test of the names that the door lets K4's row make
hold.) WHAT IS STILL A PREMISE BESIDE THE TWO STRUCTURES AND THE TESTS: hobj, hObj (the lookup's run
"objects" across K4's accept: Riders/ObjectsAtMeans.lean has both, under a structure of named
premises) · make (what K4's row makes: Riders/MakeOfMeans.lean, item by item) · `K4Front`
(K4FrontOfMeans.lean) · hbase, only (lines on the public parameters and the piece).
K4RowOfMeans.lean calls all of these. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.K4Reads
import Johnson.Road.K4.K4MeansFields
import Johnson.Road.K4.Riders.OfMeans
import Johnson.Road.K4.Riders.KeepsOfMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.Riders (riderSort same_of_means dec_of_means inOrder_of_means restQ_of_means
  keepT_of_means keepP_of_means restP_of_means k4PubFit k4TiedFit lay_in)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Strs)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning start pubSets pubRowM bookFit fenceFit)
open VerifiableInference.Desc.First.FillK4 (isLay k4NextFit k4ToldFit)
open VerifiableInference.Desc.Sound (Frame Piece strsOf insQ outsQ openAfter meansQ onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- Inside K4's laws' fence (`SameIn`) the light fence of `K4Reads` holds. -/
theorem layRest_in (H : AtK4 links ps k m pl) {base : ℕ} {x y : S × Fr.E.Str}
    (h : SameIn D.N Mg Z links ps k base x y) : LayRest x.1 y.1 :=
  ⟨lay_in H h, h.2.2.rest⟩

/-- **`K4Riders` out of the two structures.** -/
theorem k4Riders_of_means (E : K4Means Mg D) (R : K4Reads D Z Fr q.base)
    (H : AtK4 links ps k m pl)
    (hsort : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → riderSort m i = true)
    (hobj : ∀ a τ fo o G w, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G →
      meansQ D.N Mg (fun s => (Z, s)) (.formsT m 2 "objects") (behindOf seatS q a τ o G) w →
      meansQ D.N Mg (fun s => (Z, s)) (.formsT m 2 "objects") a w) :
    K4Riders D.N Mg Z links ps k m q par :=
  ⟨same_of_means E H q.base hsort (fun x y h => R.rw x.1 y.1 (layRest_in H h))
    (fun x y h => R.decT x.1 y.1 (layRest_in H h)) (fun x y h => R.req x.1 y.1 (layRest_in H h))
    (fun x y h => R.head x.1 y.1 x.2 y.2 (layRest_in H h) ⟨h.2.2.table, h.2.2.trees⟩), hobj⟩

/-- **`K4Keeps` out of the two structures, the tests on the public parameters, and what is still
owed.** -/
theorem k4Keeps_of_means (E : K4Means Mg D) (R : K4Reads D Z Fr q.base)
    {rest : Option ℕ → String → Bool} (Kp : K4Kept Mg rest Z)
    (H : AtK4 links ps k m pl) {h3 : Forest.Shape} {lm first : ℕ} {Q3 : Fork → Prop}
    (Kf : K4Front Mg Z links ps m h3 lm first Q3)
    (hnext : k4NextFit links ps = true) (told : List (List VerifiableInference.Desc.Oracle))
    (htold : k4ToldFit links ps told = true) (hbf : bookFit D.N ps told = true)
    (hff : fenceFit D.N links ps = true) (hbase : D.N.treesAt (some pl) = q.base)
    (only : ∀ m', isLay links m' = true →
      Pub.callerIn m' ∈ (pubSets Mg.more links ps)[k]?.getD [] → m' = m)
    (hlinks : D.links = links)
    (hpub : k4PubFit rest D.moreL links ps = true) (htied : k4TiedFit links ps = true)
    (hpc : VerifiableInference.Desc.K3.pieceAt X m false = 2)
    (hObj : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → Mg.pub (.formsInT m 2 "objects") (Z, a.1) = true →
      Mg.pub (.formsInT m 2 "objects") (Z, (behindOf seatS q a τ o G').1) = true)
    (make : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes ++
        [Pub.formsInT m 3 "own", .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m],
      Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true)
    (hDoorP : ∀ nm ∈ (Mg.more.rows links pl).makes, ∀ a,
      Mg.pubP (VerifiableInference.Desc.First.moreItem nm) a) :
    ∃ pl', K4Keeps D.N Mg Z links ps k m pl pl' q par :=
  k4Keeps_at D.N Z (hlinks ▸ E.fields) H Kf hnext told htold hbf hff hbase only
    (fun x y h => R.smp x.1 y.1 (layRest_in H h))
    (dec_of_means E fun a τ fo o G' y c hc => by
      rw [R.decT a.1 _ ⟨(lay_of_look y.look).imp fun _ h => h.1, (rest_of_yes y).1⟩ c]
      exact hc)
    (fun x y h => inOrder_of_means E h.2.2 (R.base x.1 y.1 (layRest_in H h)))
    (restQ_of_means E Kp H Kf.fit (E.more ▸ hpub) hpc) (keepT_of_means E H htied hObj) make
    (keepP_of_means E H (E.more ▸ hpub)) (restP_of_means E H hDoorP)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Riders_of_means
#print axioms OnBytes.Road.K4.k4Keeps_of_means
