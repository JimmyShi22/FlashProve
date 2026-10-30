-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K9RowWritten.lean:
  THE ROW OF KIND K9's LOT, PART 3: AT THE WRITTEN VALUES OF THE FULL SIZE.
  The term k9SkW: the lot's skeleton
  (k9SkE, Johnson/AtFull/Desc/Lots/K9RowAt.lean) at
  the written list of 282 places (spotsWritten, Johnson/AtFull/Desc/SpotsWritten.lean),
  the written first chain's entries (dryProofFull's)
  and the written shape's groups;
  the row at these four values;
  and closed facts on that term by Lean's kernel, each stated AGAINST
  the written table of the first chain's cut (cutFirstFull,
  Johnson/Desc/Ok/PlanWritten/CutLit.lean): no literal of this file's own.
  Definitions with code, statements and proofs.

THE NAMES.
splitE, splitE_eq: k entries taken off a list in ONE loop that ends in a triple (the front; the
  rest; the count of roots, forced at each step): so that Lean's kernel, which evaluates lazily,
  hands on a tail of the written list and a numeral, not a tower of unevaluated drops. It is (take,
  drop, rootsE).
walkE, walk_eq: stretchedE over splitE; it is stretchedE, at every list.
esW, groupsW, lsW, twW, xsW, k9SkW: the written values and the term.
k9_row_written: **(hs : spotsOf Z.cuts = some spotsWritten) (he : Z.D.1.map (·.entry) = esW) (hg :
  Z.s₀.check.frame.groups = groupsW) (ht : ∀ l ∈ lsW, (K9.testsWhere Z.p.X l 0).isSome = twW l) ⊢
  (lotSk G (k9Ninth Z)).cut lsW = k9SkW.cut lsW.**
rowButName k r: a skeleton has the written row r's place, number of rounds, length of oracles, told
  trees and list before. The name is not compared: in the description a block bears its place's name
  (the spots'), not the lot's.
links_written: lsW is 0, 1, …, 24.
blocks_count: k9SkW has 75 blocks.
blocks_places: no two of them stand at one place.
blocks_written: each of them passes its test on the plan (so none is a block that refuses, and K9's
  and K10's numbers fit), has neither claims nor runs behind the batching, and has a written row of
  cutFirstFull but for the name.
batch_written: at each l < 25 cutFirstFull has a row of kind K9 with one round in segment l, and at
  that row's place k9SkW supplies a batching that passes its test on the plan, is bare and has that
  row but for the name.

WHAT THE FACTS GIVE TOGETHER: 75 skeletons at 75 different places, each with a written row at its
  own place. By a count over the written table's text (a program; no Lean): its 358
  places all differ; it has 25 rows of kind K10, and 75 of kind K9: 25 with one round, 50 with none.
  A block's skeleton has 0, k + 2 or 0 rounds and the kinds K9, K10, K9: so it cannot meet a
  batching's row (kind K9, one round). So the 75 fall among the 50 + 25, and being 75 at different
  places they are all of them; the 25 batchings have the other 25: THAT LAST STEP IS A COUNT BY
  READING, NO THEOREM HERE.

Limits. THE FOUR HYPOTHESES ARE PREMISES: nothing here shows that they hold at any public files. WHO
  IS TO GIVE THEM, AS FAR AS SEEN HERE (pointers; none held): hs: that file's spots_written behind
  "Z.cuts is the written table of steps" · he: the ledger's premise on the plans, with a short law
  on the written rounds' entries that is not typed · hg, ht: no payer known here. lsW IS
  linksOf spotsWritten; back_of_skel_cut WANTS linksOf B.spots: THAT B.spots IS spotsWritten IS
  SOMEBODY's STEP (off the base's return and hs): not here. NOT SAID: the blocks' order · that the
  lot supplies no batching at another place (part 4 says both, against another written value) ·
  anything on back_of_skel_cut's own four Bools over all fifteen lots. THAT THE TESTS CAN SAY FALSE
  IS SHOWN BY NO LINE HERE. Written values of one set of public
  files, with synthetic weights. The full size alone. Nothing on soundness.
-/
import Johnson.AtFull.Desc.Lots.K9RowAt
import Johnson.AtFull.Desc.SpotsWritten
import Johnson.G.DryProofLit
import Johnson.Desc.ReqLit.Full
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc.Lots
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutFirstFull)
open ProofFile ProofFile.Sk

/-! ### one loop a stretch -/

/-- k entries off the list: the front (behind acc, which is turned), the rest, the count of roots.
-/
def splitE : Nat → List Fmt.Entry → Nat → List Fmt.Entry →
    List Fmt.Entry × List Fmt.Entry × Nat
  | 0, es, n, acc => (acc.reverse, es, n)
  | _ + 1, [], n, acc => (acc.reverse, [], n)
  | k + 1, e :: es, n, acc => Johnson.G.force (n + e.roots) fun m => splitE k es m (e :: acc)

theorem splitE_eq : ∀ (k : Nat) (es : List Fmt.Entry) (n : Nat) (acc : List Fmt.Entry),
    splitE k es n acc = (acc.reverse ++ es.take k, es.drop k, rootsE n (es.take k))
  | 0, es, n, acc => by
    simp [splitE, rootsE]
  | k + 1, [], n, acc => by
    simp [splitE, rootsE]
  | k + 1, e :: es, n, acc => by
    rw [splitE, Johnson.G.force_eq, splitE_eq k es]
    simp [rootsE, Johnson.G.force_eq]

/-- `stretchedE` over that loop. -/
def walkE : List Spot → List Fmt.Entry → Nat → XsE
  | [], _, _ => []
  | p :: ps, es, n =>
    match splitE (p.cuts.foldl (fun a c => a + c.take) 0) es n [] with
    | (front, rest, m) => (p, front, n) :: walkE ps rest m

theorem walk_eq : ∀ (ps : List Spot) (es : List Fmt.Entry) (n : Nat),
    stretchedE ps es n = walkE ps es n
  | [], _, _ => rfl
  | p :: ps, es, n => by
    rw [walkE, splitE_eq]
    show (p, es.take _, n) :: stretchedE ps (es.drop _) (rootsE n (es.take _)) =
      (p, [].reverse ++ es.take _, n) :: walkE ps (es.drop _) (rootsE n (es.take _))
    rw [walk_eq ps]
    rfl

/-! ### the written values -/

/-- The written first chain's entries. -/
def esW : List Fmt.Entry := Johnson.G.dryProofFull.1.map (·.1.entry)

/-- The written shape's groups. -/
def groupsW : Array OnBytes.ReqGroup := OnBytes.reqGroups VerifiableInference.Desc.ReqLit.shapeFull

/-- The written places' segments' numbers. -/
def lsW : List Nat := linksOf spotsWritten

/-- Each of the 25 segments has its sort and numbers. -/
def twW (l : Nat) : Bool := decide (l < 25)

/-- The written places with their stretches of entries. -/
def xsW : XsE := walkE spotsWritten esW 0

/-- **K9's lot's skeleton at the written values.** -/
def k9SkW : LotSk := k9SkE groupsW xsW twW

/-- **THE ROW AT THE WRITTEN VALUES.** -/
theorem k9_row_written (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW)
    (ht : ∀ l ∈ lsW, (K9.testsWhere Z.p.X l 0).isSome = twW l) :
    (lotSk G (k9Ninth Z)).cut lsW = k9SkW.cut lsW := by
  rw [k9_row_at Z G lsW hs he hg ht, walk_eq]
  rfl

/-! ### closed facts, against the written table of the first chain's cut -/

/-- A skeleton has the written row's five fields behind the name. -/
def rowButName (k : Skel)
    (r : String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) : Bool :=
  decide (k.place = r.2.1) && decide (k.nRounds = r.2.2.1) && decide (k.nOracles = r.2.2.2.1) &&
    decide (k.told = r.2.2.2.2.1) && decide (k.before = r.2.2.2.2.2)

theorem links_written : lsW = List.range 25 := by decide +kernel

theorem blocks_count : k9SkW.blocks.length = 75 := by decide +kernel

/-- No two of the blocks stand at one place. -/
theorem blocks_places : (k9SkW.blocks.map (·.place)).Nodup := by decide +kernel

/-- The test on the blocks. -/
def blocksB : Bool :=
  k9SkW.blocks.all fun k => k.planOk && k.bare && cutFirstFull.any fun r => rowButName k r

theorem blocks_written : blocksB = true := by decide +kernel

/-- The test on the batchings. -/
def batchB : Bool :=
  (List.range 25).all fun l =>
    cutFirstFull.any fun r =>
      r.2.1.kind == .K9 && r.2.1.link == some l && r.2.2.1 == 1 &&
        (k9SkW.batch r.2.1).any fun k => k.planOk && k.bare && rowButName k r

theorem batch_written : batchB = true := by decide +kernel

end Johnson.AtFull.Desc.Lots

#print axioms Johnson.AtFull.Desc.Lots.splitE_eq
#print axioms Johnson.AtFull.Desc.Lots.walk_eq
#print axioms Johnson.AtFull.Desc.Lots.k9_row_written
#print axioms Johnson.AtFull.Desc.Lots.links_written
#print axioms Johnson.AtFull.Desc.Lots.blocks_count
#print axioms Johnson.AtFull.Desc.Lots.blocks_places
#print axioms Johnson.AtFull.Desc.Lots.blocks_written
#print axioms Johnson.AtFull.Desc.Lots.batch_written
