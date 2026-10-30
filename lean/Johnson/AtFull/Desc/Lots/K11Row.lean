-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K11Row.lean: THE ROW OF THE MERGE's LOT (`K11.lot`,
Johnson/Desc/ProofFile/Lot/K11.lean: the merge of the claims on the committed table) FOR AN EXAMPLE
OF THE PROOF FILE's DESCRIPTION AT THE FULL SIZE: the lot's one block has the written skeleton,
under hypotheses by field on what the lot reads; and the closed facts at the written values, by
Lean's kernel. Definitions, statements and proofs.

What it says.
  The written table of steps is `Johnson.AtFull.Cut.cutWritten`
    (Johnson/AtFull/Cut/CutWrittenLit.lean, 477 rows). The written entries are `esWritten`
    (Johnson/AtFull/K4Sent/Written.lean).
  `sentOn cuts es look`: `K11.sentAt?` from the table of steps and the entries alone; `sentAt_eq`:
    the two are one, at every public part.
  `skel_blkAt`: the skeleton (`ProofFile.Sk.skel`, Johnson/Desc/ProofFile/Law/Skel/Skel.lean) of the lot's
    block, at every public part Z and all segments' records G. It reads four things: how many
    segments are built; the committed table's number of column bits; the plan's number of claims on
    that table; and how many trees the first chain's declared rounds send in front of the step that
    is looked for.
  `rowW`: the written skeleton. `k11_lot_row`: `((K11.lot Z).blocks G).map skel = rowW` where Z's
    table of steps and entries are the written ones, 25 segments are built, the table has 18 column
    bits and the plan has one claim. `k11_lotSk`, `k11_steady`: the same in the form of a lot's
    skeleton (`ProofFile.Sk.lotSk`, `ProofFile.Sk.Steady`).
  By the kernel: `sent_written`: at the written table of steps and entries 76 roots (trees) are sent
    in front of the step "H.8.call". ONE TEST that hangs on the written values and could have come
    out otherwise: `sent_earlier` (in front of "H.6.call": 75). THREE FACTS THAT ARE NO TESTS.
    `sent_oneLess` (one root less at the first entry that sends one: 75) follows from
    `sent_written`: `sentOn` adds the roots of the entries in front of the step, and since these
    send 76 the first entry that sends one stands among them. `sent_noStep` (the step struck from
    the table: none) follows from `sentOn`'s own text at every table; `sent_behind` (no root from
    that step on: 76 still: it looks in front alone) from that text and `sent_written`.
  By the kernel: `row_is_cut`: row number 346 of the written table `cutFirstFull`
    (Johnson/Desc/Ok/PlanWritten/CutLit.lean) is `rowW`'s member in that table's form (`Skel.row`),
    under the seat's name "H:9"; `row_alone`: no other row has that place; `row_not_75`,
    `row_not_21`, `row_not_named`: at a bent `rowW` the comparison says no: they show that
    `sameRows` reads these three fields, and no more: given `row_is_cut` they could not have come
    out otherwise unless it were blind to a field.

Limits. THAT ANY PUBLIC PART HAS THE WRITTEN TABLE OF STEPS AND ENTRIES, OR ANY RECORDS THE THREE
NUMBERS, IS SHOWN NOWHERE HERE: the five equations are premises: hc and he are also the premises of
`k4SentB_written` (Johnson/AtFull/K4Sent/Written.lean), and stay owed; hk and hn are fields of the
public parameters; hb, the number of built segments, hangs on the segments' maker: these three are
paid in the goals' scope in Johnson/AtFull/Desc/Lots/K11RowScope.lean, under four premises of its
own (hS, hR, hZ, hG). No law at an opening and none under the
proof file's pins is spent. THE ROW IS BLIND TO THE ROUNDS' ENTRIES AND TO THE DECISION: a skeleton
has the number of rounds, not the rounds; of the place's numbers work, nMsg and nLin enter these
alone. 76 does not pin the step: in front of "H.7.call" and "H.9.call" as many roots are sent. The
block's name in `rowW` is the kind's own; the written table's row bears its seat's name, which comes
of the places' list, not of the lot. Written values of one set of public files, with synthetic
weights. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Lot.K11
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.AtFull.K4Sent.Written
import Johnson.AtFull.Cut.CutWrittenLit
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K11Row

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (Cut)
open VerifiableInference.PlanWritten (cutFirstFull sameRows)
open OnBytes.Road.K4 (rootsOf rootsFrom_eq beforeAt)
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open ProofFile.Sk (Skel skel toldFrom LotSk lotSk Steady steady_none)

/-! ## 1 What the lot reads of the public part -/

/-- `K11.sentAt?`, from the table of steps and the entries. -/
def sentOn (cuts : List Cut) (es : List Fmt.Entry) (look : String) : Option Nat :=
  if cuts.any fun c => c.look == look then some (rootsOf (es.take (beforeAt cuts look))) else none

/-- **`K11.sentAt?` is its twin**, at every public part and every name. -/
theorem sentAt_eq (Z : ProofFile.Pub) (look : String) :
    K11.sentAt? Z look = sentOn Z.cuts (Z.D.1.map (·.entry)) look := by
  unfold K11.sentAt? sentOn ProofFile.Pub.roundsBefore?
  by_cases h : (Z.cuts.any fun c => c.look == look) = true
  · rw [if_pos h, if_pos h]
    show some ((Z.D.1.take (Z.roundsBefore look)).foldl (fun n r => n + r.entry.roots) 0) = _
    unfold rootsOf
    rw [rootsFrom_eq, ← List.map_take, List.foldl_map]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-! ## 2 The skeleton, in general -/

/-- Of a list of empty lists no member is told. -/
theorem told_replicate (n k : Nat) :
    toldFrom k (List.replicate n ([] : List VerifiableInference.Desc.Oracle)) = [] := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    show toldFrom (k + 1) _ = []
    exact ih (k + 1)

/-- **The skeleton of the lot's block**: what it reads of Z and G, by field. -/
theorem skel_blkAt (Z : ProofFile.Pub) (look : String) (G : ProofFile.Ground) :
    skel (K11.blkAt Z look G) =
      { name := "the merge of the claims on the weights"
        place := ⟨1, some (G.built.size - 1), 9, .K11⟩
        nRounds := G.W.layers.wsLay.lk + 4
        nOracles := G.W.layers.wsLay.lk + 4
        told := []
        before := (List.range ((K11.sentAt? Z look).getD 0)).map fun n => (1, n)
        planOk := (G.W.H.NCL == 1) && (K11.sentAt? Z look).isSome
        claims := ["the merge"]
        after := [] } := by
  have hr : (K11.blkAt Z look G).rounds.length = G.W.layers.wsLay.lk + 4 := by
    show ((Johnson.Desc.First.ForkMerge.mergeEntries G.W.layers.wsLay.lk 1 _).map _).length = _
    simp [Johnson.Desc.First.ForkMerge.mergeEntries]
  have ho : (K11.blkAt Z look G).oracles =
      List.replicate (G.W.layers.wsLay.lk + 4) [] := rfl
  unfold skel
  rw [hr, ho, told_replicate, List.length_replicate]
  rfl

/-! ## 3 The row -/

/-- **The written skeleton of the merge's lot's one block.** -/
def rowW : List Skel :=
  [{ name := "the merge of the claims on the weights"
     place := ⟨1, some 24, 9, .K11⟩
     nRounds := 22
     nOracles := 22
     told := []
     before := (List.range 76).map fun n => (1, n)
     planOk := true
     claims := ["the merge"]
     after := [] }]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the written values 76 roots (trees) are sent in front of the merge.** -/
theorem sent_written : sentOn cutWritten esWritten "H.8.call" = some 76 := by decide +kernel

/-- **THE ROW**: the lot returns one block, and its skeleton is the written one. -/
theorem k11_lot_row {Z : ProofFile.Pub} {G : ProofFile.Ground} (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) (hb : G.built.size = 25)
    (hk : G.W.layers.wsLay.lk = 18) (hn : G.W.H.NCL = 1) :
    ((K11.lot Z).blocks G).map skel = rowW := by
  have hs : K11.sentAt? Z "H.8.call" = some 76 := by
    rw [sentAt_eq, hc, he]
    exact sent_written
  show [skel (K11.blkAt Z "H.8.call" G)] = rowW
  rw [skel_blkAt, hs, hb, hk, hn]
  rfl

/-- The lot supplies no batching: so its batchings' skeletons hang on no gatherer. -/
theorem k11_steady (Z : ProofFile.Pub) (G : ProofFile.Ground) : Steady G (K11.lot Z) :=
  steady_none G (K11.lot Z) fun _ => rfl

/-- **The row, as a lot's skeleton.** -/
theorem k11_lotSk {Z : ProofFile.Pub} {G : ProofFile.Ground} (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) (hb : G.built.size = 25)
    (hk : G.W.layers.wsLay.lk = 18) (hn : G.W.H.NCL = 1) :
    lotSk G (K11.lot Z) =
      { name := "the merge of the weights' claims", letters := false, still := [], blocks := rowW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  unfold lotSk
  rw [k11_lot_row hc he hb hk hn]
  rfl

/-! ## 4 The count at other tables and entries, by the kernel -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No test: it follows from `sentOn`'s text at every table. Without the step in the table: none,
and so the block's test on the plan is false. -/
theorem sent_noStep :
    sentOn (cutWritten.filter fun c => c.look != "H.8.call") esWritten "H.8.call" = none := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- In front of an earlier step of the head's segment one tree less is sent: the count hangs on the
step that is looked for. -/
theorem sent_earlier : sentOn cutWritten esWritten "H.6.call" = some 75 := by decide +kernel

/-- The entries with one root less at the first entry that sends a root. -/
def esOneLess : List Fmt.Entry → List Fmt.Entry
  | [] => []
  | e :: es => if e.roots == 0 then e :: esOneLess es else { e with roots := e.roots - 1 } :: es

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- One root less in front: 75. -/
theorem sent_oneLess : sentOn cutWritten (esOneLess esWritten) "H.8.call" = some 75 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No test: it follows from `sentOn`'s text at every list. No root from the step on: 76 still: the
count looks in front alone. -/
theorem sent_behind :
    sentOn cutWritten
      (esWritten.zipIdx.map fun x =>
        if decide (beforeAt cutWritten "H.8.call" ≤ x.2) then { x.1 with roots := 0 } else x.1)
      "H.8.call" = some 76 := by
  decide +kernel

/-! ## 5 The written skeleton against the written table of the first chain -/

/-- `rowW`'s rows in the form of the written table (`Skel.row`), under the seat's name. -/
def rowsAs (name : String) (ks : List Skel) :
    List (String × Place × Nat × Nat × List (Nat × List VerifiableInference.Desc.Oracle) ×
      List (Nat × Nat)) :=
  ks.map fun k => ({ k with name := name } : Skel).row

set_option maxRecDepth 1000000 in
/-- **Row number 346 of the written table is `rowW`'s member, under the seat's name "H:9".** -/
theorem row_is_cut : sameRows ((cutFirstFull.drop 346).take 1) (rowsAs "H:9" rowW) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No other row has that place. -/
theorem row_alone :
    (cutFirstFull.filter fun r => decide (r.2.1 = ⟨1, some 24, 9, .K11⟩)).length = 1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison reads `before`: with one tree less it is not that row. -/
theorem row_not_75 :
    sameRows ((cutFirstFull.drop 346).take 1)
      (rowsAs "H:9" (rowW.map fun k => { k with before := (List.range 75).map fun n => (1, n) })) =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison reads the number of rounds: with one round less it is not that row. -/
theorem row_not_21 :
    sameRows ((cutFirstFull.drop 346).take 1)
      (rowsAs "H:9" (rowW.map fun k => { k with nRounds := 21 })) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The comparison reads the name: under the kind's own name it is not that row: the name is the
seat's. -/
theorem row_not_named :
    sameRows ((cutFirstFull.drop 346).take 1) (rowW.map Skel.row) = false := by decide +kernel

end Johnson.AtFull.Lots.K11Row

#print axioms Johnson.AtFull.Lots.K11Row.sentAt_eq
#print axioms Johnson.AtFull.Lots.K11Row.told_replicate
#print axioms Johnson.AtFull.Lots.K11Row.skel_blkAt
#print axioms Johnson.AtFull.Lots.K11Row.sent_written
#print axioms Johnson.AtFull.Lots.K11Row.k11_lot_row
#print axioms Johnson.AtFull.Lots.K11Row.k11_steady
#print axioms Johnson.AtFull.Lots.K11Row.k11_lotSk
#print axioms Johnson.AtFull.Lots.K11Row.sent_noStep
#print axioms Johnson.AtFull.Lots.K11Row.sent_earlier
#print axioms Johnson.AtFull.Lots.K11Row.sent_oneLess
#print axioms Johnson.AtFull.Lots.K11Row.sent_behind
#print axioms Johnson.AtFull.Lots.K11Row.row_is_cut
#print axioms Johnson.AtFull.Lots.K11Row.row_alone
#print axioms Johnson.AtFull.Lots.K11Row.row_not_75
#print axioms Johnson.AtFull.Lots.K11Row.row_not_21
#print axioms Johnson.AtFull.Lots.K11Row.row_not_named
