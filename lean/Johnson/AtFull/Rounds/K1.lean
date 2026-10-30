-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K1.lean: THE DECLARED ROUNDS OF THE LOT OF THE COMMITMENTS (`ProofFile.k1Pure`,
Johnson/Desc/ProofFile/Lots/PureLots.lean) ARE THE WRITTEN LISTS: each of the lot's 51
sub-protocols declares the list of rounds that the written table `listAt`
(Johnson/AtFull/Rounds/ListAt.lean) has under the written name of its place
(`nameW`, Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean). Definitions, statements
and proofs. It stands beside the lot's first row (Johnson/AtFull/Desc/Lots/K1/: Twin.lean,
Written.lean, View.lean), which has each sub-protocol's NUMBER of rounds; here are the rounds.

WHAT IS NOT PAID, FIRST. Two hypotheses by field are left: `hc` (the first chain's codes are the
written ones) and `hs` (its request's shape is the written one): they are two of the first row's
four, and like these TO BE PAID WITHOUT THE ENTRY TESTS' COMPARISONS. THE FIRST ROW's OTHER TWO
(the layout; the answers to a sample) ARE NOT WANTED HERE: no round reads them. THE WRITTEN NAMES:
hc stands at `Johnson.G.codesFull2`, hs at
`VerifiableInference.PlanWritten.proofSizedFull.request`, both on `G.first`, as in the first row;
other files' rows stand at other written names for the same values and on `Z.first`: NONE OF THESE
TIES IS HAD HERE. That the public part's maker returns anywhere (`hZ`, `hG`) is not shown. WHOEVER
JOINS THIS ROW to `ProofFile.Sk.Full.rows_by_place`, which runs over the lots of
`T.lots` and their sub-protocols at `B.G₀`, owes three equations: `B.G₀ = G`; that the member of
`T.lots` is `ProofFile.k1Pure` at this very Z; and that law's own `B.spots = spotsW`. WHAT THE TEST
CANNOT SEE, by its make: the sendings of one sort have one list at all segments, so the test does
not tell segment i from segment j: that the places are the right ones is said by `blocks_rd` and
`rd_places`, not by `rd_written`. The closed facts here are decided by Lean's kernel at
`ProofFile.Sk.Full.nameW` as Names.lean, over its Data.lean, has it.
Nothing on what a sub-protocol decides. No soundness is claimed. No example of the
head is shown in this file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth.

The road, in two steps.
(1) A law, at every public part Z and every ground G, nothing evaluated: the lot's sub-protocols'
    places and rounds are a function of the first chain's codes, its request's shape and the 25
    views of the first row. The layout, the plan's two numbers, the arrays and the quiet step's
    test on the plan, which the first row reads, are NOT read by a round.
      `PR`, `pr`   a sub-protocol's place and its declared rounds
      `laterRd`, `firstRd`, `segRd`, `k1Rd`   THE TWIN
      `pr_laterAt`, `pr_firstAtS`, `pr_retype` (by rfl); `pr_andThen`: a step without a round, laid
          behind, adds none and leaves the place. The law has no premise, so it holds too where no
          quiet step is found and the lot lays the sub-protocol that refuses: `quietOf_bare`
          (Twin.lean) is stated of whatever stands there, that one too
      `seg_rd`, `blocks_rd`   **MAIN: the lot's places and rounds are the twin's**
      `first_gp`, `later_gp`, `k1Rd_congr`   what the twin reads
      `k1Rd_places`   its places read the views alone
(2) Closed facts at the written values (`qW`, `gpW`, `viewW`, Written.lean), by Lean's kernel, each
    looked at with the evaluator first.
      `rdB N xs`   the test: each member's rounds are `listAt` of the name that N gives its place
      `rd_written`   **all 51 pass at `nameW`**
      `rd_size`   there are 51, each of two rounds, and four different lists among them
      `rd_places`   **the 51 places, with their written names, in their order, are those of the
          written cut's rows of the kind K1 inside a link** (`k1Rows`, Written.lean); no name stands
          twice: so no two members share a place, and none stands at another kind's row;
          `rd_places_bites`: it can fail
      `rd_names`   the first five members' written names: the four different lists stand at
          members 0, 1, 2 and 4
      `rdBut`; `rd_first_bites`, `rd_reads_bites`, `rd_digits_bites`, `rd_att_bites`   NEGATIVE
          TESTS, stated positively: for each of the four different lists, one member's rounds
          exchanged for another written list OF THE SAME LENGTH: the test rejects
      `rd_swap_bites`, `rd_name_bites`   a segment's two pieces exchanged in the maker's input;
          every place under one name: the test rejects
  `rounds_of_test`   from a yes of the test to each sub-protocol
  `k1_rounds_at`   from hypotheses by field
  `k1_length_in_scope`   **the lot has 51 sub-protocols**: in the goals' scope, behind the front's
      return, under no further hypothesis: so the row's "for each" is not idle
  `k1_rounds_in_scope`   **UNDER hc AND hs, in the goals' scope, behind the front's return:
      b.rounds = listAt (nameW b.place)**; `k1_lst_in_scope`: the same in the form that
      `ProofFile.Sk.Full.rows_by_place` uses (`Lst`, Johnson/Desc/ProofFile/Law/Skel/SkelLists.lean)

-/
import Johnson.AtFull.Desc.Lots.K1.View
import Johnson.AtFull.Rounds.ListAt
import Johnson.Desc.ProofFile.Law.Skel.SkelLists
import Johnson.Desc.ProofFile.Law.Skel.Full.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Rounds.K1

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open _root_.Desc.Plain (GPar)
open VerifiableInference.Desc.K1 (parLater firstPar laterAt firstSegmentOpening linkNumbers gpOf
  parLater_congr firstPar_congr)
open ProofFile (Ground Pub Cl)
open ProofFile.Sk.Full (nameW)
open Johnson.AtFull.Desc.K1Lot (View segView quietOf Bare quietOf_bare qW gpW viewW viewBut k1Rows
  view_in_scope)

/-! ## 1 The law: what a round of the lot reads -/

/-- A place and the rounds declared there. -/
abbrev PR : Type := Place × List Fmt.DeclaredRound

/-- A sub-protocol's place and its declared rounds. -/
def pr {C : Type} (b : Block S C) : PR := (b.place, b.rounds)

/-- A segment's later sending. -/
def laterRd (q : Params.First) (gp : GPar) (l piece m : ℕ) : PR :=
  (⟨1, some l, piece, .K1⟩, VerifiableInference.Desc.K1.rounds (parLater q gp l piece m))

/-- The first segment's opening. -/
def firstRd (q : Params.First) (gp : GPar) : PR :=
  (⟨1, some 0, 1, .K1⟩, VerifiableInference.Desc.K1.rounds (firstPar q gp))

theorem pr_laterAt (q : Params.First) (gp : GPar) (l piece m : ℕ) (arrays : Option (List ℕ)) :
    pr (laterAt q gp l piece m arrays : Block S Unit) = laterRd q gp l piece m := rfl

theorem pr_firstAtS (q : Params.First) (gp : GPar) :
    pr (firstSegmentOpening q gp : Block S Unit) = firstRd q gp := rfl

theorem pr_retype {C C' : Type} (b : Block S C) : pr (b.retype : Block S C') = pr b := rfl

/-- A step without a round, laid behind, adds none; the place is the first one's. -/
theorem pr_andThen (n : String) (p : Block S Unit) {z : Block S Unit} (hz : Bare z) :
    pr (p.andThen n z) = pr p := by
  show (p.place, p.rounds ++ z.rounds) = (p.place, p.rounds)
  rw [hz.1, List.append_nil]

/-- A segment's two members: of its view the two pieces alone are read. -/
def segRd (q : Params.First) (gp : GPar) (l : ℕ) : Option View → List PR
  | none => []
  | some v => [laterRd q gp l v.1 1, laterRd q gp l v.2.1 2]

/-- **The lot's places and rounds, of what they read.** -/
def k1Rd (q : Params.First) (gp : GPar) (vs : List (ℕ × Option View)) : List PR :=
  firstRd q gp :: vs.flatMap fun y => segRd q gp y.1 y.2

/-- One segment. -/
theorem seg_rd (Z : Pub) (G : Ground) (X : LinkH) (l : ℕ) :
    ((match linkNumbers G X with
      | none => ([] : List (Block S Unit))
      | some (p1, pd, reads, digits) =>
        [(laterAt G.first (gpOf Z) l p1 1 reads : Block S Unit).andThen
            (laterAt G.first (gpOf Z) l p1 1 reads : Block S Unit).name (quietOf G l X),
         laterAt G.first (gpOf Z) l pd 2 digits]).map
      fun (b : Block S Unit) => pr (b.retype : Block S Cl)) =
      segRd G.first (gpOf Z) l (segView G (X, l)) := by
  unfold segView
  cases h : linkNumbers G X with
  | none => rfl
  | some n =>
    obtain ⟨p1, pd, reads, digits⟩ := n
    simp only [List.map_cons, List.map_nil, pr_retype, pr_andThen _ _ (quietOf_bare G l X),
      pr_laterAt, Option.map_some]
    rfl

/-- **AT EVERY PUBLIC PART AND EVERY GROUND: the lot's places and rounds are the twin's.** -/
theorem blocks_rd (Z : Pub) (G : Ground) :
    ((ProofFile.k1Pure Z).blocks G).map pr =
      k1Rd G.first (gpOf Z) (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) := by
  show (((VerifiableInference.Desc.K1.blocks (gpOf Z) (fun G l X => some (quietOf G l X)) G).map
    fun (b : Block S Unit) => (b.retype : Block S Cl)) ++ []).map pr = _
  rw [List.append_nil, List.map_map]
  unfold VerifiableInference.Desc.K1.blocks k1Rd
  simp only [List.map_cons, List.singleton_append, List.map_flatMap, List.flatMap_map,
    Function.comp_apply, pr_retype, pr_firstAtS]
  congr 1
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨X, l⟩ := x
  exact seg_rd Z G X l

/-- No round reads the plan's two numbers. -/
theorem first_gp (q : Params.First) (gp gp' : GPar) : firstRd q gp = firstRd q gp' := rfl

theorem later_gp (q : Params.First) (gp gp' : GPar) (l piece m : ℕ) :
    laterRd q gp l piece m = laterRd q gp' l piece m := rfl

/-- **Of the first chain's parameters the twin reads the codes and the request's shape alone; of
the plan's two numbers, neither.** -/
theorem k1Rd_congr {q q' : Params.First} (hc : q.codes = q'.codes) (hs : q.shape = q'.shape)
    (gp gp' : GPar) (vs : List (ℕ × Option View)) : k1Rd q gp vs = k1Rd q' gp' vs := by
  have e1 : firstRd q gp = firstRd q' gp' := by
    rw [first_gp q gp gp']
    unfold firstRd
    rw [firstPar_congr hc hs]
  have e2 : ∀ l piece m, laterRd q gp l piece m = laterRd q' gp' l piece m := by
    intro l piece m
    rw [later_gp q gp gp']
    unfold laterRd
    rw [parLater_congr hc hs]
  have e3 : ∀ l v, segRd q gp l v = segRd q' gp' l v := by
    intro l v
    cases v with
    | none => rfl
    | some v => simp only [segRd, e2]
  unfold k1Rd
  simp only [e1, e3]

/-- The twin's places read the views alone. -/
theorem k1Rd_places (q q' : Params.First) (gp gp' : GPar) (vs : List (ℕ × Option View)) :
    (k1Rd q gp vs).map (·.1) = (k1Rd q' gp' vs).map (·.1) := by
  have e3 : ∀ l v, (segRd q gp l v).map (·.1) = (segRd q' gp' l v).map (·.1) := by
    intro l v
    cases v <;> rfl
  unfold k1Rd
  rw [List.map_cons, List.map_cons, List.map_flatMap, List.map_flatMap]
  congr 1
  exact List.flatMap_congr fun y _ => e3 y.1 y.2

/-! ## 2 The test, and from its yes to each sub-protocol -/

/-- The test: each member's rounds are the written list under the name that N gives its place. -/
def rdB (N : Place → String) (xs : List PR) : Bool :=
  xs.all fun x => decide (Johnson.AtFull.Rounds.listAt (N x.1) = x.2)

theorem rounds_of_test {N : Place → String} {xs : List PR} (h : rdB N xs = true) {C : Type}
    {bs : List (Block S C)} (e : bs.map pr = xs) :
    ∀ b ∈ bs, b.rounds = Johnson.AtFull.Rounds.listAt (N b.place) := by
  intro b hb
  have hm : pr b ∈ xs := by
    rw [← e]
    exact List.mem_map_of_mem hb
  exact (of_decide_eq_true (List.all_eq_true.1 h _ hm)).symm

/-! ## 3 Closed facts at the written values -/

set_option maxRecDepth 1000000 in
/-- **BY LEAN's KERNEL: at the written values each of the 51 members' rounds are the written list
under the written name of its place.** -/
theorem rd_written : rdB nameW (k1Rd qW gpW viewW) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 51; each has two rounds; four different lists are among them. With `rd_written`: at
each of the 51 the table's list has two rounds, so each of the 51 names is one that the table knows:
"the empty list under an unknown name" passes nowhere. The third clause is what lets the negative
tests be: a table with one list everywhere would not have it. -/
theorem rd_size : (k1Rd qW gpW viewW).length = 51 ∧
    ((k1Rd qW gpW viewW).all fun x => x.2.length == 2) = true ∧
    ((k1Rd qW gpW viewW).map (·.2)).eraseDups.length = 4 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **BY LEAN's KERNEL: the 51 places with their written names, in their order, are those of the
written cut's rows of the kind K1 inside a link; and no name stands twice among them.** (The written
cut has a 52nd row of the kind, "M:4", outside the links: another lot's.) -/
theorem rd_places : (k1Rd qW gpW viewW).map (fun x => (nameW x.1, x.1)) =
      k1Rows.map (fun r => (r.1, r.2.1)) ∧ (k1Rows.map (·.1)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: with segment 5's two pieces exchanged the order of the places is another. -/
theorem rd_places_bites :
    decide ((k1Rd qW gpW (viewBut 5 (some (6, 4, true, true, true)))).map
      (fun x => (nameW x.1, x.1)) = k1Rows.map (fun r => (r.1, r.2.1))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The first five members' written names: the opening; segment 0 (layers): reads, digits; segment 1
(attention): reads, digits. -/
theorem rd_names : ((k1Rd qW gpW viewW).take 5).map (fun x => nameW x.1) =
    ["G0:1", "G0:4", "G0:6", "A0:4", "A0:6"] := by decide +kernel

/-! ## 4 The test can fail -/

/-- The list with the rounds of member number i exchanged for r. -/
def rdBut (i : ℕ) (r : List Fmt.DeclaredRound) (xs : List PR) : List PR :=
  xs.zipIdx.map fun y => if y.2 == i then (y.1.1, r) else y.1

set_option maxRecDepth 1000000 in
/-- Member 0, "G0:1" (the first segment's opening), gets the list of "G0:4" (a sending of reads). -/
theorem rd_first_bites : rdB nameW (rdBut 0 (Johnson.AtFull.Rounds.listAt "G0:4")
    (k1Rd qW gpW viewW)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Member 1, "G0:4" (a sending of reads), gets the list of "G0:6" (a layers' segment's digits): the
second round is the same, the first differs. -/
theorem rd_reads_bites : rdB nameW (rdBut 1 (Johnson.AtFull.Rounds.listAt "G0:6")
    (k1Rd qW gpW viewW)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Member 2, "G0:6" (a layers' segment's digits), gets the list of "A0:6" (an attention segment's).
-/
theorem rd_digits_bites : rdB nameW (rdBut 2 (Johnson.AtFull.Rounds.listAt "A0:6")
    (k1Rd qW gpW viewW)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Member 4, "A0:6" (an attention segment's digits), gets the list of "G0:6" (a layers' segment's).
-/
theorem rd_att_bites : rdB nameW (rdBut 4 (Johnson.AtFull.Rounds.listAt "G0:6")
    (k1Rd qW gpW viewW)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- In the maker's input: segment 5's two pieces exchanged. Why it bites: of `parLater q gp link
piece moment` the piece goes into the field `place` alone (Johnson/Desc/K1/Places.lean:62), which no
round reads; the moment goes into `parts` (:63), which both rounds read
(Johnson/Desc/K1/Send.lean:122, :126). So the reads' rounds come to stand at the place that bears
the digits' name, and the other way round: two members fail. -/
theorem rd_swap_bites :
    rdB nameW (k1Rd qW gpW (viewBut 5 (some (6, 4, true, true, true)))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Every place under the name of the first sending of reads. -/
theorem rd_name_bites : rdB (fun _ => "G0:4") (k1Rd qW gpW viewW) = false := by decide +kernel

/-! ## 5 The row -/

/-- **The lot's second row, from hypotheses by field.** hc and hs are to be paid WITHOUT the entry
tests' comparisons. -/
theorem k1_rounds_at {Z : Pub} {G : Ground} (hc : G.first.codes = Johnson.G.codesFull2)
    (hs : G.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request)
    (hv : (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) = viewW) :
    ∀ b ∈ (ProofFile.k1Pure Z).blocks G,
      b.rounds = Johnson.AtFull.Rounds.listAt (nameW b.place) := by
  refine rounds_of_test rd_written ?_
  rw [blocks_rd, hv]
  exact k1Rd_congr (q' := qW) hc hs _ _ _

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : Pub} {G : Ground}

/-- **The lot has 51 sub-protocols**: in the goals' scope, behind the front's return; neither hc nor
hs is wanted. So "for each sub-protocol of the lot" is not idle. -/
theorem k1_length_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    ((ProofFile.k1Pure Z).blocks G).length = 51 := by
  have h := congrArg List.length (blocks_rd Z G)
  rw [view_in_scope hS hR hZ hG] at h
  have e := congrArg List.length (k1Rd_places G.first qW (gpOf Z) gpW viewW)
  simp only [List.length_map] at h e
  rw [h, e]
  exact rd_size.1

/-- **UNDER hc AND hs, WHICH NOTHING HERE PAYS: the lot's second row in the goals' scope, behind the
front's return**: each sub-protocol of the lot declares the written list under the written name of
its place. -/
theorem k1_rounds_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (hc : G.first.codes = Johnson.G.codesFull2)
    (hs : G.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request) :
    ∀ b ∈ (ProofFile.k1Pure Z).blocks G,
      b.rounds = Johnson.AtFull.Rounds.listAt (nameW b.place) :=
  k1_rounds_at hc hs (view_in_scope hS hR hZ hG)

/-- **UNDER hc AND hs, WHICH NOTHING HERE PAYS: the same in the form that the law on the rounds'
column uses** (`ProofFile.Sk.Full.rows_by_place`'s `w`, at this lot and this ground). -/
theorem k1_lst_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (hc : G.first.codes = Johnson.G.codesFull2)
    (hs : G.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request) :
    ∀ b ∈ (ProofFile.k1Pure Z).blocks G,
      ProofFile.Sk.Lst Johnson.AtFull.Rounds.listAt (nameW b.place) b.rounds :=
  fun b hb => Or.inr (k1_rounds_in_scope hS hR hZ hG hc hs b hb)

end

end Johnson.AtFull.Rounds.K1

#print axioms Johnson.AtFull.Rounds.K1.pr_laterAt
#print axioms Johnson.AtFull.Rounds.K1.pr_firstAtS
#print axioms Johnson.AtFull.Rounds.K1.pr_retype
#print axioms Johnson.AtFull.Rounds.K1.pr_andThen
#print axioms Johnson.AtFull.Rounds.K1.seg_rd
#print axioms Johnson.AtFull.Rounds.K1.blocks_rd
#print axioms Johnson.AtFull.Rounds.K1.first_gp
#print axioms Johnson.AtFull.Rounds.K1.later_gp
#print axioms Johnson.AtFull.Rounds.K1.k1Rd_congr
#print axioms Johnson.AtFull.Rounds.K1.k1Rd_places
#print axioms Johnson.AtFull.Rounds.K1.rounds_of_test
#print axioms Johnson.AtFull.Rounds.K1.rd_written
#print axioms Johnson.AtFull.Rounds.K1.rd_size
#print axioms Johnson.AtFull.Rounds.K1.rd_places
#print axioms Johnson.AtFull.Rounds.K1.rd_places_bites
#print axioms Johnson.AtFull.Rounds.K1.rd_names
#print axioms Johnson.AtFull.Rounds.K1.rd_first_bites
#print axioms Johnson.AtFull.Rounds.K1.rd_reads_bites
#print axioms Johnson.AtFull.Rounds.K1.rd_digits_bites
#print axioms Johnson.AtFull.Rounds.K1.rd_att_bites
#print axioms Johnson.AtFull.Rounds.K1.rd_swap_bites
#print axioms Johnson.AtFull.Rounds.K1.rd_name_bites
#print axioms Johnson.AtFull.Rounds.K1.k1_rounds_at
#print axioms Johnson.AtFull.Rounds.K1.k1_length_in_scope
#print axioms Johnson.AtFull.Rounds.K1.k1_rounds_in_scope
#print axioms Johnson.AtFull.Rounds.K1.k1_lst_in_scope
