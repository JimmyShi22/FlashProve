-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K8Row.lean: THE ROW OF THE SMALLNESS TEST's LOT (ProofFile.P1K8.lot,
Johnson/Desc/ProofFile/Lot/K8.lean) FOR AN EXAMPLE OF THE HEAD BY LEAN's KERNEL: the lot's blocks'
skeletons (ProofFile.Sk.skel, Johnson/Desc/ProofFile/Law/Skel/Skel.lean) are the written ones, under
hypotheses by field on what the lot reads of the public part Z and of the ground G. After the
pattern for the lot of K4 (Johnson/Road/K4/K4FromSk.lean, Johnson/AtFull/K4Sent/Rows.lean).
NO SUB-PROTOCOL IMPORTS THIS FILE.
THE LOT HAS NO OPTION IN IT: it lays one block for each built link: «the lot returns» is by
definition. A refusal can hide in a block's test on the plan alone, and that test is seven tests on
numbers.
  k8StepsFrom       ONE WALK over the table of steps, taking each step's rounds off the entries: of
                    each step its name, the roots in front of it and the roots in it
  k8MsgsTab         ProofFile.k8Msgs as a look-up in that table
  k8Steps_find · k8Msgs_eq   LAWS AT ALL LETTERS
  k8PreB · k8LenB · k8AsksB · k8GroundB   what the test on the plan reads beside the steps: see
                    below
  k8PreOn_bent · k8AsksOn_bent   each of the two can fail: one bent number: false
  k8RowOn           a block's skeleton, from plain data
  k8Skel_par · k8Skel_whole · k8Lot_skel   LAWS AT ALL LETTERS: no hypothesis
  k8KindsW · k8TabW   the 25 written pairs (kind, name); the walk at the written values
  k8RowsW           THE WRITTEN ROWS: A NAMED CLOSED LIST, CUT FROM THE WRITTEN TABLE of the first
                    chain's sub-protocols (cutFirstFull, Johnson/Desc/Ok/PlanWritten/CutLit.lean):
                    its 25 rows at 14 l + 6 | 343: place, counts, told rounds and «before» as they
                    stand there; the kind's own name, a yes on the plan and the three runs' names
  k8RowsW_names     25 rows; the written table's rows there bear the spots' names, of kind K8
  k8Rows_written    BY THE KERNEL: the rows made at the written values ARE k8RowsW
  k8Rows_noStep · k8Rows_noEntry · k8Rows_notPre   three negative tests, by the kernel, that cannot
                    but refuse: the test is idle nowhere
  k8Rows_rootMore · k8Rows_swapped   two on WELL-FORMED WRONG DATA (every row's own test on the
                    plan still says true): the comparison bites
  k8Rows_ownName    the written table's rows do NOT bear the blocks' own name
  k8_row_at         THE ROW, on the blocks' skeletons
  k8_lotSk_at · k8_steady   the row on the lot's skeleton (ProofFile.Sk.lotSk); the lot has no batching
WHAT THE LOT READS, BY FIELD. OF A BUILT LINK X (a member of G.built): kind · name · g · tl.mats (of
each matrix k and m) · tl.tau. OF G.W, through ProofFile.k8Asks: hS (X.kind = 2) · A[X.g]'s S (X.kind = 1)
· y and layers.rd (else). OF Z: cuts · D.1's entries' numbers of roots. (Also nU, of G.W.H | A | G:
it goes into a function behind the batching, of which a skeleton has the name alone.) k8PreB X
reads X.tl.mats' k and X.tl.tau; k8LenB X reads X.tl.mats and is true by a law; k8AsksB G X reads
what k8Asks reads. WHETHER G.built's MEMBERS ARE THE PLANNER's OWN RECORDS OR SOMETHING MADE OF THEM
IS NOT ASKED HERE: the tests stand at G.built's members as they are.
THE HYPOTHESES. hc · he: Z's table of steps and the first chain's entries are the written ones:
cutWritten is Johnson.AtFull.Cut.cutWritten (Johnson/AtFull/Cut/CutWrittenLit.lean: the
final constant), esWritten is Johnson.AtFull.K4Sent.esWritten (Johnson/AtFull/K4Sent/Written.lean) ·
hk: the 25 built links' kinds and names are the written ones · hn: k8GroundB G: at each built link
k8PreB and k8AsksB say true. NO OPENING OF THE MAKER, NO SCOPE, NO PINNED ENTRY TEST; nothing on how
G was made.
THE NAME COLUMN. A block of this lot bears the kind's own name; the written table's row at its place
bears the spot's name («G0:5» … «A11:5», «H:6»), which the maker lays over it. So k8RowsW, the lot's
own skeletons, has the kind's name.
That the maker lays the spot's name is not shown here.
WHAT A SKELETON DOES NOT HOLD. The round's own declaration ({ name := "RNG", trits := columns * tau
}): a skeleton has how many rounds, not which: so ks and tau enter the block there too, and this row
does not fix the number of trits. The comparison of the declared rounds does (the entry tests' first
row).
LIMITS. Closed facts on written values of one set of public files, with synthetic weights. THE
WRITTEN TABLE WAS PRINTED OFF THIS VERY LOT's BLOCKS: IT IS NO INDEPENDENT WITNESS. That any Z and G
meet the four hypotheses is shown nowhere here. hn is ONE FENCED TEST over some ten fields of G, not
an equation with written values: the kernel can pay it only at a closed G. ProofFile.k8Asks has a default
(getD []) at attention: a link without a family passes k8AsksB (the lot's own text). No soundness is
claimed.
-/
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Road.K4.K4SentAt
import Johnson.AtFull.K4Sent.Written
import Johnson.AtFull.Cut.CutWrittenLit
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8L
open VerifiableInference.Desc.First (Cut K8.whole)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Road.K4 (rootsOf rootsFrom_eq beforeAt k4Roots_eq)
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open VerifiableInference.PlanWritten (cutFirstFull)
open ProofFile.Sk (Skel skel lotSk Steady steady_none)

/-! ### sums -/

theorem k8Foldl_shift {α : Type} (g : α → Nat) (l : List α) :
    ∀ a, l.foldl (fun n x => n + g x) a = a + l.foldl (fun n x => n + g x) 0 := by
  induction l with
  | nil => intro a; rfl
  | cons x l ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih (a + g x), ih (0 + g x)]
    omega

theorem k8RootsOf_eq (es : List Fmt.Entry) : rootsOf es = es.foldl (fun a e => a + e.roots) 0 :=
  rootsFrom_eq es 0

theorem k8RootsOf_append (a b : List Fmt.Entry) : rootsOf (a ++ b) = rootsOf a + rootsOf b := by
  rw [k8RootsOf_eq, k8RootsOf_eq, k8RootsOf_eq, List.foldl_append,
    k8Foldl_shift (fun e : Fmt.Entry => e.roots)]

theorem k8RootsOf_take_add (es : List Fmt.Entry) (n t : Nat) :
    rootsOf (es.take (n + t)) = rootsOf (es.take n) + rootsOf ((es.drop n).take t) := by
  rw [List.take_add, k8RootsOf_append]

/-- The count of roots in front of round k reads the entries alone. -/
theorem k8Roots_take (l : List Fmt.DeclaredRound) (k : Nat) :
    (l.take k).foldl (fun a r => a + r.entry.roots) 0 = rootsOf ((l.map (·.entry)).take k) := by
  rw [← List.map_take, ← k4Roots_eq]
  rfl

theorem k8Before_cons (c : Cut) (cs : List Cut) (look : String) :
    beforeAt (c :: cs) look = if c.look != look then c.take + beforeAt cs look else 0 := by
  unfold beforeAt
  rw [List.takeWhile_cons]
  split
  · rw [List.foldl_cons, k8Foldl_shift (fun c : Cut => c.take)]
    omega
  · rfl

/-! ### one walk over the table of steps -/

/-- Of each step: its name, the roots in front of it, the roots in it. r: the roots so far. -/
def k8StepsFrom : List Cut → List Fmt.Entry → Nat → List (String × Nat × Nat)
  | [], _, _ => []
  | c :: cs, es, r =>
    Johnson.G.force (rootsOf (es.take c.take)) fun d =>
      Johnson.G.force (r + d) fun r' => (c.look, r, d) :: k8StepsFrom cs (es.drop c.take) r'

/-- **What the walk has at a step's name.** -/
theorem k8Steps_find (look : String) : ∀ (cuts : List Cut) (es : List Fmt.Entry) (r : Nat),
    (k8StepsFrom cuts es r).find? (·.1 == look) =
      (cuts.find? (·.look == look)).map fun c =>
        (c.look, r + rootsOf (es.take (beforeAt cuts look)),
          rootsOf ((es.drop (beforeAt cuts look)).take c.take))
  | [], _, _ => rfl
  | c :: cs, es, r => by
    rw [k8StepsFrom, Johnson.G.force_eq, Johnson.G.force_eq, List.find?_cons, List.find?_cons,
      k8Before_cons]
    by_cases h : (c.look == look) = true
    · have h' : (c.look != look) = false := by rw [bne, h]; rfl
      simp only [h, h']
      show some (c.look, r, rootsOf (es.take c.take)) =
        some (c.look, r + rootsOf (es.take 0), rootsOf ((es.drop 0).take c.take))
      rw [List.take_zero, List.drop_zero]
      rfl
    · have h0 : (c.look == look) = false := by simpa using h
      have h' : (c.look != look) = true := by rw [bne, h0]; rfl
      simp only [h0, h']
      rw [k8Steps_find look cs (es.drop c.take) (r + rootsOf (es.take c.take))]
      simp only [if_true, k8RootsOf_take_add, List.drop_drop, Nat.add_assoc]

/-- `ProofFile.k8Msgs`, as a look-up in the walk's table. -/
def k8MsgsTab (tab : List (String × Nat × Nat)) (look : String) : List Nat :=
  match tab.find? (·.1 == look) with
  | some x => (List.range x.2.2).map (· + x.2.1)
  | none => []

/-- **`ProofFile.k8Msgs` is that look-up**, at every public part and every name. -/
theorem k8Msgs_eq (Z : ProofFile.Pub) (look : String) :
    ProofFile.k8Msgs Z look = k8MsgsTab (k8StepsFrom Z.cuts (Z.D.1.map (·.entry)) 0) look := by
  unfold k8MsgsTab
  rw [k8Steps_find]
  unfold ProofFile.k8Msgs ProofFile.Pub.roundsBefore?
  cases hf : Z.cuts.find? (·.look == look) with
  | none => rfl
  | some c =>
    have h : (Z.cuts.any fun c => c.look == look) = true :=
      List.any_eq_true.2 ⟨c, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
    rw [if_pos h]
    show (List.range ((Z.D.1.take (beforeAt Z.cuts look + c.take)).foldl _ 0 -
      (Z.D.1.take (beforeAt Z.cuts look)).foldl _ 0)).map
        (· + (Z.D.1.take (beforeAt Z.cuts look)).foldl _ 0) =
      (List.range (rootsOf (((Z.D.1.map (·.entry)).drop (beforeAt Z.cuts look)).take c.take))).map
        (· + (0 + rootsOf ((Z.D.1.map (·.entry)).take (beforeAt Z.cuts look))))
    rw [k8Roots_take, k8Roots_take, k8RootsOf_take_add, Nat.add_sub_cancel_left, Nat.zero_add]

/-! ### what the test on the plan reads of G -/

/-- Of the test on the plan, on plain numbers: there is a matrix, a column and a combination. -/
def k8PreOn (ks : List Nat) (tau : Nat) : Bool :=
  !ks.isEmpty && ks.foldl (· + ·) 0 != 0 && tau != 0

/-- The same at a built link: it reads X.tl.mats (each matrix's k) and X.tl.tau. -/
def k8PreB (X : LinkH) : Bool := k8PreOn (X.tl.mats.toList.map (·.k)) X.tl.tau

/-- It can fail: no matrix; no column; no combination. -/
theorem k8PreOn_bent :
    k8PreOn [3, 4] 160 = true ∧ k8PreOn [] 160 = false ∧ k8PreOn [0, 0] 160 = false ∧
      k8PreOn [3, 4] 0 = false := by decide

/-- Of the test on the plan: as many numbers of rows as of columns. -/
def k8LenB (X : LinkH) : Bool :=
  (X.tl.mats.toList.map (·.m)).length == (X.tl.mats.toList.map (·.k)).length

theorem k8LenB_true (X : LinkH) : k8LenB X = true := by
  unfold k8LenB
  rw [List.length_map, List.length_map]
  exact beq_self_eq_true _

/-- Of the test on the plan, on plain numbers: no family of tables is empty or sums over no row. -/
def k8AsksOn (asks : List (Nat × Nat × Nat)) : Bool := asks.all fun a => a.2.1 != 0 && a.2.2 != 0

/-- The same at a built link: it reads ProofFile.k8Asks G X: X.kind, X.g, and of G.W: hS at the head;
A[X.g]'s S at attention; y and layers.rd at the layers. -/
def k8AsksB (G : ProofFile.Ground) (X : LinkH) : Bool := k8AsksOn (ProofFile.k8Asks G X)

/-- It can fail: an empty family; a family that sums over no row. -/
theorem k8AsksOn_bent :
    k8AsksOn [(0, 2, 8)] = true ∧ k8AsksOn [(0, 0, 8)] = false ∧ k8AsksOn [(0, 2, 0)] = false := by
  decide

/-- **The one test on G**: at each built link both say true. -/
def k8GroundB (G : ProofFile.Ground) : Bool := G.built.toList.all fun X => k8PreB X && k8AsksB G X

/-! ### skeletons -/

/-- **A block's skeleton, from plain data.** -/
def k8RowOn (tab : List (String × Nat × Nat)) (kind : Nat) (name : String)
    (pre len asks : Bool) (l : Nat) : Skel :=
  { name := "the smallness test: the draw of the matrix"
    place := ⟨1, some l, if kind == 2 then 6 else 5, .K8⟩
    nRounds := 1
    nOracles := 1
    told := []
    before := (k8MsgsTab tab (name ++ (if kind == 2 then ".1.call" else ".0.call")) ++
      k8MsgsTab tab (name ++ (if kind == 2 then ".4.call" else ".3.call"))).map fun n => (1, n)
    planOk := pre &&
      !(k8MsgsTab tab (name ++ (if kind == 2 then ".1.call" else ".0.call"))).isEmpty &&
      !(k8MsgsTab tab (name ++ (if kind == 2 then ".4.call" else ".3.call"))).isEmpty && len &&
      asks
    claims := ["K8.equations"]
    after := ["K8.lsTail", "K8.tests"] }

/-- The skeleton of the kind's block, at a place's numbers. -/
theorem k8Skel_par (p : VerifiableInference.Desc.First.K8.ParW) :
    skel (K8.whole p) =
      { name := "the smallness test: the draw of the matrix"
        place := ⟨1, some p.link, p.piece, .K8⟩
        nRounds := 1
        nOracles := 1
        told := []
        before := (p.matsIn ++ p.readsIn).map fun n => (1, n)
        planOk := !p.ks.isEmpty && VerifiableInference.Desc.First.K8.columns p.toPar != 0 &&
          p.tau != 0 && !p.matsIn.isEmpty && !p.readsIn.isEmpty && p.ms.length == p.ks.length &&
          p.asks.all fun a => a.2.1 != 0 && a.2.2 != 0
        claims := ["K8.equations"]
        after := ["K8.lsTail", "K8.tests"] } := rfl

/-- **The skeleton of the lot's block at a built link**, at all letters. -/
theorem k8Skel_whole (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : LinkH) (l : Nat) :
    skel (K8.whole (ProofFile.k8ParW Z G X l)) =
      k8RowOn (k8StepsFrom Z.cuts (Z.D.1.map (·.entry)) 0) X.kind X.name (k8PreB X) (k8LenB X)
        (k8AsksB G X) l := by
  rw [k8Skel_par]
  unfold k8RowOn
  rw [← k8Msgs_eq, ← k8Msgs_eq]
  rfl

/-- **The lot's blocks' skeletons**, at all letters. -/
theorem k8Lot_skel (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((ProofFile.P1K8.lot Z).blocks G).map skel =
      G.built.toList.zipIdx.map fun x =>
        k8RowOn (k8StepsFrom Z.cuts (Z.D.1.map (·.entry)) 0) x.1.kind x.1.name (k8PreB x.1)
          (k8LenB x.1) (k8AsksB G x.1) x.2 := by
  show (ProofFile.k8Whole Z G).map skel = _
  unfold ProofFile.k8Whole
  rw [List.map_map]
  exact List.map_congr_left fun x _ => k8Skel_whole Z G x.1 x.2

/-! ### the written values -/

/-- The 25 written pairs (kind, name). -/
def k8KindsW : List (Nat × String) :=
  ((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++ [(2, "H")]

/-- The walk at the written table of steps and the written entries. -/
def k8TabW : List (String × Nat × Nat) := k8StepsFrom cutWritten esWritten 0

/-- The rows, from plain data. -/
def k8RowsAt (kinds : List (Nat × String)) (tab : List (String × Nat × Nat)) (pre : Bool) :
    List Skel :=
  kinds.zipIdx.map fun x => k8RowOn tab x.1.1 x.1.2 pre true true x.2

/-- Where the kind's row of link l stands in the written table. -/
def k8At (l : Nat) : Nat := if l == 24 then 343 else 14 * l + 6

/-- **THE WRITTEN ROWS**: cut from the written table; the kind's own name, a yes on the plan and the
three runs' names laid on. -/
def k8RowsW : List Skel :=
  (List.range 25).filterMap fun l => (cutFirstFull[k8At l]?).map fun r =>
    { name := "the smallness test: the draw of the matrix", place := r.2.1, nRounds := r.2.2.1
      nOracles := r.2.2.2.1, told := r.2.2.2.2.1, before := r.2.2.2.2.2, planOk := true
      claims := ["K8.equations"], after := ["K8.lsTail", "K8.tests"] }

set_option maxRecDepth 1000000 in
/-- 25 rows; the written table's rows there bear the spots' names and are of kind K8. -/
theorem k8RowsW_names :
    (decide (k8RowsW.length = 25) && k8KindsW.zipIdx.all fun x =>
      (cutFirstFull[k8At x.2]?).any fun r =>
        decide (r.1 = x.1.2 ++ (if x.2 == 24 then ":6" else ":5")) &&
          decide (r.2.1 = ⟨1, some x.2, if x.2 == 24 then 6 else 5, .K8⟩)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the written values the rows are the written rows.** -/
theorem k8Rows_written : k8RowsAt k8KindsW k8TabW true = k8RowsW := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A negative test: without the step «G5.3.call». -/
theorem k8Rows_noStep :
    decide (k8RowsAt k8KindsW (k8StepsFrom (cutWritten.filter fun c => c.look != "G5.3.call")
      esWritten 0) true = k8RowsW) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A second: without entries. -/
theorem k8Rows_noEntry :
    decide (k8RowsAt k8KindsW (k8StepsFrom cutWritten [] 0) true = k8RowsW) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A third: where the links' own numbers fail. -/
theorem k8Rows_notPre : decide (k8RowsAt k8KindsW k8TabW false = k8RowsW) = false := by
  decide +kernel

/-! The three above cannot but refuse: a list falls empty, or a yes on the plan is a no. They show
that the test is idle nowhere. The next two are well-formed wrong data: every row's own test on the
plan still says true; the comparison with the written rows must bite. -/

/-- Every row's own test on the plan says true. -/
def k8AllPlanOk (rows : List Skel) : Bool := rows.all (·.planOk)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A fourth: the first round of the step «G5.3.call» sends one root more: that link's list grows by
one number and every later number moves by one. -/
theorem k8Rows_rootMore :
    (k8AllPlanOk (k8RowsAt k8KindsW (k8StepsFrom cutWritten (esWritten.zipIdx.map fun x =>
        if x.2 == beforeAt cutWritten "G5.3.call" then { x.1 with roots := x.1.roots + 1 }
        else x.1) 0) true) &&
      !decide (k8RowsAt k8KindsW (k8StepsFrom cutWritten (esWritten.zipIdx.map fun x =>
        if x.2 == beforeAt cutWritten "G5.3.call" then { x.1 with roots := x.1.roots + 1 }
        else x.1) 0) true = k8RowsW)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A fifth: the first two layers' links bear each other's names. -/
theorem k8Rows_swapped :
    (k8AllPlanOk (k8RowsAt (k8KindsW.map fun x =>
        if x.2 == "G0" then (x.1, "G1") else if x.2 == "G1" then (x.1, "G0") else x)
        k8TabW true) &&
      !decide (k8RowsAt (k8KindsW.map fun x =>
        if x.2 == "G0" then (x.1, "G1") else if x.2 == "G1" then (x.1, "G0") else x)
        k8TabW true = k8RowsW)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A sixth: none of the written table's 25 rows bears the blocks' own name. -/
theorem k8Rows_ownName :
    ((List.range 25).any fun l => (cutFirstFull[k8At l]?).any fun r =>
      decide (r.1 = "the smallness test: the draw of the matrix")) = false := by
  decide +kernel

/-! ### the row -/

variable {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **THE ROW, at hypotheses by field.** -/
theorem k8_row_at (hc : Z.cuts = cutWritten) (he : Z.D.1.map (·.entry) = esWritten)
    (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW) (hn : k8GroundB G = true) :
    ((ProofFile.P1K8.lot Z).blocks G).map skel = k8RowsW := by
  rw [k8Lot_skel, hc, he, ← k8Rows_written]
  unfold k8RowsAt
  rw [← hk, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  have h := List.all_eq_true.1 hn x.1 (List.fst_mem_of_mem_zipIdx hx)
  rw [Bool.and_eq_true] at h
  show k8RowOn _ _ _ (k8PreB x.1) (k8LenB x.1) (k8AsksB G x.1) _ =
    k8RowOn _ _ _ true true true _
  rw [h.1, h.2, k8LenB_true]
  rfl

/-- **The row, on the lot's skeleton.** -/
theorem k8_lotSk_at (hc : Z.cuts = cutWritten) (he : Z.D.1.map (·.entry) = esWritten)
    (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW) (hn : k8GroundB G = true) :
    lotSk G (ProofFile.P1K8.lot Z) =
      { name := "the smallness test", letters := false, still := [], blocks := k8RowsW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  unfold lotSk
  rw [k8_row_at hc he hk hn]
  rfl

/-- The lot has no batching. -/
theorem k8_steady (Z : ProofFile.Pub) (G : ProofFile.Ground) : Steady G (ProofFile.P1K8.lot Z) :=
  steady_none G _ fun _ => rfl

end P1K8L

#print axioms P1K8L.k8Foldl_shift
#print axioms P1K8L.k8RootsOf_eq
#print axioms P1K8L.k8RootsOf_append
#print axioms P1K8L.k8RootsOf_take_add
#print axioms P1K8L.k8Roots_take
#print axioms P1K8L.k8Before_cons
#print axioms P1K8L.k8Steps_find
#print axioms P1K8L.k8Msgs_eq
#print axioms P1K8L.k8PreOn_bent
#print axioms P1K8L.k8LenB_true
#print axioms P1K8L.k8AsksOn_bent
#print axioms P1K8L.k8Skel_par
#print axioms P1K8L.k8Skel_whole
#print axioms P1K8L.k8Lot_skel
#print axioms P1K8L.k8RowsW_names
#print axioms P1K8L.k8Rows_written
#print axioms P1K8L.k8Rows_noStep
#print axioms P1K8L.k8Rows_noEntry
#print axioms P1K8L.k8Rows_notPre
#print axioms P1K8L.k8Rows_rootMore
#print axioms P1K8L.k8Rows_swapped
#print axioms P1K8L.k8Rows_ownName
#print axioms P1K8L.k8_row_at
#print axioms P1K8L.k8_lotSk_at
#print axioms P1K8L.k8_steady
