-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllShape.lean: THE SMALLNESS TEST: THE TEST WITH CODE ON THE PREMISES OF
THE TAIL OF ITS RUN OF EQUATIONS (tailReadyB, Johnson/Desc/K8/Honest/EqTailToy.lean) READS THE SHAPE
ALONE; AND THE ONE Bool OF THE WHOLE RUN, ON SHAPES. General laws: nothing is evaluated.

tailReadyB runs the library's own folds (the marks of the reads, the tiling of the tables, the count
of ties) on the records. Here: its value at the records is its value at the blank records of their
shapes (Johnson/Desc/First/Shape/Tail.lean): the same numbers, flags and marks, zeros of the same
sizes. So fun a => tailReadyB ... a.blank ... is a test on a shape without a field element, with no
second text of a fold.

  rowBlank, treeBlank, ledBlank   the way back for the ledger.
  eF, eFs         a table, and the list of tables, with the weights laid to 0.
  segsOf_e, readsList_e, markLoop_two, markRead_e, marksOf_e, tablesTile_e, tableB_e, readB_e
                  fold by fold.
  **tailReadyB_blank**   the law.
  allB            THE ONE Bool OF THE WHOLE LIST "K8.equations", on the shapes of the record, the
                  tables and the ledger and two numbers of claims.
  keysAt_gives, **allReady_of_shape**   a yes at the shapes gives the eight premises at the
                  records (AllReady, Johnson/Desc/K8/Honest/EqAllReturns.lean).
  **eqAll_of_shape**   a yes at the shapes and the three tests on values: the whole list returns
                  (over eqAll_returns, Johnson/Desc/K8/Honest/EqAllProofs.lean).
  allB_no         without a heard record the Bool rejects.

Limits. THE UPDATE IS NOT HERE: what the shape behind the list is, as a function of the shape in
front, is not stated. One direction alone: that the list's return gives the Bool's yes is not shown;
by reading it need not hold (the test on the sumcheck's row asks two sizes that the run does not
test); no example is made. What the Bool costs Lean's kernel at the full size is not measured: the
marks of the reads are laid one by one into arrays as long as the vectors' parts that hold tables.
Nothing on the tests on values. No argument is shown at which allB says yes. A TEST THAT READS A
FIELD WHICH THE SHAPES DO NOT HOLD ANSWERS, AT ledBlank, FOR THE DEFAULT (see its docstring): each
test run there wants a law of its own, as tailReadyB has here. ledBlank HAS A NAMESAKE OF THE SAME
TYPE: H2K5.Honest.ledBlank (Johnson/Desc/K5/Honest/Law/RunsBlank.lean): nearly the same text: that
one lays no root; this one lays a root where the shape says "rooted". Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllToy
import Johnson.Desc.K8.Honest.EqAllProofs
import Johnson.Desc.First.Shape.Tail
import Johnson.Desc.First.TailClaims.EqShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)

/-! ## The way back for the ledger -/

def rowBlank (r : RowSh) : HRow :=
  { coef := Array.replicate r.coef zeroE, L := Array.replicate r.entries zeroE, L0 := r.col0,
    rowForm := r.form, rowOnes := r.ones, rowFirst := r.first }

def treeBlank (T : TreeSh) : HTree :=
  { name := T.name, kind := if T.symbols then .symbols else .table, R := T.R, K := T.K,
    root := if T.rooted then some 0 else none, rows := (T.rows.map rowBlank).toArray }

/-- The ledger with these numbers, flags and marks; zeros of these sizes. What the shapes do not
hold is left to the records' defaults: a row's rowPoint, rowLo, rowHi (empty); an array's owner
(false); the ledger's theta and c0 (0); a debt's name is "". -/
def ledBlank (L : LedSh) : Fork :=
  { trees := (L.trees.map treeBlank).toArray, ns := L.ns, next := L.next,
    vp := Array.replicate L.shown zeroE, mf := Array.replicate L.factors zeroE,
    LS := Array.replicate L.coefs zeroE, gotF := L.got.toArray, nClaim := L.claims,
    thetaDrawnF := L.drawn, planClaimsF := L.planClaims, kapMapF := L.handed.toArray,
    doorShutF := L.shut, owed := (L.owed.map fun b => ({ what := "", added := b } : Owed)).toArray }

theorem tree_kind (T : HTree) : (treeBlank (treeSh T)).kind = T.kind := by
  show (if (T.kind == .symbols) = true then HKind.symbols else HKind.table) = T.kind
  cases T.kind <;> rfl

theorem led_trees (F : Fork) :
    (ledBlank (ledSh F)).trees = F.trees.map fun T => treeBlank (treeSh T) := by
  show ((F.trees.toList.map treeSh).map treeBlank).toArray = _
  rw [List.map_map]
  apply Array.ext'
  simp

theorem led_size (F : Fork) : (ledBlank (ledSh F)).trees.size = F.trees.size := by
  rw [led_trees, Array.size_map]

theorem led_kinds (F : Fork) :
    (ledBlank (ledSh F)).trees.map (·.kind) = F.trees.map (·.kind) := by
  rw [led_trees, Array.map_map]
  congr 1
  funext T
  exact tree_kind T

theorem led_cols (F : Fork) (tU : Nat) : colsOf (ledBlank (ledSh F)) tU = colsOf F tU := by
  unfold colsOf
  rw [led_trees, Array.getElem?_map, Option.map_map]
  rfl

/-! ## The tables -/

/-- A table with its weights laid to 0. -/
def eF (f : HFun) : HFun := (funSh f).blank

/-- The list of tables, each with its weights laid to 0. -/
def eFs (funs : Array HFun) : Array HFun := ((funs.toList.map funSh).map FunSh.blank).toArray

theorem eFs_toList (funs : Array HFun) : (eFs funs).toList = funs.toList.map eF := by
  show ((funs.toList.map funSh).map FunSh.blank) = _
  rw [List.map_map]
  rfl

theorem eF_size (f : HFun) : (eF f).phi.size = f.phi.size := by
  show (Array.replicate f.phi.size zeroE).size = _
  rw [Array.size_replicate]

theorem segsOf_e (tl : HTailF2) (mu un : Nat) (Fn : HFun) :
    segsOf tl mu un (eF Fn) = (segsOf tl mu un Fn).map fun x => (eF x.1, x.2) := by
  unfold segsOf
  show (if (Fn.mat == mu && Fn.tree == un) = true then
    (List.range ((tl.mats.getD mu {}).m / Fn.len)).map fun sg => (eF Fn, sg) else []) = _
  split
  · rw [List.map_map]
    rfl
  · rfl

theorem readsList_e (tl : HTailF2) (funs : Array HFun) :
    readsList tl (eFs funs) = (readsList tl funs).map fun x => (eF x.1, x.2) := by
  unfold readsList
  rw [eFs_toList]
  simp only [List.map_flatMap, List.flatMap_map, segsOf_e]

/-- The marks' loop at two records and two tables that agree on where an entry lies. -/
theorem markLoop_two {a b : HTailF2} (Fn Fn' : HFun) (sg t0 : Nat)
    (h : ∀ c, a.tabAt Fn c sg = b.tabAt Fn' c sg) : ∀ (count c : Nat) (m : Array Bool),
      a.markLoop Fn sg t0 count c m = b.markLoop Fn' sg t0 count c m
  | 0, _, _ => by
    unfold HTailF2.markLoop
    rfl
  | count + 1, c, m => by
    unfold HTailF2.markLoop
    rw [h c]
    cases b.tabAt Fn' c sg with
    | none => rfl
    | some pos =>
      dsimp only
      rw [markLoop_two Fn Fn' sg t0 h count]

theorem markRead_e (tl : HTailF2) (Fn : HFun) (sg : Nat) (rd : Array (Array Bool)) :
    (tailSh tl).blank.markRead (eF Fn) sg rd = tl.markRead Fn sg rd := by
  unfold HTailF2.markRead
  dsimp only
  rw [markLoop_two (a := (tailSh tl).blank) (b := tl) (eF Fn) Fn sg _ fun c => rfl]
  rfl

theorem marksOf_e (tl : HTailF2) (funs : Array HFun) :
    marksOf (tailSh tl).blank (eFs funs) = marksOf tl funs := by
  unfold marksOf
  show (readsList tl (eFs funs)).foldlM _ (noMarks tl) = _
  rw [readsList_e, List.foldlM_map]
  congr 1
  funext rd x
  exact markRead_e tl x.1 x.2 rd

theorem tablesTile_e (tl : HTailF2) (funs : Array HFun) (un : Nat) :
    (tailSh tl).blank.tablesTile (eFs funs) un = tl.tablesTile funs un := by
  unfold HTailF2.tablesTile
  rw [eFs_toList, List.filter_map, List.map_map]
  rfl

theorem tableB_e (tl : HTailF2) (funs : Array HFun) :
    tableB (tailSh tl).blank (eFs funs) = tableB tl funs := by
  unfold tableB
  rw [eFs_toList, List.all_map]
  congr 1
  funext Fn
  show (!(decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) ||
    ((tl.ix.U.getD Fn.tree none).isSome && Fn.len != 0 &&
      (tl.mats.getD Fn.mat {}).m % Fn.len == 0 && (eF Fn).phi.size == Fn.len)) = _
  rw [eF_size]

theorem readB_e (tl : HTailF2) (F : Fork) (x : HFun × Nat) :
    readB (tailSh tl).blank (ledBlank (ledSh F)) (eF x.1, x.2) = readB tl F x := by
  unfold readB
  show (match tl.ix.U.getD x.1.tree none with
    | none => false
    | some tU => _) = _
  cases tl.ix.U.getD x.1.tree none with
  | none => rfl
  | some tU =>
    dsimp only
    rw [led_cols]
    rfl

/-- **The test with code on the seventeen premises reads the shape alone.** before, front: the two
numbers of claims that tailReadyB takes (allB hands in front + n and front: n claims on the list so
far, front in front of the list). -/
theorem tailReadyB_blank (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork)
    (cs : Array Claim) :
    tailReadyB before front (tailSh tl).blank (eFs funs) (ledBlank (ledSh F))
      (Array.replicate cs.size {}) = tailReadyB before front tl funs F cs := by
  unfold tailReadyB
  rw [marksOf_e, tablesTile_e, tablesTile_e, tableB_e, readsList_e, List.all_map, List.length_map,
    led_size, led_kinds, Array.size_replicate]
  have e1 : (readB (tailSh tl).blank (ledBlank (ledSh F)) ∘
      fun x : HFun × Nat => (eF x.1, x.2)) = readB tl F := funext fun x => readB_e tl F x
  have e2 : ((eFs funs).all fun Fn => decide (Fn.mat < (tailSh tl).blank.NM) &&
      (Fn.tree == 0 || Fn.tree == 2)) =
      funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2) := by
    rw [← Array.all_toList, ← Array.all_toList, eFs_toList, List.all_map]
    rfl
  rw [e1, e2]
  rfl

/-! ## The whole list -/

/-- **THE ONE Bool OF THE WHOLE LIST "K8.equations"**, on shapes: t: the record's; fs: the tables';
L: the ledger's; n: the number of claims on the list so far; front: the number of claims in front of
the list. The first clauses are tests on numbers of the shapes; the last is the test on
the tail's seventeen premises, run at the blank records. -/
def allB (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) : Bool :=
  match t.heard with
  | none => false
  | some g =>
    t.funClosed && fs.length == t.funs.length && g.rows.length == lookRows t.blank &&
      Law.keysAt g.narrow (Law.EqSh.mk t.narrow L []) && openB g.leaves L &&
      tailReadyB (front + n) front t.blank (fs.map FunSh.blank).toArray (ledBlank L)
        (Array.replicate (n + 4) {})

/-- What the Bool of eqKeys gives, at the record. -/
theorem keysAt_gives {tl : HTailF2} {g : Forest.Heard} {L : LedSh} {l : List ClaimSh}
    (hb : Law.keysAt (heardSh g) (Law.EqSh.mk (tlSh tl) L l) = true) :
    padKeyDigits tl = true ∧
      (∀ q ∈ [0, 1], ∀ p ∈ (tl.zOf q).pieces.toList, Law.idxOk tl g q p = true) ∧
      laidDigits tl = some g.shape.pub := by
  have h' : ((padKeyDigits tl &&
      ([0, 1].all fun q => ((tlSh tl).callAt q).pieces.all
        (Law.idxB ((tlSh tl).callAt q).n (Law.zkAt (heardSh g) q)))) &&
      ((laidDigits tl).map (·.toList) == some g.shape.pub.toList)) = true := hb
  rw [Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨hk, hi⟩, hl⟩ := h'
  refine ⟨hk, fun q hq p hp => ?_, ?_⟩
  · have a := List.all_eq_true.1 hi q hq
    rw [Law.call_sh tl q, Law.zk_sh] at a
    rw [Law.idx_sh]
    exact List.all_eq_true.1 a (pieceSh p) (List.mem_map.2 ⟨p, hp, rfl⟩)
  · have a := beq_iff_eq.1 hl
    cases hd : laidDigits tl with
    | none =>
      rw [hd] at a
      cases a
    | some r =>
      rw [hd] at a
      rw [Array.toList_inj.1 (Option.some.inj a)]

/-- **A yes of the Bool at the shapes gives the eight premises at the records.** -/
theorem allReady_of_shape {front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim}
    (h : allB front (tailSh tl) (funs.toList.map funSh) (ledSh F) cs.size = true) :
    ∃ g rd s1 s3, AllReady front tl funs F cs g rd s1 s3 := by
  unfold allB at h
  cases hg : tl.heard with
  | none =>
    have e : (tailSh tl).heard = none := by
      show tl.heard.map heardAll = _
      rw [hg]
      rfl
    rw [e] at h
    cases h
  | some g =>
    have e : (tailSh tl).heard = some (heardAll g) := by
      show tl.heard.map heardAll = _
      rw [hg]
      rfl
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
    rw [heard_narrow, tail_narrow] at a4
    obtain ⟨hk, hi, hl⟩ := keysAt_gives a4
    have a6' : tailReadyB (front + cs.size) front (tailSh tl).blank (eFs funs)
        (ledBlank (ledSh F)) (Array.replicate (cs ++ Array.replicate 4 ({} : Claim)).size {}) =
        true := by
      rw [Array.size_append, Array.size_replicate]
      exact a6
    rw [tailReadyB_blank] at a6'
    obtain ⟨rd, s1, s3, hT⟩ := tailReady_of_B a6'
    refine ⟨g, rd, s1, s3, ⟨a1, ?_⟩, hg, ?_, hk, hi, hl, open_of_B a5,
      fun c4 e4 => tailReady_size (by simp [e4]) hT⟩
    · have := beq_iff_eq.1 a2
      simpa [tailSh] using this
    · have := beq_iff_eq.1 a3
      simpa [heardAll] using this

/-- **Where the Bool accepts at the shapes and the three tests on values pass, the whole list
returns.** What the law says of what lies behind is not handed on. -/
theorem eqAll_of_shape {front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim}
    (h : allB front (tailSh tl) (funs.toList.map funSh) (ledSh F) cs.size = true)
    (v1 : tl.funsHeld funs = true) (v2 : (F.LS.extract tl.slotA tl.slotB).all isZeroE = true)
    (v3 : LiveCols tl funs F.theta) :
    ∃ out s', eqAll tl funs front (F, cs) = .ok (out, s') := by
  obtain ⟨g, rd, s1, s3, hA⟩ := allReady_of_shape h
  obtain ⟨out, s', e, -⟩ := eqAll_returns front tl funs F cs g rd s1 s3 hA v1 v2 v3
  exact ⟨out, s', e⟩

/-- Without a heard record the Bool rejects. -/
theorem allB_no (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat)
    (h : t.heard = none) : allB front t fs L n = false := by
  unfold allB
  rw [h]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tree_kind
#print axioms VerifiableInference.Desc.First.K8.Honest.led_trees
#print axioms VerifiableInference.Desc.First.K8.Honest.led_size
#print axioms VerifiableInference.Desc.First.K8.Honest.led_kinds
#print axioms VerifiableInference.Desc.First.K8.Honest.led_cols
#print axioms VerifiableInference.Desc.First.K8.Honest.eFs_toList
#print axioms VerifiableInference.Desc.First.K8.Honest.eF_size
#print axioms VerifiableInference.Desc.First.K8.Honest.segsOf_e
#print axioms VerifiableInference.Desc.First.K8.Honest.readsList_e
#print axioms VerifiableInference.Desc.First.K8.Honest.markLoop_two
#print axioms VerifiableInference.Desc.First.K8.Honest.markRead_e
#print axioms VerifiableInference.Desc.First.K8.Honest.marksOf_e
#print axioms VerifiableInference.Desc.First.K8.Honest.tablesTile_e
#print axioms VerifiableInference.Desc.First.K8.Honest.tableB_e
#print axioms VerifiableInference.Desc.First.K8.Honest.readB_e
#print axioms VerifiableInference.Desc.First.K8.Honest.tailReadyB_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.keysAt_gives
#print axioms VerifiableInference.Desc.First.K8.Honest.allReady_of_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_of_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.allB_no
#print axioms VerifiableInference.Desc.First.K8.Honest.rowBlank
#print axioms VerifiableInference.Desc.First.K8.Honest.treeBlank
#print axioms VerifiableInference.Desc.First.K8.Honest.ledBlank
#print axioms VerifiableInference.Desc.First.K8.Honest.eF
#print axioms VerifiableInference.Desc.First.K8.Honest.eFs
#print axioms VerifiableInference.Desc.First.K8.Honest.allB
