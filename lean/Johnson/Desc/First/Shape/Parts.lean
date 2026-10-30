-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Parts.lean: THE SHAPES OF THE RECORDS THAT ALL SUB-PROTOCOLS OF THE FIRST
CHAIN SHARE: what is kept of a form, a run, a claim, a sumcheck, the ledger, a lookup's heard record
and the smallness test's record: flags, counts, marks, lengths and public numbers: no field element,
AND NOT ALL ELSE (the list: LEFT OUT, below). With the ledger's and the sumcheck's tests and updates
on these shapes, and their laws. Definitions and general laws; nothing is evaluated.

What it is for. A verifier's step says yes where its guards on the structure pass and its tests on
values pass. These shapes are for the first half: one Bool and one update on a shape that holds no
field element, so that it can be run without a proof. This file has the parts of such a shape.

Each shape is a nested product of Nat, Bool, String, lists and options: no field element, by type.
EACH COMPONENT IS REACHED BY A NAMED READER (AffSh.slots, LedSh.got, ...), made by mk and turned by
a named setter: a law names no position in a product, so a component can be added behind the others
without turning a law's statement.
NARROW, BY INTENT: a component is meant to be here only if a guard on the structure reads it or an
update needs it. Each further component asks a law of every step that writes it.

  1  entSh, affSh, runSh, claimSh   a form's entries and slots by number; a run without its weights;
     a claim. affSh_ofConst | slot | ent | addMul | add | sub; claims_push.
  2  pscSh, takenSh, taken_sh   a sumcheck: two flags, each variable's number of coefficients (the
     library's d; the reader's name is "degrees"), the number of challenges, the first slot, the
     start form's shape, a third flag. affSh_addSlots; rowFormSh, affSh_rowForm: the shape of the
     claim that a sumcheck leaves.
  3  rowSh, treeSh, ledSh   the ledger: the number of slots, three sizes, the slots' marks, the owed
     claims' marks, three numbers, two flags, the marks of the weights handed out; array by array:
     name, kind, two numbers, THE MARK THAT THE CHAIN HAS RECEIVED ITS COMMITMENT; row by row: two
     sizes, two numbers, two flags. modAt, map_modify, map_modAt: a change of one member of an array
     or a list, seen through a reader; LedSh.modRow: a change at one row of one array;
     LedSh.rooted, LedSh.setRootedAt: the arrays' marks, and one of them set.
     sizedB, freeB, fillB, paidB: tests and updates. fillB_zip, free_get; sized_of_B, free_of_B;
     hide_of_free, hide_of_B: where the slots are there and free, Fork.hideRun returns, and the
     shape behind is the shape in front with these slots filled; ledSh_paid; got_fill, owed_paid:
     the two updates, mark by mark;
     ledSh_onRow: a change of one virtual row (HTailF2.onRow, OnBytes/Model/Tail.lean);
     rooted_ledSh, ledSh_taken, rooted_setRootedAt: the chain's receipt of an array's commitment
     (Fork.rootTaken, OnBytes/Model/Hide.lean) sets that array's mark and turns nothing else.
  4  openB, open_of_B   the test on a sumcheck and the ledger that gives the library's own condition
     for a sumcheck's row (D6.Ret.Open, OnBytes/K/Kc/Returns/FlReturns6.lean).
  5  pieceSh, callSh, heardSh, tlSh   readers alone: no law of this file speaks of them.

Defaults. THE MAKERS THAT READ A SHAPE OFF A RECORD (entSh ... tlSh) LAY NO DEFAULT: each is total
on its record, whole lists are kept, and an Option stays an Option (tlSh's heard, laid, joinObj):
where it is none a Bool over it says no. Three things ON THE SHAPE's side are silent outside a list,
each as the library's own text is:
  LedSh.treeAt, TreeSh.rowAt   the empty array's and the empty row's shape: as F.trees.getD t {} and
    T.rows.getD r {} (Johnson/Desc/First/TailClaims/SelfTests.lean). No law or test of this file
    calls them. A guard that reads through them asks that the place is there only where the
    library's own guard does.
  modAt, LedSh.modRow, paidB   a number outside the list turns nothing: as Array.modify in
    HTailF2.onRow (OnBytes/Model/Tail.lean) and Fork.paid (OnBytes/Model/Hide.lean). Of paid the
    library says itself: "if there is none, nothing is marked and nothing is refused"
    (OnBytes/Model/Look.lean, at Forest.Heard). The update is as silent as the text.
fillB is not silent: where first + n goes beyond the list, its value is longer than the list. Each
law of this file that names fillB asks that first + n lies within it, outright or by freeB: freeB
asks that the slots are there (first + n within the number of slots; the marks of that length).

LEFT OUT, beside the field elements themselves. Of a form (Aff): each entry's and each slot's
coefficient, the constant. Of a run (Run2): the factor; of the weights all but their number. Of a
sumcheck (Psc): target, eps, claim; of the challenges all but their number; of each variable
(Weight) all but d: moment and psi (not even their lengths), fixedInv, AND fixed, WHICH IS A NUMBER.
Of a virtual row (HRow): of coef and L all but the size; rowPoint, rowLo, rowHi whole (not even
their sizes). Of an array (HTree): owner; of root all but whether it is there; of kind all but
whether it is "symbols". Of an owed claim (Owed): what. Of the ledger (Fork): c0, theta; of vp, mf,
LS all but the size. Of a piece (Piece): r0 AND Rp, WHICH ARE NUMBERS. Of a lookup's heard record
and of the smallness test's record: most fields (Johnson/Desc/First/Shape/Tail.lean has these two
whole).

Limits. That a shape is blind to what a prover sends and to what is drawn is so by type for field
elements alone: a number can still be made of a value; which numbers of these records are the plan's
or counts is not shown in this file. sizedB asks two sizes that Fork.hide itself does not test (the
library's laws on hideRun ask them): so freeB and openB are sufficient, not necessary. The marks are
plain lists of Bools; the test and the update pass over them once.
Nothing on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns6
import Johnson.Desc.Claim
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.PscRun VerifiableInference.Desc
open D6.Ret (Open taken hideRun_free)
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)

/-! ## 1 Forms, runs, claims -/

/-- An entry of a virtual row without its coefficient: array, row, index. -/
abbrev EntSh : Type := Nat × Nat × Nat

def entSh (e : Ent) : EntSh := (e.tree, e.row, e.idx)

/-- A form without its coefficients and constant: its entries, its slots. -/
abbrev AffSh : Type := List EntSh × List Nat

namespace AffSh
def mk (ents : List EntSh) (slots : List Nat) : AffSh := (ents, slots)
def ents (a : AffSh) : List EntSh := a.1
def slots (a : AffSh) : List Nat := a.2
/-- One form's entries and slots behind another's. -/
def append (a b : AffSh) : AffSh := mk (a.ents ++ b.ents) (a.slots ++ b.slots)
end AffSh

def affSh (a : Aff) : AffSh := AffSh.mk (a.ents.toList.map entSh) (a.slots.toList.map (·.1))

theorem affSh_ofConst (v : E) : affSh (Aff.ofConst v) = AffSh.mk [] [] := rfl

theorem affSh_slot (j : Nat) : affSh (Aff.slot j) = AffSh.mk [] [j] := rfl

theorem affSh_ent (t r i : Nat) : affSh (Aff.ent t r i) = AffSh.mk [(t, r, i)] [] := rfl

/-- A fold that pushes f x for each member x. -/
theorem foldl_push_map {α β : Type} (f : α → β) : ∀ (l : List α) (init : Array β),
    (l.foldl (fun acc x => acc.push (f x)) init).toList = init.toList ++ l.map f
  | [], init => by simp
  | x :: l, init => by
    rw [List.foldl_cons, foldl_push_map f l, Array.toList_push]
    simp

theorem affSh_addMul (a b : Aff) (k : E) : affSh (a.addMul b k) = (affSh a).append (affSh b) := by
  unfold affSh Aff.addMul AffSh.append AffSh.ents AffSh.slots AffSh.mk
  dsimp only
  have e1 := foldl_push_map (fun x : Ent => ({ x with coef := mulE x.coef k } : Ent))
    b.ents.toList a.ents
  have e2 := foldl_push_map (fun x : Nat × E => (x.1, mulE x.2 k)) b.slots.toList a.slots
  rw [← Array.foldl_toList, ← Array.foldl_toList, e1, e2, List.map_append, List.map_append,
    List.map_map, List.map_map]
  rfl

theorem affSh_add (a b : Aff) : affSh (a + b) = (affSh a).append (affSh b) := affSh_addMul a b _

theorem affSh_sub (a b : Aff) : affSh (a - b) = (affSh a).append (affSh b) := affSh_addMul a b _

/-- A run of entries without its weights and factor: array, row, first entry, the number of weights,
the first weight, the length. -/
abbrev RunSh : Type := Nat × Nat × Nat × Nat × Nat × Nat

namespace RunSh
def mk (tree row first weights w0 n : Nat) : RunSh := (tree, row, first, weights, w0, n)
def tree (r : RunSh) : Nat := r.1
def row (r : RunSh) : Nat := r.2.1
def first (r : RunSh) : Nat := r.2.2.1
def weights (r : RunSh) : Nat := r.2.2.2.1
def w0 (r : RunSh) : Nat := r.2.2.2.2.1
def n (r : RunSh) : Nat := r.2.2.2.2.2
end RunSh

def runSh (r : Run2) : RunSh := RunSh.mk r.tree r.row r.first r.w.size r.w0 r.n

/-- A claim: its place among the powers, its form's shape, its runs' shapes. -/
abbrev ClaimSh : Type := Option Nat × AffSh × List RunSh

namespace ClaimSh
def mk (eqFirst : Option Nat) (form : AffSh) (runs : List RunSh) : ClaimSh := (eqFirst, form, runs)
def eqFirst (c : ClaimSh) : Option Nat := c.1
def form (c : ClaimSh) : AffSh := c.2.1
def runs (c : ClaimSh) : List RunSh := c.2.2
end ClaimSh

def claimSh (c : Claim) : ClaimSh := ClaimSh.mk c.eqFirst (affSh c.form) (c.runs.toList.map runSh)

theorem claims_push (cs : Array Claim) (c : Claim) :
    (cs.push c).toList.map claimSh = cs.toList.map claimSh ++ [claimSh c] := by
  rw [Array.toList_push, List.map_append]
  rfl

/-! ## 2 A sumcheck -/

/-- A sumcheck: the row is made; it is begun; each variable's number of coefficients (the library's
d); the number of challenges; the first slot; the shape of the form that the sum must equal; the
round in the further variable has been run. -/
abbrev PscSh : Type := Bool × Bool × List Nat × Nat × Nat × AffSh × Bool

namespace PscSh
def mk (rowMade started : Bool) (degrees : List Nat) (challenges first : Nat) (start : AffSh)
    (ended : Bool) : PscSh := (rowMade, started, degrees, challenges, first, start, ended)
def rowMade (p : PscSh) : Bool := p.1
def started (p : PscSh) : Bool := p.2.1
def degrees (p : PscSh) : List Nat := p.2.2.1
def challenges (p : PscSh) : Nat := p.2.2.2.1
def first (p : PscSh) : Nat := p.2.2.2.2.1
def start (p : PscSh) : AffSh := p.2.2.2.2.2.1
def ended (p : PscSh) : Bool := p.2.2.2.2.2.2
end PscSh

def pscSh (p : Psc) : PscSh :=
  PscSh.mk p.rowMade p.started (p.vars.toList.map (·.d)) p.r.size p.first (affSh p.start) p.ended

/-- How many slots a sumcheck has taken, of its variables' numbers of coefficients. -/
def takenSh (ds : List Nat) : Nat := 1 + (ds.map (· - 1)).sum

theorem taken_sh (p : Psc) : takenSh (pscSh p).degrees = taken p := by
  show 1 + ((p.vars.toList.map (·.d)).map (· - 1)).sum = 1 + _
  rw [List.map_map]
  rfl

/-- The slots first, first + 1, ... laid behind a form. -/
theorem affSh_addSlots (a : Aff) (first : Nat) (form : Array E) :
    affSh (addSlots a first form) =
      (affSh a).append (AffSh.mk [] (List.range' first form.size)) := by
  have key : ∀ (l : List E) (j : Nat) (u : Aff), affSh (l.foldl addSlot (j, u)).2 =
      (affSh u).append (AffSh.mk [] (List.range' j l.length)) := by
    intro l
    induction l with
    | nil =>
      intro j u
      simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
    | cons x l ih =>
      intro j u
      rw [List.foldl_cons]
      show affSh (l.foldl addSlot (j + 1, Aff.addMul u (Aff.slot j) x)).2 = _
      rw [ih, affSh_addMul, affSh_slot]
      simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots, List.range'_succ]
  unfold addSlots
  rw [← Array.foldl_toList, key, Array.length_toList]

/-- The shape of the claim that a sumcheck leaves: its n own slots from first on; the start form's
entries and slots; those of the terms that are kept. -/
def rowFormSh (first n : Nat) (start kept : AffSh) : AffSh :=
  AffSh.mk (start.ents ++ kept.ents) (List.range' first n ++ start.slots ++ kept.slots)

theorem affSh_rowForm (p : Psc) (S0 : E) (kept : Aff) :
    affSh (p.rowForm S0 kept) = rowFormSh p.first p.walk.1.length (affSh p.start) (affSh kept) := by
  unfold Psc.rowForm
  dsimp only
  rw [affSh_addMul, affSh_addMul, affSh_addSlots, affSh_sub, affSh_ofConst, affSh_ofConst]
  simp [rowFormSh, AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]

/-! ## 3 The ledger -/

/-- A list with f laid on member number i; a number outside the list turns nothing. The same
function, with map_modify, stands in Johnson/Desc/Ground/Shape/Core.lean under the namespace
VerifiableInference.Desc.Ground.Sh. -/
def modAt {α : Type} (l : List α) (i : Nat) (f : α → α) : List α :=
  l.zipIdx.map fun x => if x.2 = i then f x.1 else x.1

/-- A change of one member of an array, seen through a reader. -/
theorem map_modify {α β : Type} (a : Array α) (i : Nat) (f : α → α) (sh : α → β) (g : β → β)
    (h : ∀ x, sh (f x) = g (sh x)) :
    (a.modify i f).toList.map sh = modAt (a.toList.map sh) i g := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Array.getElem_toList,
    Array.getElem_modify, Nat.zero_add]
  by_cases e : i = j
  · rw [if_pos e, if_pos e.symm, h]
  · rw [if_neg e, if_neg fun a => e a.symm]

/-- A virtual row: the sizes of its weights on the rows and on the entries; the first column that
the second holds; two flags of the product form; the first row that the equality polynomial covers.
-/
abbrev RowSh : Type := Nat × Nat × Nat × Bool × Bool × Nat

namespace RowSh
def mk (coef entries col0 : Nat) (form ones : Bool) (first : Nat) : RowSh :=
  (coef, entries, col0, form, ones, first)
def coef (r : RowSh) : Nat := r.1
def entries (r : RowSh) : Nat := r.2.1
def col0 (r : RowSh) : Nat := r.2.2.1
def form (r : RowSh) : Bool := r.2.2.2.1
def ones (r : RowSh) : Bool := r.2.2.2.2.1
def first (r : RowSh) : Nat := r.2.2.2.2.2
/-- The shape of the empty row. -/
def empty : RowSh := mk 0 0 0 false false 0
def setCoef (r : RowSh) (n : Nat) : RowSh := mk n r.entries r.col0 r.form r.ones r.first
def setForm (r : RowSh) (form ones : Bool) (first : Nat) : RowSh :=
  mk r.coef r.entries r.col0 form ones first
end RowSh

def rowSh (r : HRow) : RowSh := RowSh.mk r.coef.size r.L.size r.L0 r.rowForm r.rowOnes r.rowFirst

/-- An array: its name; it holds symbols; its numbers of rows and columns; its virtual rows; the
chain has received its commitment. -/
abbrev TreeSh : Type := String × Bool × Nat × Nat × List RowSh × Bool

namespace TreeSh
def mk (name : String) (symbols : Bool) (R K : Nat) (rows : List RowSh) (rooted : Bool) : TreeSh :=
  (name, symbols, R, K, rows, rooted)
def name (T : TreeSh) : String := T.1
def symbols (T : TreeSh) : Bool := T.2.1
def R (T : TreeSh) : Nat := T.2.2.1
def K (T : TreeSh) : Nat := T.2.2.2.1
def rows (T : TreeSh) : List RowSh := T.2.2.2.2.1
def rooted (T : TreeSh) : Bool := T.2.2.2.2.2
/-- Row number r; outside the list: the shape of the empty row. -/
def rowAt (T : TreeSh) (r : Nat) : RowSh := T.rows.getD r RowSh.empty
def setRows (T : TreeSh) (rows : List RowSh) : TreeSh :=
  mk T.name T.symbols T.R T.K rows T.rooted
def setRooted (T : TreeSh) (rooted : Bool) : TreeSh := mk T.name T.symbols T.R T.K T.rows rooted
end TreeSh

def treeSh (T : HTree) : TreeSh :=
  TreeSh.mk T.name (T.kind == .symbols) T.R T.K (T.rows.toList.map rowSh) T.root.isSome

/-- The ledger: the number of slots; the sizes of what was shown and of the factors; for each slot:
it is filled; for each owed claim: it has been added; the number of claims in the plan; the arrays;
the next slot; the size of the slots' coefficients; the number of claims added; the batching element
is drawn; for each claim of the plan: its weight has been handed out; the door is shut. -/
abbrev LedSh : Type :=
  Nat × Nat × Nat × List Bool × List Bool × Nat × List TreeSh × Nat × Nat × Nat × Bool ×
    List Bool × Bool

namespace LedSh
def mk (ns shown factors : Nat) (got owed : List Bool) (planClaims : Nat) (trees : List TreeSh)
    (next coefs claims : Nat) (drawn : Bool) (handed : List Bool) (shut : Bool) : LedSh :=
  (ns, shown, factors, got, owed, planClaims, trees, next, coefs, claims, drawn, handed, shut)
def ns (L : LedSh) : Nat := L.1
def shown (L : LedSh) : Nat := L.2.1
def factors (L : LedSh) : Nat := L.2.2.1
def got (L : LedSh) : List Bool := L.2.2.2.1
def owed (L : LedSh) : List Bool := L.2.2.2.2.1
def planClaims (L : LedSh) : Nat := L.2.2.2.2.2.1
def trees (L : LedSh) : List TreeSh := L.2.2.2.2.2.2.1
def next (L : LedSh) : Nat := L.2.2.2.2.2.2.2.1
def coefs (L : LedSh) : Nat := L.2.2.2.2.2.2.2.2.1
def claims (L : LedSh) : Nat := L.2.2.2.2.2.2.2.2.2.1
def drawn (L : LedSh) : Bool := L.2.2.2.2.2.2.2.2.2.2.1
def handed (L : LedSh) : List Bool := L.2.2.2.2.2.2.2.2.2.2.2.1
def shut (L : LedSh) : Bool := L.2.2.2.2.2.2.2.2.2.2.2.2
/-- Array number t; outside the list: the shape of the empty array. -/
def treeAt (L : LedSh) (t : Nat) : TreeSh := L.trees.getD t (TreeSh.mk "" false 0 0 [] false)
/-- Array by array: the chain has received its commitment. -/
def rooted (L : LedSh) : List Bool := L.trees.map TreeSh.rooted
def setGot (L : LedSh) (got : List Bool) : LedSh :=
  mk L.ns L.shown L.factors got L.owed L.planClaims L.trees L.next L.coefs L.claims L.drawn
    L.handed L.shut
def setOwed (L : LedSh) (owed : List Bool) : LedSh :=
  mk L.ns L.shown L.factors L.got owed L.planClaims L.trees L.next L.coefs L.claims L.drawn
    L.handed L.shut
def setTrees (L : LedSh) (trees : List TreeSh) : LedSh :=
  mk L.ns L.shown L.factors L.got L.owed L.planClaims trees L.next L.coefs L.claims L.drawn
    L.handed L.shut
/-- f laid on row r of array t; a place outside the lists turns nothing. -/
def modRow (L : LedSh) (t r : Nat) (f : RowSh → RowSh) : LedSh :=
  L.setTrees (modAt L.trees t fun T => T.setRows (modAt T.rows r f))
/-- Array number i is marked: the chain has received its commitment. A number outside the list turns
nothing. -/
def setRootedAt (L : LedSh) (i : Nat) : LedSh :=
  L.setTrees (modAt L.trees i fun T => T.setRooted true)
end LedSh

def ledSh (F : Fork) : LedSh :=
  LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList (F.owed.toList.map (·.added)) F.planClaimsF
    (F.trees.toList.map treeSh) F.next F.LS.size F.nClaim F.thetaDrawnF F.kapMapF.toList
    F.doorShutF

/-- The ledger's three arrays on the slots have their size. -/
def sizedB (L : LedSh) : Bool := L.shown == L.ns && L.factors == L.ns && L.got.length == L.ns

/-- The n slots from first on are there and free, in a ledger whose arrays have their size. -/
def freeB (L : LedSh) (first n : Nat) : Bool :=
  sizedB L && decide (first + n ≤ L.ns) && ((L.got.drop first).take n).all (!·)

/-- The marks with the n slots from first on filled, where they lie within the list; where they go
beyond it the value is longer than the list. -/
def fillB (got : List Bool) (first n : Nat) : List Bool :=
  got.take first ++ List.replicate n true ++ got.drop (first + n)

/-- The same, mark by mark. -/
theorem fillB_zip (got : List Bool) (first n : Nat) (hn : first + n ≤ got.length) :
    fillB got first n =
      got.zipIdx.map fun x => x.1 || (decide (first ≤ x.2) && decide (x.2 < first + n)) := by
  refine List.ext_getElem (by simp [fillB]; omega) fun i i1 i2 => ?_
  have il : i < got.length := by simpa using i2
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  unfold fillB
  by_cases h1 : i < first
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp [show ¬ first ≤ i by omega]
  · by_cases h2 : i < first + n
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp [show first ≤ i by omega, h2]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [h2]
      congr 1
      omega

/-- What the pass over n marks from first on says of each. -/
theorem free_get (got : List Bool) (first n : Nat)
    (h : ((got.drop first).take n).all (!·) = true) (i : Nat) (hi : i < n) :
    got[first + i]?.getD false = false := by
  by_cases hl : first + i < got.length
  · have hm : got[first + i] ∈ (got.drop first).take n :=
      List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩
    have := List.all_eq_true.1 h _ hm
    simpa [hl] using this
  · simp [hl]

/-- The owed marks with number i paid. -/
def paidB (owed : List Bool) (i : Nat) : List Bool := owed.zipIdx.map fun x => x.1 || x.2 == i

theorem sized_of_B {F : Fork} (h : sizedB (ledSh F) = true) : Sized F := by
  simp only [sizedB, ledSh, LedSh.mk, LedSh.shown, LedSh.ns, LedSh.factors, LedSh.got,
    Bool.and_eq_true, beq_iff_eq, Array.length_toList] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem free_of_B {F : Fork} {first n : Nat} (h : freeB (ledSh F) first n = true) :
    Sized F ∧ first + n ≤ F.ns ∧ ∀ i, i < n → ¬ Filled F (first + i) := by
  unfold freeB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨sized_of_B h.1.1, of_decide_eq_true h.1.2, fun i hi hf => ?_⟩
  have k := free_get (ledSh F).got first n h.2 i hi
  have e : (ledSh F).got[first + i]? = F.gotF[first + i]? := Array.getElem?_toList ..
  rw [e] at k
  unfold Filled at hf
  rw [Array.getD_eq_getD_getElem?] at hf
  rw [hf] at k
  cases k

/-- The marks behind a filling, mark by mark. -/
theorem got_fill {F H : Fork} {first n : Nat} (hF : Sized F) (hS : Same F H) (hH : Sized H)
    (hn : first + n ≤ F.ns) (h1 : ∀ j, first ≤ j → j < first + n → Filled H j)
    (h2 : ∀ j, (j < first ∨ first + n ≤ j) → (Filled H j ↔ Filled F j)) :
    H.gotF.toList = fillB F.gotF.toList first n := by
  have hl : H.gotF.size = F.gotF.size := by rw [hH.2.2, hF.2.2, hS.ns]
  rw [fillB_zip _ _ _ (by rw [Array.length_toList, hF.2.2]; exact hn)]
  refine List.ext_getElem (by simp [hl]) fun i i1 i2 => ?_
  have iH : i < H.gotF.size := by simpa using i1
  have iF : i < F.gotF.size := by rw [← hl]; exact iH
  have eH : Filled H i ↔ H.gotF[i] = true := by simp [Filled, Array.getD, iH]
  have eF : Filled F i ↔ F.gotF[i] = true := by simp [Filled, Array.getD, iF]
  simp only [List.getElem_map, List.getElem_zipIdx, Array.getElem_toList, Nat.zero_add]
  by_cases hin : first ≤ i ∧ i < first + n
  · rw [eH.1 (h1 i hin.1 hin.2)]
    simp [hin.1, hin.2]
  · have k := h2 i (by omega)
    rw [eH, eF] at k
    have hb : (decide (first ≤ i) && decide (i < first + n)) = false := by
      simpa using fun a => by omega
    rw [hb, Bool.or_false]
    exact Bool.eq_iff_iff.2 k

/-- **Where the slots are there and free, the filling returns, and the shape behind is the shape in
front with these slots filled.** At all values. -/
theorem hide_of_free {F : Fork} {first : Nat} {v : Array E} (hF : Sized F)
    (hn : first + v.size ≤ F.ns) (hfree : ∀ i, i < v.size → ¬ Filled F (first + i)) (f : E) :
    ∃ H, F.hideRun first v f = some H ∧ Same F H ∧ Sized H ∧
      ledSh H = (ledSh F).setGot (fillB (ledSh F).got first v.size) := by
  obtain ⟨H, hH⟩ := hideRun_free (F := F) first v f hF fun i hi => ⟨by omega, hfree i hi⟩
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok F H first v f hF hH
  refine ⟨H, hH, a1, a2, ?_⟩
  have eg : H.gotF.toList = fillB F.gotF.toList first v.size :=
    got_fill hF a1 a2 hn (fun j j1 j2 => by
      have := (a3 (j - first) (by omega)).2.2.1
      rw [show first + (j - first) = j by omega] at this
      exact this) fun j hj => (a4 j hj).2.2
  have eo : H.owed = F.owed := by rw [a1]
  have ep : H.planClaimsF = F.planClaimsF := by rw [a1]
  have et : H.trees = F.trees := by rw [a1]
  have e1 : H.LS = F.LS := by rw [a1]
  have e2 : H.nClaim = F.nClaim := by rw [a1]
  have e3 : H.thetaDrawnF = F.thetaDrawnF := by rw [a1]
  have e4 : H.kapMapF = F.kapMapF := by rw [a1]
  have e5 : H.doorShutF = F.doorShutF := by rw [a1]
  show LedSh.mk H.ns H.vp.size H.mf.size H.gotF.toList (H.owed.toList.map (·.added))
      H.planClaimsF (H.trees.toList.map treeSh) H.next H.LS.size H.nClaim H.thetaDrawnF
      H.kapMapF.toList H.doorShutF =
    LedSh.mk F.ns F.vp.size F.mf.size (fillB F.gotF.toList first v.size)
      (F.owed.toList.map (·.added)) F.planClaimsF (F.trees.toList.map treeSh) F.next F.LS.size
      F.nClaim F.thetaDrawnF F.kapMapF.toList F.doorShutF
  rw [eg, eo, ep, et, e1, e2, e3, e4, e5, a1.next, a2.1, a2.2.1, a1.ns, hF.1, hF.2.1]

/-- The same from the test with code. -/
theorem hide_of_B {F : Fork} {first : Nat} {v : Array E}
    (h : freeB (ledSh F) first v.size = true) (f : E) :
    ∃ H, F.hideRun first v f = some H ∧ Same F H ∧ Sized H ∧
      ledSh H = (ledSh F).setGot (fillB (ledSh F).got first v.size) := by
  obtain ⟨hF, hn, hfree⟩ := free_of_B h
  exact hide_of_free hF hn hfree f

/-- The owed marks behind a payment, mark by mark. -/
theorem owed_paid (F : Fork) (i : Nat) :
    (F.paid i).owed.toList.map (·.added) = paidB (F.owed.toList.map (·.added)) i := by
  refine List.ext_getElem (by simp [paidB, Fork.paid]) fun j j1 j2 => ?_
  simp only [paidB, Fork.paid, List.getElem_map, List.getElem_zipIdx, Array.getElem_toList,
    Array.getElem_modify, Nat.zero_add]
  by_cases e : i = j
  · simp [e]
  · have e' : (j == i) = false := by simpa using fun a => e a.symm
    simp [e, e']

theorem ledSh_paid (F : Fork) (i : Nat) :
    ledSh (F.paid i) = (ledSh F).setOwed (paidB (ledSh F).owed i) := by
  show LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList ((F.paid i).owed.toList.map (·.added))
    F.planClaimsF (F.trees.toList.map treeSh) F.next F.LS.size F.nClaim F.thetaDrawnF
    F.kapMapF.toList F.doorShutF = _
  rw [owed_paid]
  rfl

/-- **A change of one virtual row**, where the change is seen through the row's shape as g. -/
theorem ledSh_onRow (F : Fork) (t r : Nat) (f : HRow → HRow) (g : RowSh → RowSh)
    (h : ∀ x, rowSh (f x) = g (rowSh x)) :
    ledSh (HTailF2.onRow F t r f) = (ledSh F).modRow t r g := by
  show LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList (F.owed.toList.map (·.added))
    F.planClaimsF ((F.trees.modify t fun X =>
      { X with rows := X.rows.modify r f }).toList.map treeSh) F.next F.LS.size F.nClaim
    F.thetaDrawnF F.kapMapF.toList F.doorShutF = _
  rw [map_modify _ _ _ treeSh (fun T => T.setRows (modAt T.rows r g)) fun X => by
    show TreeSh.mk X.name (X.kind == .symbols) X.R X.K ((X.rows.modify r f).toList.map rowSh)
      X.root.isSome = _
    rw [map_modify _ _ _ rowSh g h]
    rfl]
  rfl

/-- The arrays' marks, off the ledger. -/
theorem rooted_ledSh (F : Fork) : (ledSh F).rooted = F.trees.toList.map (·.root.isSome) := by
  show (F.trees.toList.map treeSh).map TreeSh.rooted = _
  rw [List.map_map]
  rfl

/-- **The chain's receipt of an array's commitment** (Fork.rootTaken, OnBytes/Model/Hide.lean): the
array's mark is set; nothing else of the shape turns. -/
theorem ledSh_taken (F : Fork) (t w : Nat) :
    ledSh (F.rootTaken t w) = (ledSh F).setRootedAt t := by
  show LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList (F.owed.toList.map (·.added)) F.planClaimsF
    ((F.trees.modify t fun X => { X with root := some w }).toList.map treeSh) F.next F.LS.size
    F.nClaim F.thetaDrawnF F.kapMapF.toList F.doorShutF = _
  rw [map_modify _ _ _ treeSh (fun T => T.setRooted true) fun _ => rfl]
  rfl

/-- A change of one member of a list, seen through a reader. -/
theorem map_modAt {α β : Type} (l : List α) (i : Nat) (f : α → α) (sh : α → β) (g : β → β)
    (h : ∀ x, sh (f x) = g (sh x)) : (modAt l i f).map sh = modAt (l.map sh) i g := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  by_cases e : j = i
  · rw [if_pos e, if_pos e, h]
  · rw [if_neg e, if_neg e]

/-- The marks behind it: the one mark is set. -/
theorem rooted_setRootedAt (L : LedSh) (i : Nat) :
    (L.setRootedAt i).rooted = modAt L.rooted i fun _ => true :=
  map_modAt L.trees i (fun T => T.setRooted true) TreeSh.rooted (fun _ => true) fun _ => rfl

/-! ## 4 A sumcheck's row -/

/-- **The test for a sumcheck's row**: its flags and sizes; its own slots are there and free. -/
def openB (p : PscSh) (L : LedSh) : Bool :=
  !p.rowMade && p.started && !p.degrees.isEmpty && p.challenges == p.degrees.length &&
    p.degrees.all (fun d => decide (1 ≤ d)) && freeB L p.first (takenSh p.degrees)

theorem open_of_B {p : Psc} {G : Fork} (h : openB (pscSh p) (ledSh G) = true) : Open p G := by
  unfold openB at h
  rw [taken_sh] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  obtain ⟨hs, hn, hfree⟩ := free_of_B h6
  have h1' : p.rowMade = false := by simpa [pscSh, PscSh.mk, PscSh.rowMade] using h1
  have h3' : p.vars.toList ≠ [] := by
    intro e
    simp [pscSh, PscSh.mk, PscSh.degrees, e] at h3
  have h4' : p.r.size = p.vars.size := by
    simpa [pscSh, PscSh.mk, PscSh.degrees, PscSh.challenges] using h4
  have h5' : ∀ w ∈ p.vars.toList, 1 ≤ w.d := by
    intro w hw
    have := List.all_eq_true.1 h5 w.d (List.mem_map.2 ⟨w, hw, rfl⟩)
    exact of_decide_eq_true this
  refine ⟨h1', h2, h4', h3', h5', hs, hn, fun j j1 j2 hf => ?_⟩
  have k := hfree (j - p.first) (by
    have : (pscSh p).first = p.first := rfl
    omega)
  have e : (pscSh p).first + (j - p.first) = j := by
    have : (pscSh p).first = p.first := rfl
    omega
  rw [e] at k
  exact k hf

/-! ## 5 A lookup's heard record and the smallness test's record: readers -/

/-- A piece of a call: array, row, first column, columns, columns rounded up, first key, a, b. -/
abbrev PieceSh : Type := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

namespace PieceSh
def mk (tree row c0 cols colsUp off a b : Nat) : PieceSh := (tree, row, c0, cols, colsUp, off, a, b)
def tree (p : PieceSh) : Nat := p.1
def row (p : PieceSh) : Nat := p.2.1
def c0 (p : PieceSh) : Nat := p.2.2.1
def cols (p : PieceSh) : Nat := p.2.2.2.1
def colsUp (p : PieceSh) : Nat := p.2.2.2.2.1
def off (p : PieceSh) : Nat := p.2.2.2.2.2.1
def a (p : PieceSh) : Nat := p.2.2.2.2.2.2.1
def b (p : PieceSh) : Nat := p.2.2.2.2.2.2.2
end PieceSh

def pieceSh (p : Piece) : PieceSh := PieceSh.mk p.tree p.row p.c0 p.Cp p.CP p.off p.a p.b

/-- A call with its pieces: the number of bits of a key's index, the pieces. -/
abbrev CallSh : Type := Nat × List PieceSh

namespace CallSh
def mk (n : Nat) (pieces : List PieceSh) : CallSh := (n, pieces)
def n (c : CallSh) : Nat := c.1
def pieces (c : CallSh) : List PieceSh := c.2
end CallSh

def callSh (c : CallZ) : CallSh := CallSh.mk c.call.n (c.pieces.toList.map pieceSh)

/-- What is kept of a lookup's heard record: the leaves' sumcheck; two numbers of owed claims; the
sizes of two points; the sizes of the calls' points; the counts of padding keys; a slot; a form's
shape; the number of rows. -/
abbrev HeardSh : Type :=
  PscSh × Nat × Nat × Nat × Nat × List Nat × List Nat × Nat × AffSh × Nat

namespace HeardSh
def mk (leaves : PscSh) (owedPlanes owedJoin zb0 zb1 : Nat) (zk pub : List Nat) (sBit : Nat)
    (cEnd : AffSh) (rows : Nat) : HeardSh :=
  (leaves, owedPlanes, owedJoin, zb0, zb1, zk, pub, sBit, cEnd, rows)
def leaves (g : HeardSh) : PscSh := g.1
def owedPlanes (g : HeardSh) : Nat := g.2.1
def owedJoin (g : HeardSh) : Nat := g.2.2.1
def zb0 (g : HeardSh) : Nat := g.2.2.2.1
def zb1 (g : HeardSh) : Nat := g.2.2.2.2.1
def zk (g : HeardSh) : List Nat := g.2.2.2.2.2.1
def pub (g : HeardSh) : List Nat := g.2.2.2.2.2.2.1
def sBit (g : HeardSh) : Nat := g.2.2.2.2.2.2.2.1
def cEnd (g : HeardSh) : AffSh := g.2.2.2.2.2.2.2.2.1
def rows (g : HeardSh) : Nat := g.2.2.2.2.2.2.2.2.2
end HeardSh

def heardSh (g : Forest.Heard) : HeardSh :=
  HeardSh.mk (pscSh g.leaves) g.owedPlanes g.owedJoin g.zb0.size g.zb1.size
    (g.zk.toList.map (·.size)) g.shape.pub.toList g.sBit (affSh g.cEnd) g.rows.size

/-- What is kept of the smallness test's record: the heard record; two numbers of the lookup's
shape; the planes' array; the test on the padding key; the host's count of padding places; the call
of the low digits and that of the high digits; the number of the claim on the key vectors. -/
abbrev TlSh : Type :=
  Option HeardSh × Nat × Nat × Nat × Bool × Option (List Nat) × CallSh × CallSh × Option Nat

namespace TlSh
def mk (heard : Option HeardSh) (kT cK planes : Nat) (padKey : Bool) (laid : Option (List Nat))
    (low high : CallSh) (joinObj : Option Nat) : TlSh :=
  (heard, kT, cK, planes, padKey, laid, low, high, joinObj)
def heard (t : TlSh) : Option HeardSh := t.1
def kT (t : TlSh) : Nat := t.2.1
def cK (t : TlSh) : Nat := t.2.2.1
def planes (t : TlSh) : Nat := t.2.2.2.1
def padKey (t : TlSh) : Bool := t.2.2.2.2.1
def laid (t : TlSh) : Option (List Nat) := t.2.2.2.2.2.1
def low (t : TlSh) : CallSh := t.2.2.2.2.2.2.1
def high (t : TlSh) : CallSh := t.2.2.2.2.2.2.2.1
def joinObj (t : TlSh) : Option Nat := t.2.2.2.2.2.2.2.2
/-- The call of the low digits for q = 0, of the high digits else: as HTailF2.zOf has it. -/
def callAt (t : TlSh) (q : Nat) : CallSh := if q == 0 then t.low else t.high
def setJoinObj (t : TlSh) (j : Option Nat) : TlSh :=
  mk t.heard t.kT t.cK t.planes t.padKey t.laid t.low t.high j
end TlSh

def tlSh (tl : HTailF2) : TlSh :=
  TlSh.mk (tl.heard.map heardSh) tl.f9.kT tl.f9.cK tl.ix.BZ (padKeyDigits tl)
    ((laidDigits tl).map (·.toList)) (callSh tl.z1) (callSh tl.z2) tl.joinObj9

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.affSh_ofConst
#print axioms VerifiableInference.Desc.First.Shape.affSh_slot
#print axioms VerifiableInference.Desc.First.Shape.affSh_ent
#print axioms VerifiableInference.Desc.First.Shape.foldl_push_map
#print axioms VerifiableInference.Desc.First.Shape.affSh_addMul
#print axioms VerifiableInference.Desc.First.Shape.affSh_add
#print axioms VerifiableInference.Desc.First.Shape.affSh_sub
#print axioms VerifiableInference.Desc.First.Shape.claims_push
#print axioms VerifiableInference.Desc.First.Shape.taken_sh
#print axioms VerifiableInference.Desc.First.Shape.affSh_addSlots
#print axioms VerifiableInference.Desc.First.Shape.affSh_rowForm
#print axioms VerifiableInference.Desc.First.Shape.map_modify
#print axioms VerifiableInference.Desc.First.Shape.fillB_zip
#print axioms VerifiableInference.Desc.First.Shape.free_get
#print axioms VerifiableInference.Desc.First.Shape.sized_of_B
#print axioms VerifiableInference.Desc.First.Shape.free_of_B
#print axioms VerifiableInference.Desc.First.Shape.got_fill
#print axioms VerifiableInference.Desc.First.Shape.hide_of_free
#print axioms VerifiableInference.Desc.First.Shape.hide_of_B
#print axioms VerifiableInference.Desc.First.Shape.owed_paid
#print axioms VerifiableInference.Desc.First.Shape.ledSh_paid
#print axioms VerifiableInference.Desc.First.Shape.ledSh_onRow
#print axioms VerifiableInference.Desc.First.Shape.rooted_ledSh
#print axioms VerifiableInference.Desc.First.Shape.ledSh_taken
#print axioms VerifiableInference.Desc.First.Shape.map_modAt
#print axioms VerifiableInference.Desc.First.Shape.rooted_setRootedAt
#print axioms VerifiableInference.Desc.First.Shape.open_of_B
