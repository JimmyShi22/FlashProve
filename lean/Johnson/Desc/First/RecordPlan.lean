-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/RecordPlan.lean: THE PLAN's TERMS FOR FOUR READERS OF THE CARRIED RECORD, AND
THAT EACH READER IS ITS TERM WHERE A TEST ON THE RECORD SAYS YES. Definitions with code and small
theorems; no Mathlib. No border, no promise, no witness: these stand in Johnson/Road/K4/Rec/.

  `seatP own places n o`: the plan's term for `K9.seatAt own book o`
    (Johnson/Desc/First/Batch/FormsIn.lean): entry o of the first n of the plan's list of (tree,
    part), if it is a member of own.
  `rowBitsP M n o part`, `placeBitsP cs M n o part`: for `Statement.rowBits` and
    `Statement.placeBits` (OnBytes/Iop/Ground.lean): off entry o of the first n of the plan's list
    of the messages' shapes.
  `maskSeatP`: for `K9.maskSeat`. `arrayInP`: for `K9.arrayIn`. `atMoment1P`: for `K9.atMoment1`.
  `oneRowP`, `ownRowP`, `hasEntP`: for three readers of the ledger's arrays: "the array has one own
    row", `K9.ownRow` (Johnson/Desc/First/Batch/ReaderOf.lean), `Fork.hasEnt`
    (OnBytes/Model/Hide.lean): off the plan's list of looks. `readsThereP`: for "array number i of
    the link's list is in the layout, of the second sending, has a row and at least k columns".
  `look_at`, **`ownRow_is`**, **`hasEnt_is`**, `oneRow_is`: where the arrays' looks are the list T.
  **`seatAt_is`**: where "K12.seatsCarried"'s test says yes (`seatsCarriedB`,
    Johnson/Desc/K12/Door/DoorBools.lean) and the book has n places.
  **`rowBits_is`**, **`placeBits_is`**: where "K12.msgShapes"'s test says yes (`msgShapesB`,
    Johnson/Desc/K12/Door/MsgShapes.lean) and the statement has n messages; the second also: the
    statement's codes are cs.

OBJECT: none. USER: Johnson/Road/K4/Rec/. LETTERS: own, places, M, cs, n.

Limits. Beyond the first n both sides answer nothing (or 0): equal, and worth nothing: a test on the
plan that spends a term should ask o < n. K04_law, the law of K4's block itself, IS NOT PROVED BY
THIS. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.FillSent
import Johnson.Desc.First.Batch.ReaderOf
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.RecordPlan
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (seatAt ownRow)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open VerifiableInference.Desc.First.FillSent (SentData TreeLook treeLook whereIsP maskP)

/-! ## The terms -/

/-- The seat of message number o, by the plan's list of (tree, part), of which n are sent. -/
def seatP (own places : List (Nat × Nat)) (n o : Nat) : Option (Nat × Nat) :=
  ((places.take n)[o]?).bind fun x => if own.contains x then some x else none

/-- The row bits of a table of message number o, by the plan's list of shapes. -/
def rowBitsP (M : List OracleShape) (n o : Nat) (part : OnBytes.Part) : Nat :=
  match (M.take n)[o]? with
  | some x => ceilLog2 (x.rows part)
  | none => 0

/-- The place bits likewise. -/
def placeBitsP (cs : Codes) (M : List OracleShape) (n o : Nat) (part : OnBytes.Part) : Nat :=
  match (M.take n)[o]? with
  | some x =>
    if x.rows part == 0 then 0
    else match part with
      | .main => (cs.base.getD x.code default).logEll
      | .mask => (cs.mask.getD x.maskCode default).logEll
  | none => 0

/-- The seat of the message with segment m's mask row. -/
def maskSeatP (shape : Params.ReqShape) (d : SentData) (own places : List (Nat × Nat))
    (n m : Nat) : Option (Nat × Nat) :=
  (maskP shape d m).bind fun o => seatP own places n o

/-- Array number t of the segment's list is in the layout, sent, and seated in own. -/
def arrayInP (layout : Params.ReqLayout) (arrs : Array (Nat × String)) (d : SentData)
    (own places : List (Nat × Nat)) (n m t : Nat) : Option Params.ReqArray :=
  (arrs[t]?).bind fun b =>
    (reqArray layout b.1 b.2).bind fun A =>
      (whereIsP d m b.1 A.message).bind fun o => (seatP own places n o).map fun _ => A

/-- The array b of the layout is of segment m's own second sending. -/
def atMoment1P (shape : Params.ReqShape) (m : Nat) (b : Nat × String) (A : Params.ReqArray) :
    Bool :=
  b.1 == m &&
    match (shape.link[b.1]?).bind fun l => l.messages[A.message]? with
    | some x => x.moment == 1
    | none => false

/-- Array number i of the link's list is in the layout, of segment m's second sending, has a row and
at least k columns. -/
def readsThereP (shape : Params.ReqShape) (layout : Params.ReqLayout)
    (arrs : Array (Nat × String)) (m i k : Nat) : Bool :=
  match arrs[i]? with
  | none => false
  | some b =>
    match reqArray layout b.1 b.2 with
    | none => false
    | some Ar => atMoment1P shape m b Ar && (decide (0 < Ar.sizeI) && decide (k ≤ Ar.sizeC))

/-- Array number i of the ledger has one own row. -/
def oneRowP (T : List TreeLook) (i : Nat) : Bool := (T[i]?).any fun X => X.1 == 1

/-- The entry names row 0 of an array with one own row. -/
def ownRowP (T : List TreeLook) (x : Ent) : Bool :=
  match T[x.tree]? with
  | some X => X.1 == 1 && x.row == 0
  | none => false

/-- The arrays have the entry that x names, inside the columns that its row's weights hold. -/
def hasEntP (T : List TreeLook) (x : Ent) : Bool :=
  match T[x.tree]? with
  | none => false
  | some X =>
    match X.2.2[x.row]? with
    | none => false
    | some r => decide (r.1 ≤ x.idx) && decide (x.idx - r.1 < r.2)

/-! ## Each reader is its term -/

/-- The look of array number i. -/
theorem look_at {trees : Array HTree} {T : List TreeLook} (h : trees.toList.map treeLook = T)
    (i : Nat) : T[i]? = (trees[i]?).map treeLook := by
  rw [← h, List.getElem?_map, Array.getElem?_toList]

theorem oneRow_is {trees : Array HTree} {T : List TreeLook} (h : trees.toList.map treeLook = T)
    (i : Nat) : ((trees[i]?).any fun X => X.R == 1) = oneRowP T i := by
  unfold oneRowP
  rw [look_at h i]
  cases trees[i]? <;> rfl

/-- **"Row 0 of an array with one own row" is the plan's.** -/
theorem ownRow_is {F : Fork} {T : List TreeLook} (h : F.trees.toList.map treeLook = T) (x : Ent) :
    ownRow F x = ownRowP T x := by
  unfold ownRow ownRowP
  rw [look_at h x.tree]
  cases F.trees[x.tree]? <;> rfl

/-- **"The arrays have the entry" is the plan's.** -/
theorem hasEnt_is {trees : Array HTree} {T : List TreeLook} (h : trees.toList.map treeLook = T)
    (x : Ent) : Fork.hasEnt trees x = hasEntP T x := by
  unfold Fork.hasEnt hasEntP
  rw [look_at h x.tree]
  cases trees[x.tree]? with
  | none => rfl
  | some X =>
    show (match X.rows[x.row]? with
      | none => false
      | some r => decide (r.L0 ≤ x.idx) && decide (x.idx - r.L0 < r.L.size)) =
      (match (X.rows.toList.map fun r => (r.L0, r.L.size))[x.row]? with
      | none => false
      | some r => decide (r.1 ≤ x.idx) && decide (x.idx - r.1 < r.2))
    rw [List.getElem?_map, Array.getElem?_toList]
    cases X.rows[x.row]? <;> rfl

/-- **The book's seat is the plan's.** -/
theorem seatAt_is {L : Laid} {B : TreeBook} {n : Nat} (h : seatsCarriedB L B = true)
    (hn : B.place.size = n) (own : List (Nat × Nat)) (o : Nat) :
    seatAt own B o = seatP own L.places n o := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.place.toList = L.places.take B.place.size := eq_of_beq h.1.1.1
  unfold seatAt seatP
  rw [← hn, ← e, Array.getElem?_toList]

/-- The shape of message number o is the plan's. -/
theorem shape_is {M : List OracleShape} {st : Statement} {n : Nat} (h : msgShapesB M st = true)
    (hn : st.oracles.size = n) (o : Nat) : (st.oracles[o]?).map (·.shape) = (M.take n)[o]? := by
  unfold msgShapesB at h
  rw [Bool.and_eq_true] at h
  have e : st.oracles.toList.map (·.shape) = M.take st.oracles.size := eq_of_beq h.1
  rw [← hn, ← e, List.getElem?_map, Array.getElem?_toList]

/-- **The row bits are the plan's.** -/
theorem rowBits_is {M : List OracleShape} {st : Statement} {n : Nat}
    (h : msgShapesB M st = true) (hn : st.oracles.size = n) (o : Nat) (part : OnBytes.Part) :
    st.rowBits o part = rowBitsP M n o part := by
  unfold Statement.rowBits rowBitsP
  rw [← shape_is h hn o]
  cases st.oracles[o]? <;> rfl

/-- **The place bits are the plan's**, where the statement's codes are. -/
theorem placeBits_is {cs : Codes} {M : List OracleShape} {st : Statement} {n : Nat}
    (h : msgShapesB M st = true) (hn : st.oracles.size = n) (hc : st.codes = cs) (o : Nat)
    (part : OnBytes.Part) : st.placeBits o part = placeBitsP cs M n o part := by
  unfold Statement.placeBits placeBitsP
  rw [← shape_is h hn o, hc]
  cases st.oracles[o]? <;> rfl

end VerifiableInference.Desc.First.RecordPlan

#print axioms VerifiableInference.Desc.First.RecordPlan.ownRow_is
#print axioms VerifiableInference.Desc.First.RecordPlan.hasEnt_is
#print axioms VerifiableInference.Desc.First.RecordPlan.seatAt_is
#print axioms VerifiableInference.Desc.First.RecordPlan.rowBits_is
#print axioms VerifiableInference.Desc.First.RecordPlan.placeBits_is
