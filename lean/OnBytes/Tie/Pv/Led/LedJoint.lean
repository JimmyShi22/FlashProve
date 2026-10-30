-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedJoint.lean: the public state between two blocks of a sub-proof, as one type.

A sub-proof of the programs' protocol tests no equation while its messages are read. Each check
becomes a claim: an affine form, in hidden values and in entries of committed arrays, that must
be 0. Cb/G6/Led.lean has the forms (Form, Aff) over a finite type J of entries and the list of
claims (Ledger). Cb/Sub/Joint.lean puts a ledger beside any block: its joint is a base joint on the
block's own statements, and the ledger. This file gives the statements and the base joint.

1. Addr, Lay: how the entries J are named. Each entry is a cell of an array (array, row, column)
   or an entry of the mask row (slot). J is any finite type; a lay gives each entry its address.
   Shape, Shape.J, Shape.lay: the entries of a written list of arrays and a number of slots.
2. Lay.hid, Lay.ent: the two kinds of term of a claim, as forms on J: a hidden value under a slot,
   and an entry of a virtual row (a public combination of the rows of one array, at one column).
3. Joint: the public state between two blocks. It holds what was shown for each slot, the claims
   that blocks have left for the ledger, and the statements that are still open, each an affine
   form with what its value is meant to be. Joint.Holds: what a value of Joint states of the
   committed entries. jointRels: the same as a relation at a joint of a chain (IOR.Rels).
4. batchAt: the one form of a list of claims with exponents. LedBatch.lean counts the elements at
   which a false list gives a true form.

What this file does not claim. Nothing is said about probabilities, about hiding, or about the
shipped Lean verifier; LedPort.lean reads that verifier's state in these types.


-/
import Cb.G6.Led
import Ior.Chain
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole Iop

/-! ## The entries and their addresses -/

/-- The address of an entry. -/
inductive Addr where
  /-- a cell: the number of the array, the row, the column -/
  | cell (arr row col : Nat)
  /-- the entry of the mask row that belongs to a slot -/
  | mask (slot : Nat)
  deriving DecidableEq, Repr

/-- A lay: each entry of J has an address, and no two have the same. The numbers of the arrays are
those of the verifier's own list; an array that is committed elsewhere (the key's matrix, an
earlier sub-proof's arrays, a message of the request) gets a number behind them.

What a lay does not say: when an entry is committed. A count of bad draws is for fixed entries, so
whoever states a block over J owes that the entries which the block's joints read (the mask row
among them) are committed before the block's draws. In the programs' protocol the mask row and the
symbol arrays go out in the sub-proof's first moment; the reads go out later. -/
structure Lay (J : Type) where
  /-- the address of an entry -/
  addr : J → Addr
  /-- no two entries have the same address -/
  inj : Function.Injective addr

/-- The public description of one array. -/
structure Arr where
  /-- the array's name -/
  name : String
  /-- the number of rows -/
  R : Nat
  /-- the number of columns -/
  K : Nat
  /-- the array is committed in this sub-proof, not elsewhere -/
  own : Bool := true
  deriving DecidableEq, Repr

/-- A written list of arrays, and the number of slots, which is the length of the mask row. -/
structure Shape where
  /-- the arrays, in the order of their numbers -/
  arrays : List Arr
  /-- the number of slots -/
  ns : Nat
  deriving DecidableEq, Repr

/-- A cell: array, row, column. -/
abbrev Shape.Cell (S : Shape) : Type :=
  (t : Fin S.arrays.length) × Fin (S.arrays.get t).R × Fin (S.arrays.get t).K

/-- The entries of a shape: cells, and entries of the mask row. -/
abbrev Shape.J (S : Shape) : Type := S.Cell ⊕ Fin S.ns

/-- The address of an entry of a shape. -/
def Shape.addr (S : Shape) : S.J → Addr
  | .inl c => .cell c.1.val c.2.1.val c.2.2.val
  | .inr j => .mask j.val

/-- The lay of a shape. -/
def Shape.lay (S : Shape) : Lay S.J where
  addr := S.addr
  inj := by
    rintro (⟨t, r, c⟩ | j) (⟨t', r', c'⟩ | j') h
    · simp only [Shape.addr, Addr.cell.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain rfl : t = t' := Fin.ext h1
      obtain rfl : r = r' := Fin.ext h2
      obtain rfl : c = c' := Fin.ext h3
      rfl
    · simp [Shape.addr] at h
    · simp [Shape.addr] at h
    · simp only [Shape.addr, Addr.mask.injEq] at h
      exact congrArg Sum.inr (Fin.ext h)

/-- The entries that tables of cells and of mask entries give. -/
def Lay.entries {E J : Type} (Y : Lay J) (cell : Nat → Nat → Nat → E) (mask : Nat → E) : J → E :=
  fun i => match Y.addr i with
    | .cell t r c => cell t r c
    | .mask j => mask j

/-! ## Affine forms: sums and multiples -/

section Algebra
variable {E J : Type} [Field E]

/-- The constant form v. -/
def affConst (v : E) : Aff E J := ⟨fun _ => 0, v⟩

/-- The form a + k b. -/
def affAddMul (a b : Aff E J) (k : E) : Aff E J :=
  ⟨fun j => a.co j + b.co j * k, a.c0 + b.c0 * k⟩

/-- The sum of the forms g x over a list. -/
def affSum {α : Type} (g : α → Aff E J) : List α → Aff E J
  | [] => affConst 0
  | x :: l => affAddMul (g x) (affSum g l) 1

/-- The one form of a list of claims with exponents: the sum of x^e times the claim, over the
members (e, claim). -/
def batchAt (x : E) (L : List (Nat × Form E J)) : Form E J :=
  ⟨fun j => (L.map fun p => x ^ p.1 * p.2.co j).sum, (L.map fun p => x ^ p.1 * p.2.tg).sum⟩

/-- The hidden value under slot j, as a form: what was shown, less the public factor times the
entry of the mask row that belongs to the slot. -/
def Lay.hid (Y : Lay J) (vp mf : Nat → E) (j : Nat) : Aff E J :=
  ⟨fun i => if Y.addr i = .mask j then -mf j else 0, vp j⟩

/-- Weights on the entries: wts on the rows of column col of array t, and 0 elsewhere. -/
def Lay.colW (Y : Lay J) (t : Nat) (wts : Nat → E) (col : Nat) : J → E :=
  fun i => match Y.addr i with
    | .cell a r c => if a = t ∧ c = col then wts r else 0
    | .mask _ => 0

/-- An entry of a virtual row, as a form: the combination wts of the rows of array t, at column
col. -/
def Lay.ent (Y : Lay J) (t : Nat) (wts : Nat → E) (col : Nat) : Aff E J := ⟨Y.colW t wts col, 0⟩

variable [Fintype J] (m : J → E)

/-- The entry of the mask row that belongs to slot j; 0 if J has none. -/
def Lay.maskAt (Y : Lay J) (j : Nat) : E := ∑ i, if Y.addr i = .mask j then m i else 0

/-- The cell (t, r, c); 0 if J has none. -/
def Lay.cellAt (Y : Lay J) (t r c : Nat) : E := ∑ i, if Y.addr i = .cell t r c then m i else 0

/-- The value of an entry of a virtual row. -/
def Lay.entryAt (Y : Lay J) (t : Nat) (wts : Nat → E) (col : Nat) : E :=
  ∑ i, Y.colW t wts col i * m i

theorem affConst_val (v : E) : (affConst v : Aff E J).val m = v := by
  simp [affConst, Aff.val]

theorem affAddMul_val (a b : Aff E J) (k : E) :
    (affAddMul a b k).val m = a.val m + b.val m * k := by
  have e : ∀ j, (a.co j + b.co j * k) * m j = a.co j * m j + b.co j * m j * k :=
    fun j => by ring
  simp only [affAddMul, Aff.val, e, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem affSum_val {α : Type} (g : α → Aff E J) (l : List α) :
    (affSum g l).val m = (l.map fun x => (g x).val m).sum := by
  induction l with
  | nil => simp [affSum, affConst_val]
  | cons x l ih => simp [affSum, affAddMul_val, ih]

theorem Lay.hid_val (Y : Lay J) (vp mf : Nat → E) (j : Nat) :
    (Y.hid vp mf j).val m = vp j - mf j * Y.maskAt m j := by
  have e : ∀ i, (if Y.addr i = .mask j then -mf j else 0) * m i =
      -mf j * (if Y.addr i = .mask j then m i else 0) := fun i => by
    split_ifs <;> ring
  simp only [Lay.hid, Aff.val, Lay.maskAt, e, ← Finset.mul_sum]
  ring

theorem Lay.ent_val (Y : Lay J) (t : Nat) (wts : Nat → E) (col : Nat) :
    (Y.ent t wts col).val m = Y.entryAt m t wts col := by
  simp only [Lay.ent, Aff.val, Lay.entryAt, add_zero]

/-- The gap of the claim "a = 0" is the value of a. -/
theorem claim_gap (a : Aff E J) : a.claim.gap m = a.val m := by
  unfold Aff.claim Form.gap Aff.val
  rw [sub_neg_eq_add]

theorem batchAt_gap (x : E) : ∀ L : List (Nat × Form E J),
    (batchAt x L).gap m = (L.map fun p => x ^ p.1 * p.2.gap m).sum
  | [] => by simp [batchAt, Form.gap]
  | p :: L => by
    have ih := batchAt_gap x L
    simp only [batchAt, Form.gap, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring

end Algebra

/-! ## The joint -/

/-- A statement that is still open: the value of a form is what it is meant to be, a function of
the committed entries. Examples: a sum over a cube that the next sumcheck starts from; the value
of a map at a point of challenges, for an end value that a later claim ties to an array. -/
structure Open (E J : Type) where
  /-- the form -/
  aff : Aff E J
  /-- what its value is meant to be -/
  means : (J → E) → E

/-- The public state between two blocks of a sub-proof: the statement of a block. The ledger of
the claims that have been added stands beside it (Cb/Sub/Joint.lean).

Slots. The hidden value under slot j is vp j - mf j * (entry j of the mask row). got j says that a
value has been put under the slot. The filled slots need not be a prefix of the slots; next counts
the slots that the messages have taken. A scalar of a sumcheck's own rounds is sent without a
mask: under its slot lies a coefficient of the hiding polynomial, with vp = 0 and mf = -1.

The two lists. owed: forms that must hold and that a block has left to its caller, who adds them
to the ledger or builds them into the start of another block. opens: what later blocks start from.

A form holds its coefficients on the entries written out, so it does not change when a further
slot is filled. pub is whatever other public data rides (points, challenges, sizes). -/
@[ext] structure Joint (P E J : Type) where
  /-- other public data -/
  pub : P
  /-- the array's commitment has been received -/
  com : Nat → Bool
  /-- the number of slots that the messages have taken -/
  next : Nat
  /-- a hidden value has been put under the slot -/
  got : Nat → Bool
  /-- what was shown for the slot -/
  vp : Nat → E
  /-- the public factor of the slot's mask entry -/
  mf : Nat → E
  /-- the claims left to the caller -/
  owed : Ledger E J
  /-- the open statements -/
  opens : List (Open E J)

namespace Joint
variable {P E J : Type} [Field E]

/-- The hidden value under slot j, as a form. -/
def hid (x : Joint P E J) (Y : Lay J) (j : Nat) : Aff E J := Y.hid x.vp x.mf j

/-- Puts a hidden value under slot j: shown - factor * (entry j of the mask row). -/
def fill (x : Joint P E J) (j : Nat) (shown factor : E) : Joint P E J :=
  { x with
    got := Function.update x.got j true
    vp := Function.update x.vp j shown
    mf := Function.update x.mf j factor }

/-- Puts the elements of v under the slots first, first + 1 and so on, all with one factor. -/
def fillRun (x : Joint P E J) (first : Nat) (v : List E) (factor : E) : Joint P E J :=
  match v with
  | [] => x
  | y :: l => (x.fill first y factor).fillRun (first + 1) l factor

/-- Takes the next n slots. -/
def take (x : Joint P E J) (n : Nat) : Joint P E J := { x with next := x.next + n }

/-- Notes that the commitment of array t has been received. -/
def commit (x : Joint P E J) (t : Nat) : Joint P E J :=
  { x with com := Function.update x.com t true }

/-- Leaves the claim that the form a is 0 to the caller. -/
def owe (x : Joint P E J) (a : Aff E J) : Joint P E J := { x with owed := x.owed ++ [a.claim] }

/-- The hidden value under another slot stays. -/
theorem fill_hid_ne (x : Joint P E J) (Y : Lay J) (j i : Nat) (y f : E) (h : i ≠ j) :
    (x.fill j y f).hid Y i = x.hid Y i := by
  simp only [hid, fill, Lay.hid, Function.update_of_ne h]

variable [Fintype J]

theorem hid_val (x : Joint P E J) (Y : Lay J) (j : Nat) (m : J → E) :
    (x.hid Y j).val m = x.vp j - x.mf j * Y.maskAt m j := Y.hid_val m _ _ _

/-- Every open statement is true of the entries m. -/
def Meant (x : Joint P E J) (m : J → E) : Prop := ∀ o ∈ x.opens, o.aff.val m = o.means m

/-- All that a joint states of the entries m: every owed claim holds, and every open statement is
true. -/
def Holds (x : Joint P E J) (m : J → E) : Prop := x.owed.Holds m ∧ x.Meant m

/-- Filling a slot changes neither list, so it changes nothing that the joint states. -/
theorem fill_holds (x : Joint P E J) (j : Nat) (y f : E) (m : J → E) :
    (x.fill j y f).Holds m ↔ x.Holds m := Iff.rfl

theorem owe_holds (x : Joint P E J) (a : Aff E J) (m : J → E) :
    (x.owe a).Holds m ↔ x.Holds m ∧ a.val m = 0 := by
  simp only [Holds, owe, Ledger.Holds, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun f hf => h1 f (Or.inl hf), h2⟩, (a.claim_holds m).1 (h1 _ (Or.inr rfl))⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    refine ⟨fun f hf => ?_, h2⟩
    rcases hf with hf | rfl
    · exact h1 f hf
    · exact (a.claim_holds m).2 h4

end Joint

instance {E J : Type} [Field E] [Fintype J] [DecidableEq E] (f : Form E J) (m : J → E) :
    Decidable (f.Holds m) := inferInstanceAs (Decidable (f.gap m = 0))

instance {E J : Type} [Field E] [Fintype J] [DecidableEq E] (L : Ledger E J) (m : J → E) :
    Decidable (L.Holds m) := inferInstanceAs (Decidable (∀ f ∈ L, f.Holds m))

instance {P E J : Type} [Field E] [Fintype J] [DecidableEq E] (x : Joint P E J) (m : J → E) :
    Decidable (x.Holds m) :=
  inferInstanceAs (Decidable ((∀ f ∈ x.owed, f.Holds m) ∧
    ∀ o ∈ x.opens, o.aff.val m = o.means m))

/-- The joint as a relation at a joint of a chain: the base joint beside which the ledger stands.
M: the committed messages; msg reads the entries off them. ok: which public states the soundness
property speaks of. The relation of the honest side and its relaxation are the same statement. -/
def jointRels {K M Wp P E J : Type} [Field E] [Fintype J] (Ex : ExtSpec)
    (ok : Joint P E J → Prop) (msg : M → J → E) (core : M × Wp → K) :
    IOR.Rels K (Joint P E J) Ex (M × Wp) :=
  ⟨fun x _ w => x.Holds (msg w.1), fun a w => a.1.Holds (msg w.1), fun a => ok a.1, core⟩

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.Lay.hid_val
#print axioms OnBytes.Road.Rows.batchAt_gap
#print axioms OnBytes.Road.Rows.Joint.owe_holds
