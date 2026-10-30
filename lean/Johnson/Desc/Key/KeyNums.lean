-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyNums.lean: the key file's table of joints: whose numbers.
Four definitions and small theorems.

Messages are numbered in two ways. A row of a statement, and the laws that other files state
over Means.Says, name an oracle message by its number in the chain's statement. The table of joints'
witness holds its messages under numbers of its own, one for the whole file (0 the index mask, 1 the
lookups' message, 2 V, 3 the folded row, 4 Omega, 5 the split's masks). A plan (KPlan) carries the
two maps: orc k, the statement's number of the witness's message k; num o, the way back.

  wordsBy num tbl   words by the statement's numbers, out of tables by the witness's numbers: at o
                    the table tbl k where num o = some k; 0 at a message that is no component.
                    The numbers alone: general in where the tables come from.
  entOf ρ R m       one message's table, read in the ring: ρ of KRead.val. The one reader.
  wordsOf ρ K R w   the words off the witness: ρ of valOf. It is wordsBy at K.num and at the tables
                    entOf ρ R (R.of w k) (wordsOf_eq).
  NumsOk K l        for every k of l: orc k is there, and num leads back to k. One round trip: it does
                    not say that no other message of the statement reads message k's table.
  NumsOnly K l      the other round trip: for every k of l: a number that num leads to k is orc k.
  wordsBy_num | wordsBy_none | wordsBy_at | wordsBy_one    what the words are at a number; one
                    message under two plans' numbers reads one table.
  wordsOf_num | wordsOf_none | wordsOf_at | words_one_message    the same at wordsOf.
  rowHolds_iff_says_words | _of_rowIn | rowsHold_iff_allSay    with rowHolds_iff_says: the
                    table's "a row holds at the witness" is Means.Says at wordsOf.
  mkOf_read | vOf_read    two named readers of the first chain's table are the words at the plan's
                    number.
  entOf_section     at a reader that writes a typed table back by a section of ρ, entOf is the table.

At silly members. num := fun _ => none: the words are 0 everywhere, so every row whose target reads 0
says its claim: NumsOk fails at every k. num := fun _ => some 0: all messages of the statement read
message 0's table: NumsOk K [0, 1] cannot hold. num := 0 ↦ 0 · 1 ↦ 1 · all else ↦ 2: NumsOk holds at
[0, 1, 2]; NumsOnly fails at 2. At a message that is no component (a fresh mask) the
words are 0: a row that names it is read at 0 there: KeyMeaning.lean's own flag: not paid here.

What rowHolds_iff_says_words serves, and what not. It serves a law of the form "for all words g: Says
St' r' g → Says St r g", at one chain, called at g := wordsOf. NOT a law that hands back "there are
words g": such g need not be the words of a witness. Not across two chains: each has its plan. Not
where g has true tables at messages that are no component: wordsOf is 0 there.
Its own two premises: hs (what the letter same is: a fact on the letters, held by nobody's promise) and
hoff (from Means.RowIn: for an open row, of whoever shows that the adding's tests have passed).

What is not claimed: that R.of w k is the table that a pin pins (KeyTies.ReadsPinned); that a state's
own copy of a number is the plan's; anything on a typed witness. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyMeaning
import Johnson.Desc.Key.RowHoldsSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

/-- **Words by the statement's numbers, out of tables by the witness's numbers.** -/
def wordsBy {GE : Type} [Zero GE] (num : Nat → Option Nat) (tbl : Nat → Part → Nat → GE) :
    Means.Words GE := fun o part i =>
  match num o with
  | some k => tbl k part i
  | none => 0

/-- **For every k of l: orc k is there, and num leads back from it to k.** One round trip. -/
def NumsOk (K : KPlan) (l : List Nat) : Prop := ∀ k ∈ l, ∃ o, K.orc k = some o ∧ K.num o = some k

/-- **For every k of l: no other message of the statement reads message k's table.** The other round
trip. WITHOUT IT: num := 0 ↦ 0 · 1 ↦ 1 · every other number ↦ 2 meets NumsOk at [0, 1, 2], and every
mask, fold and rider then reads V's table. -/
def NumsOnly (K : KPlan) (l : List Nat) : Prop := ∀ k ∈ l, ∀ o, K.num o = some k → K.orc k = some o

theorem NumsOnly.mono {K : KPlan} {l l' : List Nat} (h : NumsOnly K l) (hs : ∀ k ∈ l', k ∈ l) :
    NumsOnly K l' := fun k hk => h k (hs k hk)

/-- Under both, message k's table stands at one number of the statement, and at no other. -/
theorem nums_unique {K : KPlan} {l : List Nat} (h : NumsOnly K l) {k o o' : Nat} (hk : k ∈ l)
    (h1 : K.num o = some k) (h2 : K.num o' = some k) : o = o' :=
  Option.some.inj ((h k hk o h1).symm.trans (h k hk o' h2))

theorem NumsOk.mono {K : KPlan} {l l' : List Nat} (h : NumsOk K l) (hs : ∀ k ∈ l', k ∈ l) :
    NumsOk K l' := fun k hk => h k (hs k hk)

section
variable {GE : Type} [Zero GE] (num num' : Nat → Option Nat) (tbl : Nat → Part → Nat → GE)

theorem wordsBy_num {o k : Nat} (h : num o = some k) : wordsBy num tbl o = tbl k := by
  funext part i
  simp only [wordsBy, h]

theorem wordsBy_none {o : Nat} (h : num o = none) : wordsBy num tbl o = fun _ _ => 0 := by
  funext part i
  simp only [wordsBy, h]

/-- One message under two numberings reads one table. -/
theorem wordsBy_one {o o' k : Nat} (h : num o = some k) (h' : num' o' = some k) :
    wordsBy num tbl o = wordsBy num' tbl o' := by
  rw [wordsBy_num num tbl h, wordsBy_num num' tbl h']

end

theorem wordsBy_at {GE : Type} [Zero GE] {K : KPlan} {l : List Nat} (h : NumsOk K l)
    (tbl : Nat → Part → Nat → GE) {k : Nat} (hk : k ∈ l) :
    ∃ o, K.orc k = some o ∧ wordsBy K.num tbl o = tbl k := by
  obtain ⟨o, h1, h2⟩ := h k hk
  exact ⟨o, h1, wordsBy_num K.num tbl h2⟩

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE) {Cells M : Type} (K K' : KPlan)
  (R : KRead Cells M)

/-- **One message's table, read in the ring.** -/
def entOf (m : M) (part : Part) (i : Nat) : GE := ρ.val (R.val m part i)

/-- **The words off the witness, by the statement's numbers.** -/
def wordsOf (w : Wit Cells Unit M) : Means.Words GE := fun o part i => ρ.val (valOf K R w o part i)

/-- The words off the witness are the tables of its messages, renumbered. -/
theorem wordsOf_eq (w : Wit Cells Unit M) :
    wordsOf ρ K R w = wordsBy K.num fun k => entOf ρ R (R.of w k) := by
  funext o part i
  unfold wordsOf wordsBy valOf entOf
  cases K.num o with
  | some k => rfl
  | none => exact ρ.zero

theorem wordsOf_num (w : Wit Cells Unit M) {o k : Nat} (h : K.num o = some k) :
    wordsOf ρ K R w o = entOf ρ R (R.of w k) := by
  rw [wordsOf_eq, wordsBy_num _ _ h]

theorem wordsOf_none (w : Wit Cells Unit M) {o : Nat} (h : K.num o = none) :
    wordsOf ρ K R w o = fun _ _ => 0 := by
  rw [wordsOf_eq, wordsBy_none _ _ h]

/-- **The statement's message number orc k bears the table of the witness's message k.** -/
theorem wordsOf_at {l : List Nat} (h : NumsOk K l) (w : Wit Cells Unit M) {k : Nat} (hk : k ∈ l) :
    ∃ o, K.orc k = some o ∧ wordsOf ρ K R w o = entOf ρ R (R.of w k) := by
  obtain ⟨o, h1, h2⟩ := h k hk
  exact ⟨o, h1, wordsOf_num ρ K R w h2⟩

/-- **One message under two statements' numbers reads one table.** -/
theorem words_one_message (w : Wit Cells Unit M) {o o' k : Nat} (h : K.num o = some k)
    (h' : K'.num o' = some k) : wordsOf ρ K R w o = wordsOf ρ K' R w o' := by
  rw [wordsOf_num ρ K R w h, wordsOf_num ρ K' R w h']

/-- **The table's "a row holds at the witness" is Means.Says at the words off the witness.** -/
theorem rowHolds_iff_says_words (hs : R.same = fun a b => ρ.val a = ρ.val b) (St : Statement)
    (w : Wit Cells Unit M) (r : OnBytes.Row) (hoff : OffTables ρ St r) :
    RowHolds R.same St (valOf K R w) r ↔ Means.Says ρ St r (wordsOf ρ K R w) := by
  rw [hs]
  exact rowHolds_iff_says ρ St (valOf K R w) r hoff

/-- The same for a row that has passed the adding's tests. -/
theorem rowHolds_iff_says_words_of_rowIn (hs : R.same = fun a b => ρ.val a = ρ.val b)
    (St : Statement) (G : OnBytes.Group) (w : Wit Cells Unit M) (r : OnBytes.Row)
    (hin : Means.RowIn St G r) :
    RowHolds R.same St (valOf K R w) r ↔ Means.Says ρ St r (wordsOf ρ K R w) :=
  rowHolds_iff_says_words ρ K R hs St w r (offTables_of_rowIn ρ St G r hin)

/-- The same for a list of rows. -/
theorem rowsHold_iff_allSay (hs : R.same = fun a b => ρ.val a = ρ.val b) (St : Statement)
    (w : Wit Cells Unit M) (rs : List OnBytes.Row) (hoff : ∀ r ∈ rs, OffTables ρ St r) :
    (∀ r ∈ rs, RowHolds R.same St (valOf K R w) r) ↔ Means.AllSay ρ St rs (wordsOf ρ K R w) :=
  ⟨fun h r hr => (rowHolds_iff_says_words ρ K R hs St w r (hoff r hr)).1 (h r hr),
    fun h r hr => (rowHolds_iff_says_words ρ K R hs St w r (hoff r hr)).2 (h r hr)⟩

/-- A mask entry, as the table reads it, is the words' entry at the slot. -/
theorem mkOf_read (w : Wit Cells Unit M) (s : Slot) :
    ρ.val (mkOf K R w s) = wordsOf ρ K R w s.oracle .mask s.index := rfl

/-- V's entry, as the first chain's table reads it, is the words' entry at V's number. -/
theorem vOf_read (St : Statement) (w : Wit Cells Unit M) (c : Nat) {o : Nat}
    (h : K.num o = some 2) :
    ρ.val (vOf K R St w c) = wordsOf ρ K R w o .main ((linLayW St.codes K.lin).index c) := by
  rw [wordsOf_num ρ K R w h]
  rfl

/-- At a reader that writes a typed table back by a section of ρ, entOf is the table. -/
theorem entOf_section (tab : M → Part → Nat → GE) (rep : GE → E) (hrep : ∀ x, ρ.val (rep x) = x)
    (hval : ∀ m part i, R.val m part i = rep (tab m part i)) (m : M) : entOf ρ R m = tab m := by
  funext part i
  unfold entOf
  rw [hval, hrep]

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.wordsOf_eq
#print axioms VerifiableInference.Desc.Key.wordsOf_at
#print axioms VerifiableInference.Desc.Key.words_one_message
#print axioms VerifiableInference.Desc.Key.rowHolds_iff_says_words
#print axioms VerifiableInference.Desc.Key.rowHolds_iff_says_words_of_rowIn
#print axioms VerifiableInference.Desc.Key.rowsHold_iff_allSay
#print axioms VerifiableInference.Desc.Key.vOf_read
#print axioms VerifiableInference.Desc.Key.entOf_section
#print axioms VerifiableInference.Desc.Key.NumsOk.mono
#print axioms VerifiableInference.Desc.Key.wordsBy_num
#print axioms VerifiableInference.Desc.Key.wordsBy_none
#print axioms VerifiableInference.Desc.Key.wordsBy_one
#print axioms VerifiableInference.Desc.Key.wordsBy_at
#print axioms VerifiableInference.Desc.Key.wordsOf_num
#print axioms VerifiableInference.Desc.Key.wordsOf_none
#print axioms VerifiableInference.Desc.Key.mkOf_read
#print axioms VerifiableInference.Desc.Key.NumsOnly.mono
#print axioms VerifiableInference.Desc.Key.nums_unique
