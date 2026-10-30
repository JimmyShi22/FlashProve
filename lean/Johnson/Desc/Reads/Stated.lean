-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Stated.lean: THE STATEMENT of the row claim_read_same_index, with what is spent
of it. No proof of the row: the row is stated over letters, and no letters are filled here.

The matter. A kind of block writes forms that name entries of the vector of reads U3. The smallness
test ties each entry of U3 to a sum of committed cells: by its own tables, each with a matrix, a
length, a first entry and weights. The relation that the link is to prove speaks of cells by the
tensors' coordinates. Nothing that the verifier tests compares the two namings: if a form names the
entry of another run of cells, or a table is laid with other weights, an honest prover of another
relation is accepted. The row says that the two namings agree.

THE ROW (it is to speak of the one written description at the release's plan):
  ClaimReadSameIndex L: at every link and every state at which the tables are closed,
    (L) every table of the third vector has as many weights as its run is long (lensB);
    (A) for every use of a read by a clause of the relation: at the place that the form names, the
        smallness test's table has just the cells, in their order, and the weights that are meant;
    (T) form by form: AS A LINEAR FORM ON U3, the form's entries of U3, each with the reading of its
        coefficient, are the uses of that form, each at its place with the coefficient that the
        clause gives it: whatever values stand at the places of U3, the two sums are equal. So two
        entries of one form cannot change places unless the readings of their coefficients are
        equal, and an entry cannot stand twice where it is meant once unless the reading of its
        coefficient is 0. It binds the meaning and not the writing: a place may be written twice, or
        two terms merged. Every entry of U3 lies inside its row.
  Order of the quantifiers: for all links, for all states, for all uses; then there are a table's
  number, the table, a column and a segment.
LETTERS (Letters K): the links, the states, "the tables are closed"; the smallness test's record and
  list of tables; the kinds' forms; and, for each use, THINGS THAT ARE TO BE MADE APART:
  place and the form's number from the kind's text; read, coef, len and cell from the relation's
  clause: the name of the read that the clause means, the coefficient with which it takes the sum,
  and the cells by the tensor's coordinates and the relation's own address of a cell, with no index
  of a read in them; wts from the kind's declaration of the read. Whoever makes cell, coef or wts
  from the table's or the form's side has a true and empty row: see Limits.
WHY (L). Weights are read with 0 beyond the array. A table whose array is shorter than its run has
  the weight 0 inside the run; if what is meant was made from the same short array, (A) holds, and
  cells of the run go unweighted with no refusal. WHO OWES (L): it stands under "for all states with
  closed tables", so it must hold at EVERY such state, also at one that the verifier refuses later.
  So at each link either the arrays' lengths follow from what is heard and from the plan, as a law
  of the hearing, or the letter AtClose must carry the test. Where tables are first laid with empty
  arrays and filled later, AtClose is the closing and not the laying. (L) IS NOT THE WHOLE OF IT: an
  array that is padded with 0 to the run's length passes. That a heard point has all its
  coordinates is asked by nothing here: a law of the hearing, which wants an owner at each link.
  lensB tests the letter funs: that this is the list of the state's record is not said.
TOOLS (for all sizes, weights and letters):
  Meant, SameIndex: what is meant at a place; the table at the place has it.
  Meant.ofRun, sameIndex_ofRun: where the cells are a run in one column, SameIndex is: the place,
    the matrix, the column, the first row, the length, the weights.
  named_of_same: the place is named by a table (Named, Cb/Pv/Tail/Places.lean).
  u3Tabs, sizeU3, phiU3: the typed sizes and weights of a record and a list of tables, the tables of
    the third vector alone. lensB: the test on lengths, a Boolean on the list.
  placeOf: the place of an entry of a form, where the entry's virtual row is the vector's own row:
    see Limits.
  entsU3, u3Value: a form's entries of U3, each as its place and its coefficient; their value at
    given values of the places.
  Letters.usesAt, Letters.clauseValue: the uses of the form with a given number; their value.
  Tied: (T) at one link and state.
  NotEmpty: there is a link, and EVERY link has a state with closed tables and a form whose part in
    U3 is not the zero form.
  IsReading: the letter val is the map of a reading (Reading, OnBytes/Model/HideLaws.lean).
  NotEmpty and IsReading stand in no clause of the row: whoever fills the letters owes both beside
    it.
WHY A LINEAR FORM, AND NOT PLACES ALONE. "The place of a use is named by its form, and every place
  that a form names is the place of a use of that form" is true of a text that swaps two entries
  inside one form. From (T) there follows, on places: where the uses' coefficients do not add up to
  0 the form has an entry; at a place that no use names the form's coefficients add up to 0.
  Neither is proved here; take the values 1 at the place and 0 elsewhere.
WHAT (T) LEANS ON. The statement on places does not read val. (T) compares readings, and is worth
  what val is worth: at a val that takes an element other than 0 to 0, a form may name a place that
  no use has, with that element for its coefficient, and (T) holds (free_val_member,
  Reads/Teeth.lean [not in this library]). So IsReading is asked: val takes the programs' 0, 1, sum,
  difference and
  product to those of K. Such a map into a ring with 1 ≠ 0 takes no element that has an inverse to 0
  (tooth_free_val, Reads/Teeth.lean [not in this library]: the same text is then refused). That
  every element whose
  residues are not all 0 has an inverse is not proved here.
WHAT IS SPENT:
  means_of_same: in front of the smallness test's round there is ONE family of small integer
    matrices with the committed packing such that, for EVERY e with SameIndex, the entry of U3 at
    e's place is the sum of e's cells under e's weights.
  spent: the same from the row, for all uses of a link; and form by form: the value of the form's
    part in U3, at the committed U3, is the uses' sums of cells, each times the clause's
    coefficient.

A Meant holds the address of EACH cell, and not a run (a matrix, a column, a first row, a length). A
relation addresses cells one by one; that the cells of a block of features follow each other in one
column is a fact to be shown, so it stands inside the statement. sameIndex_ofRun: the form with a
run.

Scope. At files in scope the plan is fixed, and the row is a law of the description, once for all.
Beyond scope the public files choose the plan: there the like is a law of the planner for every
admitted file, or a test on the plan. Neither is stated here.

Uses of `verify-on-bytes`'s records (OnBytes/Model/): HTailF2 and HFun, as the record and the list
of tables in sizeU3, phiU3, lensB and two letters, through OnBytes.Tie.Pv.Tail.sizeOf; Aff and Ent,
as the forms and their entries in placeOf, entsU3, u3Value and one letter; Reading, the record of
OnBytes/Model/HideLaws.lean, in IsReading. No routine of that program is named.

Limits. Not said: that the relation means the model; a kind's algebra at true sums, beyond the
coefficients of the entries of U3: a form's slots, its constant and its entries of other arrays are
not read; smallness; any count of errors; that the weights are fixed before the matrix is drawn;
tables of the first vector; the digits' lookup; completeness; hiding.
VIRTUAL ROWS. An entry of a form names a VIRTUAL row of its array, a public combination of the
array's rows (Ent, OnBytes/Model/Hide.lean). placeOf, (T) and spent take that number for U3's own
row, and the letter cols for the number of the array's columns. So they speak of U3 only where, for
every r, virtual row r of U3's array has the weight 1 on row r and 0 on all other rows, and cols is
the number of that array's columns in the state. uEnt (OnBytes/Model/Look.lean) says the same of the
entries that it makes, and does not test it. Neither is a letter, a premise or a clause here: it is
owed by whoever takes spent's sum for a form's value (Aff.value, OnBytes/Model/HideLaws.lean), and
it wants an owner at each link.
THE READING. A coefficient is compared behind val. In the row val is a free letter: the laws of a
reading are asked by IsReading, beside the row, and no theorem of this file spends them. spent's sum
is formed in K from the readings one by one; that it is the reading of the form's value in the
programs' field is not said.
THE FORM'S NUMBER. Which form stands for which clause is the letter formNo. The letters hold no
clause: a text that moves an entry from one clause's form into another's, with formNo read off that
text, meets (T). formNo is worth its making.
The letter read is read in Reads/DeclRow.lean alone. The letters are free: the row is worth what
their making is worth. (L) is spent by no theorem: it shuts a silent case of (A).

-/
import Cb.Pv.Tail.PlacesOne
import OnBytes.Tie.Pv.Tail.SizeOf
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun Aff Ent Reading)

/-! ## 1. What is meant at a place, and that the table there has it (tools) -/

/-- What is meant at one place of the vector of reads: a sum of cells under weights.
It does not say who means it. -/
structure Meant (K : Type) where
  /-- the place in the vector of reads -/
  pos : ℕ
  /-- the number of cells -/
  len : ℕ
  /-- cell number j, for j below len: its matrix, its column, its row -/
  cell : ℕ → ℕ × ℕ × ℕ
  /-- the weight of cell number j -/
  w : ℕ → K

/-- **The table at the place has what is meant.** There are a table (number n), a column c and a
segment sg, inside the sizes, such that: (I) the place is that of (n, c, sg); (II) the table's
length is the number of cells, and cell number j is row sg * len + j of column c of its matrix;
(III) the table's weight number j is the weight of cell number j.
It asks nothing beyond len, and nothing of any other place. -/
def SameIndex {K : Type} (t : TSize) (phi : ℕ → ℕ → K) (e : Meant K) : Prop :=
  ∃ (n : ℕ) (T : Tab) (c sg : ℕ), t.tabs[n]? = some T ∧ T.mat < t.NM ∧ c < t.k T.mat ∧
    sg < t.m T.mat / T.len ∧
    e.pos = T.start + c * (t.m T.mat / T.len) + sg ∧
    e.len = T.len ∧
    ∀ j, j < T.len → e.cell j = (T.mat, c, sg * T.len + j) ∧ phi n j = e.w j

/-- The place is named by a table. -/
theorem named_of_same {K : Type} {t : TSize} {phi : ℕ → ℕ → K} {e : Meant K}
    (h : SameIndex t phi e) : Named t e.pos := by
  obtain ⟨n, T, c, sg, h1, h2, h3, h4, h5, -, -⟩ := h
  exact ⟨n, T, c, sg, h1, h2, h3, h4, h5⟩

/-- What is meant, where the cells are a run: rows row0, row0 + 1, ... of one column. -/
def Meant.ofRun {K : Type} (pos mat col row0 len : ℕ) (w : ℕ → K) : Meant K :=
  ⟨pos, len, fun j => (mat, col, row0 + j), w⟩

/-- At a run: the place, the matrix, the column, the first row, the length, the weights. -/
theorem sameIndex_ofRun {K : Type} (t : TSize) (phi : ℕ → ℕ → K) (pos mat col row0 len : ℕ)
    (w : ℕ → K) :
    SameIndex t phi (Meant.ofRun pos mat col row0 len w) ↔
      ∃ (n : ℕ) (T : Tab) (c sg : ℕ), t.tabs[n]? = some T ∧ T.mat < t.NM ∧ c < t.k T.mat ∧
        sg < t.m T.mat / T.len ∧
        pos = T.start + c * (t.m T.mat / T.len) + sg ∧
        mat = T.mat ∧ col = c ∧ row0 = sg * T.len ∧ len = T.len ∧
        ∀ j, j < T.len → phi n j = w j := by
  constructor
  · rintro ⟨n, T, c, sg, h1, h2, h3, h4, h5, h6, h7⟩
    have h0 : 0 < T.len := by
      rcases Nat.eq_zero_or_pos T.len with h | h
      · rw [h, Nat.div_zero] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · exact h
    have e0 : (mat, col, row0 + 0) = (T.mat, c, sg * T.len + 0) := (h7 0 h0).1
    simp only [Prod.mk.injEq, Nat.add_zero] at e0
    exact ⟨n, T, c, sg, h1, h2, h3, h4, h5, e0.1, e0.2.1, e0.2.2, h6, fun j hj => (h7 j hj).2⟩
  · rintro ⟨n, T, c, sg, h1, h2, h3, h4, h5, e1, e2, e3, h6, h7⟩
    refine ⟨n, T, c, sg, h1, h2, h3, h4, h5, h6, fun j hj => ⟨?_, h7 j hj⟩⟩
    show (mat, col, row0 + j) = (T.mat, c, sg * T.len + j)
    rw [e1, e2, e3]

/-! ## 2. The smallness test's side, off its record and its list of tables (tools) -/

/-- The tables of the third vector, in the list's order. -/
def u3Tabs (funs : Array HFun) : List HFun := funs.toList.filter fun Fn => Fn.tree == 2

/-- The typed sizes of a record, with the tables of the third vector alone. A table of the first
vector has places in another vector: it must not answer for a place of U3. -/
def sizeU3 (tl : HTailF2) (funs : Array HFun) : TSize :=
  { OnBytes.Tie.Pv.Tail.sizeOf tl with
    tabs := (u3Tabs funs).map fun Fn => ⟨Fn.mat, Fn.len, Fn.start⟩ }

/-- Weight j of table number n of these. val: the reading of an element of the programs' field. -/
def phiU3 {K : Type} (val : E → K) (funs : Array HFun) (n j : ℕ) : K :=
  val (((u3Tabs funs).getD n default).phi.getD j zeroE)

/-- **The test on lengths.** Every table of the third vector has as many weights as its run is long.
A Boolean on the public list. -/
def lensB (funs : Array HFun) : Bool := (u3Tabs funs).all fun Fn => Fn.phi.size == Fn.len

/-! ## 3. The text's side: the places that a form names (tools) -/

/-- The place of an entry in a vector that is laid in rows of cols entries. x.row is the number of a
VIRTUAL row of the array (Ent, OnBytes/Model/Hide.lean), and is taken here for the vector's own row.
So this is the entry's place in the vector only where, for every r, virtual row r of the array has
the weight 1 on row r and 0 on all other rows, and cols is the number of the array's columns.
Nothing here asks that: see Limits. -/
def placeOf (cols : ℕ) (x : Ent) : ℕ := x.row * cols + x.idx

/-- The entries of array number iU3 in the form f, in the form's order: each as its place and the
reading of its coefficient. An entry that stands twice is listed twice. -/
def entsU3 {K : Type} (val : E → K) (iU3 cols : ℕ) (f : Aff) : List (ℕ × K) :=
  (f.ents.toList.filter fun x => x.tree == iU3).map fun x => (placeOf cols x, val x.coef)

/-- The value of these entries where v stands at the places: the form's part in U3, as a linear form
in v. -/
def u3Value {K : Type} [CommRing K] (val : E → K) (iU3 cols : ℕ) (f : Aff) (v : ℕ → K) : K :=
  ((entsU3 val iU3 cols f).map fun p => p.2 * v p.1).sum

/-! ## 4. The letters -/

/-- The letters of the row. A use: one reading of an entry of U3 by one clause of the relation that
the link is to prove. -/
structure Letters (K : Type) where
  /-- the links' names, the verifier's states, the uses' names -/
  Link : Type
  State : Type
  Use : Type
  /-- the description's links -/
  links : List Link
  /-- the state stands where the link's list of tables is closed: all points of the weights are
  drawn, the smallness test's matrix is not. Whether U3 was heard by then is not asked. -/
  AtClose : Link → State → Prop
  /-- the reading of an element of the programs' field -/
  val : E → K
  /-- THE SMALLNESS TEST: its record and its list of tables -/
  tl : Link → State → HTailF2
  funs : Link → State → Array HFun
  /-- THE KINDS' TEXT: all forms of the link but the smallness test's own: claims, the lookup's
  among them, keys handed to the lookup, guests; the number of U3 among the link's arrays; the
  entries in a row of U3 -/
  forms : Link → State → List Aff
  iU3 : Link → ℕ
  cols : Link → ℕ
  /-- the uses of a link -/
  uses : Link → List Use
  /-- FROM THE KIND'S TEXT: the number, in the link's list of forms, of the form that stands for the
  use's clause, and the place that it names for this use -/
  formNo : Link → Use → ℕ
  place : Link → Use → ℕ
  /-- FROM THE RELATION'S CLAUSE: the name of the read that the clause means here: which matrix,
  under which weights; and the coefficient with which the clause takes the use's sum -/
  read : Link → Use → String
  coef : Link → State → Use → K
  /-- FROM THE RELATION'S CLAUSE: how many cells the use sums, and cell number j by the relation's
  own address (matrix, column, row) of the tensor's coordinates. No index of a read enters. -/
  len : Link → Use → ℕ
  cell : Link → Use → ℕ → ℕ × ℕ × ℕ
  /-- FROM THE KIND'S DECLARATION OF THE READ: the weight of cell number j -/
  wts : Link → State → Use → ℕ → K

variable {K : Type}

/-- What a use means, at the place that the form names for it. -/
def Letters.meant (L : Letters K) (l : L.Link) (s : L.State) (u : L.Use) : Meant K :=
  ⟨L.place l u, L.len l u, L.cell l u, L.wts l s u⟩

/-- The uses of the form number n of a link, in the list's order. -/
def Letters.usesAt (L : Letters K) (l : L.Link) (n : ℕ) : List L.Use :=
  (L.uses l).filter fun u => L.formNo l u == n

/-- The value of these uses where v stands at the places: each use's coefficient times the value at
its place. -/
def Letters.clauseValue [CommRing K] (L : Letters K) (l : L.Link) (s : L.State) (n : ℕ)
    (v : ℕ → K) : K :=
  ((L.usesAt l n).map fun u => L.coef l s u * v (L.place l u)).sum

/-- The typed sizes and the weights at a link and a state. -/
abbrev Letters.size (L : Letters K) (l : L.Link) (s : L.State) : TSize :=
  sizeU3 (L.tl l s) (L.funs l s)
@[inherit_doc Letters.size]
abbrev Letters.phi (L : Letters K) (l : L.Link) (s : L.State) : ℕ → ℕ → K :=
  phiU3 L.val (L.funs l s)

/-! ## 5. THE ROW -/

/-- **The uses are tied to the text, form by form.** Every use's number is that of a form of the
link. For every form of the link: its entries of U3 lie inside their rows; and its part in U3 is, as
a linear form, the sum of the uses of that form, each at its place with the clause's coefficient. -/
def Tied [CommRing K] (L : Letters K) (l : L.Link) (s : L.State) : Prop :=
  (∀ u ∈ L.uses l, L.formNo l u < (L.forms l s).length) ∧
  ∀ (n : ℕ) (f : Aff), (L.forms l s)[n]? = some f →
    (∀ x ∈ f.ents.toList, x.tree = L.iU3 l → x.idx < L.cols l) ∧
    ∀ v : ℕ → K, u3Value L.val (L.iU3 l) (L.cols l) f v = L.clauseValue l s n v

/-- **claim_read_same_index.** At every link, at every state with the tables closed:
(L) the test on lengths says yes; (A) for every use, the smallness test's table at the use's place
has the cells and the weights that are meant; (T): Tied.
It is true of letters without a state with closed tables, and (A) of a link without uses: see
NotEmpty. It does not say that the letters are a description's. -/
def ClaimReadSameIndex [CommRing K] (L : Letters K) : Prop :=
  ∀ l ∈ L.links, ∀ s, L.AtClose l s →
    lensB (L.funs l s) = true ∧
    (∀ u ∈ L.uses l, SameIndex (L.size l s) (L.phi l s) (L.meant l s u)) ∧
    Tied L l s

/-- The row is not empty at these letters: there is a link, and every link has a state with closed
tables at which the part in U3 of some form is not the zero form. With (T) there is then a use, and
(A) speaks of it. It does not say that the letter forms holds all forms of the link. -/
def NotEmpty [CommRing K] (L : Letters K) : Prop :=
  L.links ≠ [] ∧ ∀ l ∈ L.links,
    ∃ s, L.AtClose l s ∧ ∃ f ∈ L.forms l s, ∃ v, u3Value L.val (L.iU3 l) (L.cols l) f v ≠ 0

/-- **The letter val is a reading's map**: it takes the programs' 0, 1, sum, difference and product
to those of K. (T) compares coefficients behind val alone, so it is worth what val is worth. It does
not say that the map is one-to-one, or that 1 ≠ 0 in K: NotEmpty gives the second. -/
def IsReading [CommRing K] (L : Letters K) : Prop := ∃ ρ : Reading K, ρ.val = L.val

/-! ## 6. What is spent -/

/-- The sum of the cells of e in the matrices a, under e's weights. -/
def Meant.sum [CommRing K] (e : Meant K) (a : ℕ → ℕ → ℕ → ℤ) : K :=
  ∑ j ∈ Finset.range e.len, e.w j * ((a (e.cell j).1 (e.cell j).2.1 (e.cell j).2.2 : ℤ) : K)

/-- **What is spent.** In front of the smallness test's round: ONE family of integer matrices, small
and with the committed packing, such that at EVERY e with SameIndex the entry of U3 is e's sum. -/
theorem means_of_same [CommRing K] {t : TSize} (Θ : TLetters K t) {x : Θ.X} {msg : Θ.M}
    (h : relIn Θ.letters x msg) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i, i < t.m μ → |a μ c i| < 2 * (t.beta : ℤ)) ∧
      (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i', i' < Alg.symRows (t.m μ) →
        Θ.sym msg μ i' c =
          ((Alg.pack (t.rad : ℤ) (fun i : Fin (t.m μ) => a μ c i) i' : ℤ) : K)) ∧
      ∀ e : Meant K, SameIndex t (Θ.phi x) e → Θ.u3 msg e.pos = e.sum a := by
  obtain ⟨a, h1, h2, h3⟩ := reads_of_relIn Θ h
  refine ⟨a, h1, h2, ?_⟩
  rintro e ⟨n, T, c, sg, g1, g2, g3, g4, g5, g6, g7⟩
  unfold Meant.sum
  rw [g5, h3 n T g1 g2 c g3 sg g4, g6]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨e1, e2⟩ := g7 j (Finset.mem_range.1 hj)
  rw [e1, e2]

/-- **The same from the row**, at a link and a state with closed tables, at letters of the smallness
test whose weights are the list's: one family of matrices, small and with the committed packing, for
all uses; and for every form of the link: the value of its part in U3, at the committed U3, is the
sum of what the uses of that form mean, each times the clause's coefficient. -/
theorem spent [CommRing K] (L : Letters K) (H : ClaimReadSameIndex L) {l : L.Link}
    (hl : l ∈ L.links) {s : L.State} (hs : L.AtClose l s)
    (Θ : TLetters K (L.size l s)) {x : Θ.X}
    (hphi : Θ.phi x = L.phi l s) {msg : Θ.M} (h : relIn Θ.letters x msg) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < (L.size l s).NM → ∀ c, c < (L.size l s).k μ → ∀ i, i < (L.size l s).m μ →
        |a μ c i| < 2 * ((L.size l s).beta : ℤ)) ∧
      (∀ μ, μ < (L.size l s).NM → ∀ c, c < (L.size l s).k μ →
        ∀ i', i' < Alg.symRows ((L.size l s).m μ) →
          Θ.sym msg μ i' c =
            ((Alg.pack ((L.size l s).rad : ℤ) (fun i : Fin ((L.size l s).m μ) => a μ c i) i' : ℤ) :
              K)) ∧
      (∀ u ∈ L.uses l, Θ.u3 msg (L.place l u) = (L.meant l s u).sum a) ∧
      (∀ (n : ℕ) (f : Aff), (L.forms l s)[n]? = some f →
        u3Value L.val (L.iU3 l) (L.cols l) f (Θ.u3 msg) =
          ((L.usesAt l n).map fun u => L.coef l s u * (L.meant l s u).sum a).sum) := by
  obtain ⟨-, hA, hT⟩ := H l hl s hs
  obtain ⟨a, h1, h2, h3⟩ := means_of_same Θ h
  have hu : ∀ u ∈ L.uses l, Θ.u3 msg (L.place l u) = (L.meant l s u).sum a := fun u hu =>
    h3 (L.meant l s u) (by rw [hphi]; exact hA u hu)
  refine ⟨a, h1, h2, hu, fun n f hf => ?_⟩
  rw [(hT.2 n f hf).2 (Θ.u3 msg)]
  unfold Letters.clauseValue
  refine congrArg List.sum (List.map_congr_left fun u hu' => ?_)
  show L.coef l s u * Θ.u3 msg (L.place l u) = L.coef l s u * (L.meant l s u).sum a
  rw [hu u (List.mem_filter.1 hu').1]

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.named_of_same
#print axioms VerifiableInference.Reads.sameIndex_ofRun
#print axioms VerifiableInference.Reads.means_of_same
#print axioms VerifiableInference.Reads.spent
