-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadStated.lean: the statement of the row claim_read_same_index at the output
head's link, for the four forms of the acceptance policy.

The row is stated here and not proved. The letters of Reads/Stated.lean are filled from three texts
that were written apart; what is still a letter is listed below. Of the row's three clauses, (T) is
shown at these letters under named premises in Reads/HeadTiedFour.lean (`tied_head`). Clauses (A)
and (L) are shown nowhere.

The three texts.
  The relation (Inst/Model/Head/Trace.lean). Its clauses (B2), (B3) (`sB2`, `sB3`: sums over the
    positions) and (B4), (Z) (`dB4`, `dZ`: at each position) read six hidden numbers, each some
    bytes of the ledger, which are features of the matrix hr. (Z) also reads the table values ex,
    three limbs for each vocabulary entry, which are features `fEx l v` of the matrix hf. Where a
    feature's cell stands in the link's matrices: `cellsH` and `placeIn`
    (Johnson/Road/HeadPlace.lean).
  The kind's text (Johnson/Desc/Kinds/Head.lean, HeadCells.lean). The forms mean, count, clip and
    table name entries of the reads rowCount, rowAtCosts and wideAtCosts, at indices written with
    `NR`, `Number.digits`, `d`, `JV` and `S2`.
  The kind's declaration (`Read.of`, Head.lean): which matrix a read sums, under which weights.

A use is byte l of a hidden number in one of the four clauses, or limb l of the table values of one
block of S2 vocabulary entries in (Z).
  From the relation: `Hid.bytes`, `Clause.hids`, `Clause.factor`, `Use.coef`, `Use.means`,
    `Use.len`, `Use.cell`. No index of a read is in them. The coefficient is 256 ^ l, low byte and
    low limb first, times the policy's C for the number b in (B2). The read that is meant: (B2) and
    (B3) are plain sums over the positions, so rowCount; (B4) and (Z) hold at each position and are
    tested at one point, so rowAtCosts and wideAtCosts.
  From the kind's text: `Clause.no`, `Clause.form`, `Use.read`, `Use.index`. The place is the read's
    first entry plus the index.
  From the declaration: `declOf`, whose weights are the use's.

The row at the head. It is to speak of the one written description at the release's plan.
  `HeadClaim P`: every read's name is found in the link's table of its tables; the sizes by which
    the relation's cells are addressed are the full size's (`NumH`, Johnson/Road/HeadPlace.lean);
    the letters are not empty (`NotEmpty`); the letter val is a reading's map (`IsReading`,
    Reads/Stated.lean); and `ClaimReadSameIndex P.letters`.
  `tooth_missing_name`: a missing name makes it false. A reader that is silent there (`Seat.start`)
    would read from place 0 on. `tooth_no_state`: so do letters without a state with closed tables.
  `HeadClaimByDecls P`: the same in two halves, the join and the address (Reads/DeclRow.lean), over
    the five declarations of the head's own reads. `headClaim_of_decls`: it gives `HeadClaim`. This
    is the form in which the row is to be shown at the head: it asks `Whole` and the name too.

Why `NumH`. `cellsH` is the verifier's rule at free sizes. Its tie to the library's own places of
the cells holds under `NumH`. With h and L free, whoever fills them from the tables' record has half
of the address by make.

Not asked, and wanting an owner: that the heard points have all their coordinates: zt as many as the
positions have bits, zl as a block's features, the sumcheck's challenges likewise. The kind's
equality weights are 0 from 2 ^ (the point's size) on. At a state whose zt is one coordinate short
the declared weights of rowAtCosts are 0 on the upper half of the positions. A table whose array is
padded with 0 to the run's length agrees and passes the test on lengths. On paper both statements
are then true, and in clip and table half the positions go unweighted. The two sides agree there, so
it is no fault of this row. It is a law of the hearing.

What is still a letter (`HeadLetters K`): the reading of the field; `verify-on-bytes`'s two records
h and L of the head's sizes, by which `cellsH` addresses; the kind's sizes and policy; at a state
the relation's own request, whose policy gives the coefficient C (that it is the kind's C is asked
by (T), through the reading of the field); the seat (the number of U3 and the entries in a row of
it; each read's first entry, if its name is found, and its table's length; each matrix's first part
and number of parts in the link's list); the states and "the tables are closed"; and at a state the
request, the lookup's points, what the head has heard, the smallness test's record and its list of
tables. In the library at hand the head's link is walked with `verify-on-bytes`'s routines and the
kind's text has no seat that runs. So these cannot be filled from one description.

Tools, proved here because they come at once. Each ties a definition of this file to its text.
  `hids_are`, `clauses_are`: the six numbers' bytes and the four clauses are the relation's, by rfl.
  `value_bytes`, `ex_limbs`: byte l of a hidden number and limb l of a table value stand with 256 ^
    l in the relation, by rfl: whence `Use.coef`.
  `addr_hr`, `addr_hf`: the addresses are those at which `cellsH` reads, by rfl.
  `cellOf_placeIn`: the declarations' rule is `placeIn`'s, the row and the column swapped, by rfl.
  `bytes_eq_digits`: the relation's first byte and number of bytes of each hidden number are `NR`
    plus the kind's first digit, and its number of digits.
  `policy_at`: the form with a clause's number, in the kind's list of the policy's forms, is the
    form that stands for the clause.
  `means_is_read`: the read that a use's clause means is the read in which the text names the entry.

Of OnBytes/Model/ this file names `Head.Shape` and `Head.HL`, as letters in `addrHr` and `addrHf`,
and `HTailF2`, `HFun` and `Aff` as Reads/Stated.lean does.

Limits. Four forms of 35 are read: not the 29 forms of the final normalization, the two of the
logits, the nine keys, or the lookup's claims on the multiplicities' bits. (The head's two guests
are clip and table, two of the four.) So (T) speaks of these four forms alone. The equations of
Reads/DeclRow.lean (`TablesAre`, `FunsAre`), which no clause of `ClaimByDecls` asks, are false of
the head's five declarations at an honest list: the link's tables are of three kinds, laid in turns.
What the head can show alone is `PartsLaid` (Reads/Join.lean). None of the four forms reads the
stream, which is borrowed and renumbered (`Border.cell` in `cellsH`): that address comes with the
normalization's forms. `Clause.hids` is read off the relation's text by eye: `clauses_are` shows
each clause with just these numbers in it, and no theorem speaks of the list. The relation is
written at the full size (1,024 positions, 202,048 vocabulary entries). At another number of
positions, of features in a block or of features the row is meant to fail, through clause (A) and
`NumH`; no theorem says so. The kind's V is read through the padded `JV` alone, so every V with the
same `JV` gives the same letters. The kind's sh, F, MF, KF and epsF are read by no letter, and the
forms' constants are compared by no clause of the row. Nothing is said of the layers' and
attention's links: their kinds' texts declare their reads elsewhere, and are to fill the record of
Reads/Decl.lean first. Nothing on soundness.


-/
import Johnson.Desc.Reads.DeclRow
import Johnson.Desc.Kinds.Head
import Johnson.Road.HeadPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtHead

open OnBytes (E mulE)
open OnBytes.Model (HTailF2 HFun Aff)
open OnBytes.Road (Mats)
open OnBytes.Road.Hd (placeIn cellsH NumH)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (nT nV fEx)

/-! ## 1. From the relation -/

/-- The relation's six hidden numbers of a position. -/
inductive Hid | c | b | u | k | z | zs

/-- A hidden number's first byte in the ledger, which is its first feature of hr, and the number of
its bytes. -/
def Hid.bytes : Hid → ℕ × ℕ
  | .c => (99, 5) | .b => (104, 1) | .u => (105, 5) | .k => (110, 5) | .z => (115, 2)
  | .zs => (117, 3)

/-- The value of a hidden number at position i, as the relation forms it. -/
def Hid.value {K : Type} [CommRing K] (x : Hid) (t : Inst.Model.Head.Cells K) (i : ℕ) : K :=
  Inst.Model.Ledger.b256 (fun n => Inst.Model.Head.Dv t n i) x.bytes.1 x.bytes.2

/-- The six are the relation's. -/
theorem hids_are {K : Type} [CommRing K] (t : Inst.Model.Head.Cells K) (i : ℕ) :
    Inst.Model.Head.hidC t i = Hid.c.value t i ∧ Inst.Model.Head.hidB t i = Hid.b.value t i ∧
    Inst.Model.Head.hidU t i = Hid.u.value t i ∧ Inst.Model.Head.hidK t i = Hid.k.value t i ∧
    Inst.Model.Head.hidZ t i = Hid.z.value t i ∧ Inst.Model.Head.hidS t i = Hid.zs.value t i :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A hidden number is its bytes in base 256, low byte first; a byte is its cell of hr plus 128. -/
theorem value_bytes {K : Type} [CommRing K] (x : Hid) (t : Inst.Model.Head.Cells K) (i : ℕ) :
    x.value t i = ∑ l ∈ Finset.range x.bytes.2, 256 ^ l * (128 + t.hr (x.bytes.1 + l) i) := rfl

/-- A table value is its three limbs in base 256, low limb first, plus an offset. -/
theorem ex_limbs {K : Type} [CommRing K] (t : Inst.Model.Head.Cells K) (v i : ℕ) :
    Inst.Model.Head.ex t v i = 8421505 + ∑ l ∈ Finset.range 3, 256 ^ l * t.hf (fEx l v) i := rfl

/-- The relation's four clauses on the policy. -/
inductive Clause | B2 | B3 | B4 | Z

/-- The hidden numbers that a clause reads. -/
def Clause.hids : Clause → List Hid
  | .B2 => [.c, .b, .u] | .B3 => [.b, .z] | .B4 => [.c, .k] | .Z => [.zs]

/-- The four clauses, written with the six numbers. -/
theorem clauses_are {K : Type} [CommRing K] (t : Inst.Model.Head.Cells K)
    (y : Inst.Model.Head.Req) (i : ℕ) :
    Inst.Model.Head.sB2 t y =
      ∑ i ∈ Finset.range nT, (y.rhoC i : K) *
        (Hid.c.value t i + (y.pol.C : K) * Hid.b.value t i + Hid.u.value t i) -
        (y.pol.theta : K) * (y.NB : K) ∧
    Inst.Model.Head.sB3 t y =
      ∑ i ∈ Finset.range nT, (y.rhoC i : K) * (Hid.b.value t i + Hid.z.value t i) -
        (if 0 < y.NB then (y.pol.cap : K) else 0) ∧
    Inst.Model.Head.dB4 t y i =
      (y.rhoC i : K) * (Hid.c.value t i + Hid.k.value t i - (y.pol.C : K)) ∧
    Inst.Model.Head.dZ t y i =
      (y.rhoC i : K) * (Hid.zs.value t i + ∑ v ∈ Finset.range nV, Inst.Model.Head.ex t v i -
        2 ^ 24) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Where the relation's cell of feature φ of hr at position i stands in the link's matrices: the
matrix, the column, the row. -/
def addrHr (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL) (φ i : ℕ) : ℕ × ℕ × ℕ :=
  (h.NHf + 1 + (placeIn L.kR (L.mR / h.T) h.T φ i).1, (placeIn L.kR (L.mR / h.T) h.T φ i).2.2,
    (placeIn L.kR (L.mR / h.T) h.T φ i).2.1)

/-- The same for hf. -/
def addrHf (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL) (φ i : ℕ) : ℕ × ℕ × ℕ :=
  (0 + (placeIn L.k (L.m / h.T) h.T φ i).1, (placeIn L.k (L.m / h.T) h.T φ i).2.2,
    (placeIn L.k (L.m / h.T) h.T φ i).2.1)

/-- The rule of Reads/Decl.lean is placeIn's, with the matrix in front and the last two swapped:
cellOf returns (matrix, column, row), placeIn (part, row, column). -/
theorem cellOf_placeIn (mat m k T F p : ℕ) :
    cellOf mat m k T F p = (mat + (placeIn k (m / T) T F p).1, (placeIn k (m / T) T F p).2.2,
      (placeIn k (m / T) T F p).2.1) := rfl

/-- cellsH reads hr at this address. A list of matrices takes the matrix, the row, the column. -/
theorem addr_hr {K : Type} (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (M : Mats K) (φ i : ℕ) :
    (cellsH h L b M).hr φ i =
      M (addrHr h L φ i).1 (addrHr h L φ i).2.2 (addrHr h L φ i).2.1 := rfl

/-- cellsH reads hf at this address. -/
theorem addr_hf {K : Type} (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (M : Mats K) (φ i : ℕ) :
    (cellsH h L b M).hf φ i =
      M (addrHf h L φ i).1 (addrHf h L φ i).2.2 (addrHf h L φ i).2.1 := rfl

/-- A use. byte cl x l: byte l of the hidden number x in the clause cl, summed over the positions.
ex l blk: limb l of the table values of the vocabulary entries S2 blk, ..., S2 blk + S2 - 1 in the
clause (Z), summed over these and the positions. -/
inductive Use
  | byte (cl : Clause) (x : Hid) (l : ℕ)
  | ex (l blk : ℕ)

/-- The use's clause. -/
def Use.clause : Use → Clause
  | .byte cl _ _ => cl
  | .ex _ _ => .Z

/-- The factor with which a clause takes a hidden number: the policy's C for b in (B2), else 1. -/
def Clause.factor {K : Type} [CommRing K] (y : Inst.Model.Head.Req) : Clause → Hid → K
  | .B2, .b => (y.pol.C : K)
  | _, _ => 1

/-- The coefficient with which the use's clause takes the use's sum: the low byte, and the low limb,
first. -/
def Use.coef {K : Type} [CommRing K] (y : Inst.Model.Head.Req) : Use → K
  | .byte cl x l => cl.factor y x * 256 ^ l
  | .ex l _ => 256 ^ l

/-- The name of the read that the use's clause means. (B2), (B3) are plain sums over the positions
with a cost. (B4), (Z) hold at each such position, and are tested at one point on the positions. -/
def Use.means : Use → String
  | .byte .B2 _ _ => "rowCount"
  | .byte .B3 _ _ => "rowCount"
  | .byte .B4 _ _ => "rowAtCosts"
  | .byte .Z _ _ => "rowAtCosts"
  | .ex _ _ => "wideAtCosts"

section Sized
variable [Head.Sizes]

/-- All uses of the four clauses. -/
def usesH : List Use :=
  ([Clause.B2, .B3, .B4, .Z].flatMap fun cl => cl.hids.flatMap fun x =>
    (List.range x.bytes.2).map fun l => Use.byte cl x l) ++
  (List.range 3).flatMap fun l => (List.range (nV / Norm.S2)).map fun blk => Use.ex l blk

/-- The number of cells that a use sums. -/
def Use.len : Use → ℕ
  | .byte _ _ _ => nT
  | .ex _ _ => Norm.S2 * nT

/-- Cell number j of a use, by the relation's features and its address. -/
def Use.cell (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL) : Use → ℕ → ℕ × ℕ × ℕ
  | .byte _ x l => fun j => addrHr h L (x.bytes.1 + l) j
  | .ex l blk => fun j => addrHf h L (fEx l (Norm.S2 * blk + j / nT)) (j % nT)

/-! ## 2. From the kind's text -/

/-- The read in which the form of a clause names its hidden numbers (summed, atCosts). -/
def Clause.read : Clause → Head.Read
  | .B2 => .rowCount | .B3 => .rowCount | .B4 => .rowAtCosts | .Z => .rowAtCosts

/-- The read of a use. -/
def Use.read : Use → Head.Read
  | .byte cl _ _ => cl.read
  | .ex _ _ => .wideAtCosts

/-- The kind's name for a hidden number. -/
def Hid.number : Hid → Head.Number
  | .c => .paid | .b => .over | .u => .slackMean | .k => .slackClip | .z => .slackCap
  | .zs => .slackTable

/-- The index at which the kind's text names the entry (summed, atCosts, tableValuesAtCosts in
Johnson/Desc/Kinds/HeadCells.lean). -/
def Use.index : Use → ℕ
  | .byte _ x l => NR + x.number.digits.1 + l
  | .ex l blk => (4 * Norm.d + (3 + l) * Head.JV) / Norm.S2 + blk

/-- The form that stands for a clause. -/
def Clause.form [Head.Policy] [Head.Request] [FinalNorm.In] [Head.Reads] : Clause → Form
  | .B2 => Head.mean | .B3 => Head.count | .B4 => Head.clip | .Z => Head.table

/-- Its number in the kind's list of the policy's forms. -/
def Clause.no : Clause → ℕ
  | .B2 => 0 | .B3 => 1 | .B4 => 2 | .Z => 3

/-- The form with that number is the clause's. -/
theorem policy_at [Head.Policy] [Head.Request] [FinalNorm.In] [Head.Reads] (cl : Clause) :
    Head.policy[cl.no]? = some cl.form := by
  cases cl <;> rfl

omit [Head.Sizes] in
/-- The relation's bytes of a hidden number are the kind's digits behind the norm's NR. -/
theorem bytes_eq_digits (x : Hid) : x.bytes = (NR + x.number.digits.1, x.number.digits.2) := by
  cases x <;> rfl

/-! ## 3. The seat, and the kind's declarations -/

/-- Where the link's frame seats the head's reads and matrices. -/
structure Seat where
  /-- the number of U3 among the link's arrays; the entries in a row of it -/
  iU3 : ℕ
  cols : ℕ
  /-- what the link's table of its tables returns for a read's name: the read's first entry in U3;
  none: no table has the name -/
  first : Head.Read → Option ℕ
  /-- the number of a read's entries: its table's length -/
  count : Head.Read → ℕ
  /-- a matrix's first part in the link's list of matrices, and the number of its parts -/
  mat : Head.Matrix → ℕ × ℕ

/-- A read's first entry, as a reader has it that is silent where the name is missing. -/
def Seat.start (S : Seat) (r : Head.Read) : ℕ := (S.first r).getD 0

/-- Entry i of a read as a variable of a form: the entry of U3 at the read's first entry plus i. -/
@[reducible] def Seat.reads (S : Seat) : Head.Reads :=
  ⟨fun r i => Aff.ent S.iU3 ((S.start r + i) / S.cols) ((S.start r + i) % S.cols)⟩

/-- A read's name. -/
def readName : Head.Read → String
  | .wideAtKeys => "wideAtKeys" | .wideAtCosts => "wideAtCosts" | .actAtLogits => "actAtLogits"
  | .rowAtCosts => "rowAtCosts" | .rowCount => "rowCount"

omit [Head.Sizes] in
/-- The read that a use's clause means is the read in which the text names the entry. -/
theorem means_is_read (u : Use) : u.means = readName u.read := by
  rcases u with ⟨cl, x, l⟩ | ⟨l, blk⟩
  · cases cl <;> rfl
  · rfl

/-- The make, the run's length and the weights one by one, of weights as a kind declares them. -/
def makeOf : Weights → Make
  | .long _ _ => .long Norm.S2
  | .short _ => .short
@[inherit_doc makeOf] def lenOf : Weights → ℕ
  | .long _ _ => Norm.S2 * Norm.T
  | .short _ => Norm.T
@[inherit_doc makeOf] def flat : Weights → ℕ → E
  | .long a b => fun j => mulE (a (j / Norm.T)) (b (j % Norm.T))
  | .short b => b

/-- A read of the head's, as the kind declares it (Read.of), at a seat. -/
def declOf [Head.Request] [FinalNorm.In] [Head.Heard] (S : Seat) (r : Head.Read) : ReadDecl E :=
  { name := readName r
    mat := (S.mat (Head.Read.of r).1).1
    parts := (S.mat (Head.Read.of r).1).2
    make := makeOf (Head.Read.of r).2
    len := lenOf (Head.Read.of r).2
    count := S.count r
    start := S.start r
    w := flat (Head.Read.of r).2 }

end Sized

/-! ## 4. The letters that are left, and the row -/

/-- What is still a letter at the head's link. -/
structure HeadLetters (K : Type) where
  /-- the reading of an element of the programs' field -/
  val : E → K
  /-- the sizes by which the relation's cells are addressed -/
  h : OnBytes.Model.Head.Shape
  L : OnBytes.Model.Head.HL
  /-- the kind's sizes and policy; the seat -/
  sizes : Head.Sizes
  policy : Head.Policy
  seat : Seat
  /-- the verifier's states; the link's list of tables is closed -/
  State : Type
  AtClose : State → Prop
  /-- at a state: the relation's own request, with the policy's three numbers -/
  req : State → Inst.Model.Head.Req
  /-- at a state: the request; the lookup's points; what the head has heard -/
  request : State → Head.Request
  points : State → FinalNorm.In
  heard : State → Head.Heard
  /-- at a state: the smallness test's record and its list of tables -/
  tl : State → HTailF2
  funs : State → Array HFun

variable {K : Type}

/-- The declaration of a read at a state. -/
def HeadLetters.decl (P : HeadLetters K) (s : P.State) (r : Head.Read) : ReadDecl E :=
  letI := P.sizes
  letI := P.request s
  letI := P.points s
  letI := P.heard s
  declOf P.seat r

/-- The five declarations of the head's own reads. -/
def HeadLetters.decls (P : HeadLetters K) (s : P.State) : List (ReadDecl E) :=
  [.wideAtKeys, .wideAtCosts, .actAtLogits, .rowAtCosts, .rowCount].map (P.decl s)

/-- The letters of Reads/Stated.lean at the head's link, for the four forms of the policy. -/
def HeadLetters.letters [CommRing K] (P : HeadLetters K) : Letters K where
  Link := Unit
  State := P.State
  Use := Use
  links := [()]
  AtClose := fun _ s => P.AtClose s
  val := P.val
  tl := fun _ s => P.tl s
  funs := fun _ s => P.funs s
  forms := fun _ s =>
    letI := P.sizes
    letI := P.policy
    letI := P.request s
    letI := P.points s
    letI := P.seat.reads
    Head.policy
  iU3 := fun _ => P.seat.iU3
  cols := fun _ => P.seat.cols
  uses := fun _ =>
    letI := P.sizes
    usesH
  formNo := fun _ u => u.clause.no
  place := fun _ u =>
    letI := P.sizes
    P.seat.start u.read + u.index
  read := fun _ u => u.means
  coef := fun _ s u => u.coef (P.req s)
  len := fun _ u =>
    letI := P.sizes
    u.len
  cell := fun _ u =>
    letI := P.sizes
    u.cell P.h P.L
  wts := fun _ s u j => P.val ((P.decl s u.read).w j)

/-- What both forms of the statement ask first: every read's name is found; the sizes by which the
relation's cells are addressed are the full size's; the letters are not empty; the letter val is a
reading's map. -/
def HeadLetters.Sane [CommRing K] (P : HeadLetters K) : Prop :=
  (∀ r, (P.seat.first r).isSome = true) ∧ NumH P.h P.L ∧ NotEmpty P.letters ∧ IsReading P.letters

/-- **claim_read_same_index at the head's link, for the four forms of the policy.** The letters are
sane; and the row at the head's letters. -/
def HeadClaim [CommRing K] (P : HeadLetters K) : Prop :=
  P.Sane ∧ ClaimReadSameIndex P.letters

/-- **The same in two halves**: the letters are sane; every table of the third vector has as
many weights as its run is long; each of the five declared reads is whole and joined to the
smallness test's tables; each use is addressed in the declared read of the name that its clause
means; the uses are tied to the four forms. -/
def HeadClaimByDecls [CommRing K] (P : HeadLetters K) : Prop :=
  P.Sane ∧ ClaimByDecls P.letters fun _ s => P.decls s

theorem headClaim_of_decls [CommRing K] (P : HeadLetters K) (H : HeadClaimByDecls P) :
    HeadClaim P :=
  ⟨H.1, claim_of_decls P.letters _ H.2⟩

/-- Where a read's name is missing the statement fails, whatever stands at place 0. -/
theorem tooth_missing_name [CommRing K] (P : HeadLetters K) (r : Head.Read)
    (h : P.seat.first r = none) :
    ¬ HeadClaim P := by
  intro H
  have h1 := H.1.1 r
  rw [h] at h1
  simp at h1

/-- Letters without a state with closed tables fail the statement. -/
theorem tooth_no_state [CommRing K] (P : HeadLetters K) (h : ∀ s, ¬ P.AtClose s) :
    ¬ HeadClaim P := by
  intro H
  obtain ⟨s, hs, -⟩ := H.1.2.2.1.2 () (List.mem_singleton.2 rfl)
  exact h s hs

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.AtHead.hids_are
#print axioms VerifiableInference.Reads.AtHead.clauses_are
#print axioms VerifiableInference.Reads.AtHead.value_bytes
#print axioms VerifiableInference.Reads.AtHead.ex_limbs
#print axioms VerifiableInference.Reads.AtHead.cellOf_placeIn
#print axioms VerifiableInference.Reads.AtHead.addr_hr
#print axioms VerifiableInference.Reads.AtHead.addr_hf
#print axioms VerifiableInference.Reads.AtHead.bytes_eq_digits
#print axioms VerifiableInference.Reads.AtHead.policy_at
#print axioms VerifiableInference.Reads.AtHead.means_is_read
#print axioms VerifiableInference.Reads.AtHead.headClaim_of_decls
#print axioms VerifiableInference.Reads.AtHead.tooth_missing_name
#print axioms VerifiableInference.Reads.AtHead.tooth_no_state
