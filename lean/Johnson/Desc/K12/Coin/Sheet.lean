-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Sheet.lean: THE LAW OF THE PROXIMITY TEST (the kind K12) IN THE PLAIN FORM
(`Reduction.Leads`, Johnson/Desc/Plain/Leads.lean): A SHEET OF STATEMENTS. Definitions, and
propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE: the proofs are in Law.lean,
beside; `K12LawF2` is concluded by no theorem; `leads_atFinish` (SeatF2.lean) seats any law of
pieceT.

What is said. The block `proximityTestKind guardedProximityTestParts π` at its own record T12, with the written rounds of its
stretch (the round "BAT", then the chain's rounds), is a piece (Johnson/Desc/Sound/ChainRule.lean).
`K12LawT`: under the named premises the prover has lost, at the piece's own errors, towards: where
the piece says yes, THERE IS ONE WITNESS WITHIN THE FIRST RADIUS OF THE WORD OF THE GROUP UNDER
TEST, READ OFF THE ORACLES IN FRONT OF THE BLOCK, AT WHICH EVERY ROW THAT IS PENDING ON THE GROUP
HOLDS. `K12LawF2`: the same at the seat `atFinish π` on the first chain's own state.

WHICH TREE IS WHICH GOES BY NUMBER, NEVER BY KEY. Two letters: num: from a declared source of an
opening to the tree's number over the file (at a description's frames: `numAt`,
Johnson/Desc/BlockSlot.lean); no: from a place of the record's book to the tree's number over the
file.

Main names.
  `colIn`, `woIn`, `W0`: a column of a tree off the statement's oracles, by the tree's number over
    the file; that tree's columns as a written oracle; the book's trees' oracles, by the book's
    place, along no.
  `rowG`, `NearAll`: a pending row carried to the group's tables; the conclusion's content.
  `QK`: the conclusion at a statement.
  `Like`: the stretch's data are the place's declared rounds as written.
  `FirstOpens`: at the statement: the trees that the first switch's declared openings name are, in
    turn, those at the places D.ts of the book (the members' trees' and the mask's), each sent in
    front of the stretch.
  `BatAt`: THE BATCHING's CONVERSE AT ONE STATEMENT, UNPAID: at all but e₀ values of the round's
    challenge: if the row batched AT THE STRETCH's OWN ENTRY has a witness within the radius, there
    is one witness for all the rows.
  `OnK`: the promise in front: THE FIRST FOLD's MASK HAS COME (the record names it), `FirstOpens`,
    `BatAt`.
  `errList`, `Bears`: the piece's errors behind "BAT" bear the chain's.
  `AtPlace`: what is public of a place and its stretch, and the facts on codes.
Every "there is", walked. In `NearAll`: row₀ and hok stand under "there is" only because `yOf` takes
a proof that names a row; the word does not hang on them (`yOf_indep`, SheetChecks.lean, beside).
w: the witness. R: fixed by its equation. In `QK`: the stage, the group, the layout and the plain
data are functions of the record in front: each stands with the equation that fixes it.
THE SILLY VERIFIERS (SheetChecks.lean): one that says yes to all has not the law (`yesAll_fails`);
one that says no to all has it, as it has every statement on soundness alone.
Limits. No soundness is claimed. NO MEMBER OF `AtPlace` IS KNOWN: that `like`, `batNone`, `own0`,
`wants`, `numOwn`, `trees` hold at the release's plan, and `FirstOpens` at the records that run, is
to be evaluated or proved. AT A PLACE WHOSE FIRST FOLD SENDS ITS OWN MASK THE PROMISE AND `own0`
FAIL AND THE LAW SAYS NOTHING: for such a place see OwnArm.lean, beside. The facts on
codes at the radii (`CodesAt`), the bound on the errors and, in the promise, `BatAt` are premises;
`dealOk` is a test on the plan, a run's. A witness, not the witness: beyond half the distance a word
may be near several code words. Nothing on what the test leaves in the record. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.SeatAcc
import Johnson.Desc.K12.Law.K12Lemma
import Johnson.Desc.K12.Law.DealOk
import Johnson.Desc.Plain.PieceYes
import Johnson.Desc.BlockSlot
import OnBytes.Slice.ManyShows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK (WO yOf recAt)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk Letters)
open H2K.First (gpOf gpL Plain logAt widthAt)

/-! ## 1 The oracles in front of the block, by the book's place -/

/-- The column at leaf x of the tree with the number j through the file, off the oracles of a
statement; nothing where the frame lists no such tree or leaf. -/
def colIn (F : Frame) (y : F.E.Str) (j x : ℕ) : List UInt64 := ((posL F.all j x).map y.2).getD []

/-- A written round that sends one tree of depth a and width w, and nothing else. -/
def rdOf (a w : ℕ) : PQ.RD := ⟨{ name := "" }, .nothing, [], some { a := a, W := w, tree := 0 }, []⟩

/-- The columns of the tree number j, as a written oracle of depth a and width w: a word that a
column lacks is read as 0. -/
def woIn (F : Frame) (y : F.E.Str) (j a w : ℕ) : WO :=
  ⟨rdOf a w, fun x k => (colIn F y j x.val).getD k.val 0⟩

/-- The written rounds and oracles of a book's trees, by the book's place, along no. -/
def W0 (F : Frame) (no : ℕ → ℕ) (book : TreeBook) (y : F.E.Str) (z : ℕ) : WO :=
  woIn F y (no z) (logAt book z) (widthAt book z)

/-! ## 2 The conclusion -/

/-- A row on members' tables, carried to the group's tables: the batching's own step
(`Own.rowInto`, Johnson/Desc/Own/Batch.lean) at the factor 1 and the empty row. -/
def rowG (S : Statement) (Ly : GroupLayout) (g : ℕ) (r : OnBytes.Row) : Option GroupRow :=
  Own.rowInto S Ly r oneE { group := g }

/-- **One witness within the radius e of the group's word, at which every one of the rows, carried
to the group's tables by G, holds.** -/
def NearAll (π : P12) (a : Fmt.M1.Stage) (D : Plain) (rd : ℕ → ℕ) (V : ℕ → WO) (e : ℕ)
    (G : OnBytes.Row → Option GroupRow) (rows : List OnBytes.Row) : Prop :=
  ∃ (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true) (w : (sgOf a).cIn.N.Wit),
    Cb.offCnt (yOf π a row₀ D hok rd V) ((sgOf a).cIn.N.enc w.1 w.2) ≤ e ∧
    ∀ r ∈ rows, ∃ R, G r = some R ∧
      (sgOf a).RIn e (stmG (sgOf a) R, yOf π a row₀ D hok rd V) w

/-- What a record in front of the block fixes: the first stage, the group under test, its layout,
the plain data behind the batching's beginning. -/
def Fixes (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) : Prop :=
  π.nums.stages = a :: rest ∧ t.st.groups[t.g]? = some G0 ∧ t.st.layout t.g = some Ly ∧
    ∀ row, gpOf π { t with st := begun t.st t.g G0, pass := .claim row Ly } a Ly = some D

/-- The conclusion at a statement in front of the block. -/
def QK (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (x : T12 × F.E.Str) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π x.1 a rest G0 Ly D ∧
    NearAll π a D rd (W0 F no D.book x.2) (rad (sgOf a)) (rowG (begun x.1.st x.1.g G0) Ly x.1.g)
      (runRows x.1.st G0).toList

/-! ## 3 The premises -/

/-- A round's data are a declared round as written: no stored table is opened. What it opens is
asked by `AtPlace.wants`. -/
def Like (d : RDT) (w : WR) : Prop :=
  d.entry = w.entry ∧ d.kind = w.kind ∧ d.items = w.items ∧ d.trees = w.tree.toList ∧ d.stored = []

/-- At the statement: the trees that the first switch's openings name are those at the places D.ts
of the book, in turn; each was sent in front of the stretch. -/
def FirstOpens (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    D.opens.map (fun o => num o.2) = D.ts.map no ∧ ∀ z ∈ D.ts, no z < base

/-- The round "BAT" as a view shows it. -/
def r0Of (dB : RDT) (m : (roundT (ckP .two) dB).up.Msg) (c : (roundT (ckP .two) dB).up.Chal) :
    Fmt.RoundView :=
  ((rvT (ckP .two) [dB] (m, c, ())).head?).getD ⟨[], ⟨[], [], [], none⟩⟩

/-- **The batching's converse, at one statement.** Whatever message "BAT"'s round holds: at all but
e₀ values of its challenge: if the batching, AT THE STRETCH's OWN ENTRY, returns a row, and that row
has a witness within the radius of the group's word, then `NearAll`: one witness for all rows. -/
def BatAt (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (e₀ : ℕ)
    (x : T12 × F.E.Str) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true), Fixes π x.1 a rest G0 Ly D →
    ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
        First.Close.bat x.1.st x.1.g dB.entry (noDigest (r0Of dB m c)) =
          .ok (row, Ly, begun x.1.st x.1.g G0) ∧
        (sgOf a).RIn (rad (sgOf a))
          (stmG (sgOf a) row, yOf π a row₀ D hok rd (W0 F no D.book x.2)) w ∧
        ¬ NearAll π a D rd (W0 F no D.book x.2) (rad (sgOf a))
          (rowG (begun x.1.st x.1.g G0) Ly x.1.g) (runRows x.1.st G0).toList) ≤ e₀

/-- **The promise in front of the block.** -/
def OnK (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (base : ℕ) (dB : RDT) (e₀ : ℕ) (x : T12 × F.E.Str) : Prop :=
  x.1.mask.isSome = true ∧ FirstOpens π num no base x.1 ∧ BatAt F π no rad rd dB e₀ x

/-- A list of errors as a list of numbers. -/
def errList : (s : Shape) → Err s → List ℕ
  | [], _ => []
  | _ :: s, (e, ε) => e :: errList s ε

/-- The second list of errors bears the first, round by round. -/
def Bears {s t : Shape} (ε : Err s) (ε' : Err t) : Prop :=
  List.Forall₂ (· ≤ ·) (errList s ε) (errList t ε')

/-- What is public of a place and its stretch, and the facts on codes. -/
structure AtPlace (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt)) :
    Prop where
  early : π.early = true
  answers : π.answers = 1
  planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true
  spend : spendOk π = true
  deal : H2K.First.dealOk π = true
  codes : CodesAt L mC mS mW rad π.nums.stages
  like : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)
  /-- "BAT"'s round sends no tree -/
  batNone : dB.trees = []
  /-- the test sends no tree but its switches' -/
  own0 : H2K.First.ownN π = 0
  /-- at all draws the stretch's wants are the declared rounds' wants, each tree by its number over
  the file -/
  wants : ∀ Rs,
    wantsOf F.a (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth (dB :: dt) Rs =
      wantsDecl num (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds Rs
  /-- the chain's own tree number free + n is the stretch's n-th -/
  numOwn : ∀ n, num (.own (π.nums.free + n)) = base + n
  trees : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
    writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c → c.Trees
  bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
    writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
    Bears c.errL εt

/-! ## 4 The statements -/

/-- The piece: the block at its own record, at its stretch. -/
def pieceT (F : Frame) (W : Type) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) : Piece (ckP .two) F T12 Unit W :=
  ⟨proximityTestKind guardedProximityTestParts π, base, dB :: dt, [], fun _ _ w => w, (e₀, εt)⟩

/-- **THE LAW OF THE KIND K12, AT ITS OWN RECORD.** -/
def K12LawT : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)),
    AtPlace F π num L mC mS mW rad base dB dt εt →
    (pieceT F W π base dB dt e₀ εt).ior.red.Leads (OnK F π num no rad rd base dB e₀)
      (fun x _ => QK F π no rad rd x) (pieceT F W π base dB dt e₀ εt).err

/-- The piece at the first chain's finish. -/
def pieceF2 (F : Frame) (W : Type) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) : Piece (ckP .two) F First.S Unit W :=
  ⟨atFinish π, base, dB :: dt, [], fun _ _ w => w, (e₀, εt)⟩

/-- **THE LAW AT THE FIRST CHAIN's FINISH.** -/
def K12LawF2 : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)),
    AtPlace F π num L mC mS mW rad base dB dt εt →
    (pieceF2 F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → OnK F π num no rad rd base dB e₀ (recAt x.1 fo, x.2))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        QK F π no rad rd (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (pieceF2 F W π base dB dt e₀ εt).err

end VerifiableInference.Desc.K12.Coin
