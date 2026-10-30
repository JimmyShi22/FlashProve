-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ToyLink.lean: a test: THE LINK's OWN DECISION (linkDescriptionAt,
Johnson/Desc/Link/LinkDesc.lean) AT A MADE-UP TINY SHAPE, ON A VIEW THAT AN HONEST PROVER's PROGRAM
MAKES; AND ON TURNED VIEWS.
Definitions with code and evaluations; no theorem. Made-up numbers alone: no model, no weights.
THIS FILE HOLDS VIEWS THAT ARE BENT OR TURNED ON PURPOSE (Cfg.bend | wrong | junk; up, atVal, atCol,
sayKey): negative tests on this library's own decision: each is refused; none is a proof of the
release's format.

The shape tinyP. Two stored tables of 2 rows, each row a message of 8 entries (the last three: the
pads of its one answer) and a tail of 2, at 16 positions · 2 + 2 drawn columns · a folded row takes
3 rows of 4 places · THREE STAGES: (k 3, h 0) → (k 1, h 1) → (k 0, h 0): so a middle switch and a
last one · 18 rounds · the batching takes 9 rows · the base case shows 70 elements.

Who makes what.
  THE FRONT, written here: the two tables (Cfg.bend: the copy's row 0, entry 2, so much larger) ·
    stored columns by Fmt.M1.symF · vecOf t: the fold at gamma of table t's rows: message, tail, one
    free entry, the sample's pad at the last place of the last real row.
  BY THE VERIFIER's OWN FORMS, evaluated at these tables: each table's OOD answers
    (Desc.K14.recGamma at one row) · the two answers to the sample (the stored sample rows): so
    these four rows hold by make.
  THE TEST: Fmt.M1.Own.go (Fmt/M1Own.lean: an honest prover's program, written for Fmt's own
    decision of another toy), started at the group's 8 rows (3 and a zero row, twice), a zero
    carried mask row, its own new mask row, made of coin; the claim: what First.Close.bat returns,
    written out.
  col0: the first tree's column as the book cuts it: the rows that were sent alone.

The tests (#guard).
  The description's tests on the plan refuse nothing (F.planWord is none). Among their clauses, not
  tried by that: fileOk is handed as true (Limits); and the plan is linkDeclaredRounds tinyP, the blocks' own
  declared rounds in a row, so the clause that holds these rounds against the plan's, whole, holds a
  list against itself.
  Unbent and unturned: all 9 rows hold at the two tables, the batched claim holds, THE DECISION SAYS
  YES.
  bend 1, all else made honestly of the two tables: the equality row alone fails, the claim fails,
  the decision says no AT THE BASE CASE.
  One larger, each alone: the first answer to the sample · the first fold's first element · a
  coefficient of a fold's round · the first switch's answer · the first element shown at the base
  case · word 0 of an opened column of each of the three trees and of a stored column · an entry of
  the first key's OOD answers: no, each AT THE BASE CASE: no test in front of it refuses them.
  A word that is the prime: no, at the test on words. A column less: "the columns". An item less:
  "the rounds".
  One larger, each alone, a word of: the first mask's symbol in tree 0 · a carried mask row's and
  the next mask's in tree 1 · the masking message's two symbols and the last message's mask row's
  in tree 2: no, each at the base case.
  junk 1: the prover's own tables have a tail that is not zero at a row that nobody sends: all 9
  rows hold, the decision says no at the base case.
  wrong 1: another vector than the fold, truly encoded, its answer made of it: its OOD sample's
  row, its two columns' rows and the equality row fail, both sample rows hold; the claim fails; no,
  at the base case.
  THE SECOND SET OF DRAWS (the same elements; each list of positions one position twice), at the
  honest making, unturned: all 9 rows hold, one column for each list, THE DECISION SAYS YES.

Limits. linkDescriptionAt is handed ok := true: the priced tests of the description's own maker (entryOk,
tiesOk: Johnson/Desc/Link/LinkDesc.lean) are not asked; they would not pass at these numbers. One
shape, two sets of draws, one set of coins. NO DRAWN ELEMENT IS 0 OR 1: "for all draws" is not tried
there by this file. A view, not a strategy: nothing is hashed, no work is tested, no tree is built.
THE PROVER OF THE TEST's ROUNDS IS Fmt.M1.Own.go, NOT THE STRATEGY OF Johnson/Prover/Link/: nothing
here ties that folder's written messages to what Own.go sends.
"claimHolds {}" WOULD ALSO PASS IF batRun REFUSED: G1 is then the default row, with empty arrays,
and the test reads 0 = 0. That batRun returns a row is shown where the claim fails (bend 1,
wrong 1); at the honest making it is not tested apart. Johnson/Prover/Link/ToyParts.lean holds the
row that the verifier's own part hands on behind the batching against the same two tables; its test
gives [] where a part refuses and none where no such row is handed on. That this row is batRun's is
tested by no command of the two files.
A test (#guard) is run by Lean's EVALUATOR (compiled code, outside the kernel) while the file
compiles; it leaves no theorem.
Nothing on soundness, on completeness at another shape, or on what any value that is sent discloses
or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Link.LinkWritten
import Fmt.M1Own

set_option autoImplicit false

namespace Johnson.Prover.Link.Toy
open OnBytes OnBytes.Params VerifiableInference.Desc Desc.K15

/-! ## The shape -/

def tinySet : Setting :=
  { p := 18446744069414584321, degree := 3, target := 128, printed := true, rowsFactor := false,
    instances := 1, samples := 1, saltBytes := 40, nonceBytes := 8,
    positionBytes := 0, workField := { request := 0, shared := 0, once := 0 },
    workSample := { request := 0, shared := 0, once := 0 },
    workCloseness := { request := 0, shared := 0, once := 0 },
    workQuery := { request := 0, shared := 0, once := 0 },
    workSmall := { request := 0, shared := 0, once := 0 } }

def tinyCodes : Codes :=
  ⟨#[⟨4, 4, 2⟩, ⟨5, 2, 2⟩, ⟨7, 2, 2⟩], #[⟨4, 8, 2⟩, ⟨5, 16, 2⟩, ⟨7, 64, 2⟩]⟩

def tinyLink : LinkShape :=
  ⟨⟨⟨4, 8, 2⟩, 1, 1, 40⟩, 2, 2, 0, 0, 3, true, 0, true, [⟨1, 1, 1, 1⟩, ⟨2, 2, 0, 0⟩], ⟨true⟩⟩

def tinyP : P15 :=
  { set := tinySet, codes := tinyCodes, S := tinyLink
    stages :=
      [{ g := { main := { logN := 4, ell := 4, r := 2, overE := true },
                mask := { logN := 4, ell := 8, r := 2, overE := true }, k := 3, h := 0, slots := 1,
                rule := OnBytes.Params.Radius.johnson, m := 1 }, t := 2, rOod := 0 },
       { g := { main := { logN := 5, ell := 2, r := 2, overE := true },
                mask := { logN := 5, ell := 16, r := 2, overE := true }, k := 1, h := 1, slots := 1,
                rule := OnBytes.Params.Radius.johnson, m := 1 }, t := 2, rOod := 10 },
       { g := { main := { logN := 7, ell := 2, r := 2, overE := true },
                mask := { logN := 7, ell := 64, r := 2, overE := true }, k := 0, h := 0, slots := 1,
                rule := OnBytes.Params.Radius.johnson, m := 1 }, t := 2, rOod := 26 }] }

def F : OneChainFileDescription (TableKey × TableKey) := linkDescriptionAt tinyP (linkDeclaredRounds tinyP) true
def blocksT : List (Block St Unit) := (linkProtocolChain tinyP).blocksInOrder

abbrev X3 := Fmt.M1.E
abbrev Cols := List (Nat × Nat × List UInt64)
def fl : Fmt.Fld := .two
def eN (a b c : Nat) : E := ⟨a.toUInt64, b.toUInt64, c.toUInt64⟩
def x3 (a b c : Nat) : X3 := (a.toUInt64, b.toUInt64, c.toUInt64)
def sumE (l : List E) : E := l.foldl addE zeroE
def sortU (l : List Nat) : List Nat := l.foldl (fun a x => Fmt.insertIntoIncreasingList x a) []
def dr (es : List E) (ps : List Nat := []) : Fmt.Drawn := ⟨es.map (·.triple), ps, [], none⟩

/-- What is turned in a run's MAKING: bend: the copy's row 0 has its entry 2 so much larger · wrong:
the first table's folded vector has its entry 0 so much larger, and is truly encoded · junk: the
tail of the group's row 3, which nobody sends, has its entry 0 so large · alt: the second set of
draws: the same elements, each list of positions one position twice. -/
structure Cfg where
  bend : Nat := 0
  wrong : Nat := 0
  junk : Nat := 0
  alt : Bool := false

/-- THE SECOND SET OF DRAWS IS RUN AT THE HONEST MAKING ALONE: there the three other letters count
as 0. -/
def Cfg.bendH (c : Cfg) : Nat := if c.alt then 0 else c.bend
def Cfg.wrongH (c : Cfg) : Nat := if c.alt then 0 else c.wrong
def Cfg.junkH (c : Cfg) : Nat := if c.alt then 0 else c.junk

section
variable (c : Cfg)

/-! ## The draws and the coins: written. The second set: each list of positions one place twice -/

def gamma : List E := [eN 3 1 4]
def seedZ : List E := [eN 5 9 2, eN 6 5 3, eN 5 8 9, eN 7 9 3]
def seedB : E := eN 2 3 8
def qs : List Nat := if c.alt then [3, 3, 6, 6] else [3, 11, 6, 3]
def phi : List E := [eN 4 6 2, eN 6 4 3, eN 3 8 3]
def recZ (t : Nat) : List E := [eN (2 + t) 7 9, eN 5 (0 + t) 2, eN 8 8 (4 + t)]
def recB (t : Nat) : E := eN 1 (9 + t) 7
def theta0 : E := eN 9 7 1
/-- from "FOLD epsilon" on -/
def vsT : List Fmt.M1.RV :=
  [⟨[], [x3 11 2 3], []⟩, ⟨[], [x3 12 4 5], []⟩, ⟨[], [x3 13 6 7], []⟩, ⟨[], [x3 14 8 9], []⟩,
   ⟨[], (List.range 6).map (fun j => x3 (20 + j) j 1) ++ [x3 5 5 5], []⟩,
   ⟨[], [x3 15 1 1], if c.alt then [9, 9] else [9, 2]⟩, ⟨[], [x3 16 2 2], []⟩,
   ⟨[], [x3 17 3 3], []⟩,
   ⟨[], (List.range 7).map (fun j => x3 (40 + j) 1 j) ++ [x3 6 6 6], []⟩,
   ⟨[], [x3 18 4 4], if c.alt then [7, 7] else [30, 7]⟩, ⟨[], [x3 19 5 5], []⟩,
   ⟨[], [], if c.alt then [41, 41] else [100, 41]⟩]
/-- The toy's "coins": a written formula of a tag and an index. -/
def coin (tag i : Nat) : X3 :=
  ((1000 + 17 * tag + i).toUInt64, (3 * tag + 5 * i + 1).toUInt64, (tag + i + 2).toUInt64)

def stagesT : List Fmt.M1.Stage :=
  [⟨⟨4, 4, 2⟩, ⟨4, 8, 2⟩, 3, 0, 2⟩, ⟨⟨5, 2, 2⟩, ⟨5, 16, 2⟩, 1, 1, 2⟩,
   ⟨⟨7, 2, 2⟩, ⟨7, 64, 2⟩, 0, 0, 2⟩]

/-! ## The tables -/

def Tc : Fmt.M1.Code := ⟨4, 8, 2⟩
def msgOfT (t b : Nat) : List UInt64 :=
  (List.range 8).map fun j =>
    if j < 5 then (10 + 3 * b + j + (if t == 1 && b == 0 && j == 2 then c.bendH else 0)).toUInt64
    else (100 * (t + 1) + 7 * b + j).toUInt64
def tlOfT (t b : Nat) : List UInt64 :=
  (List.range 2).map fun j => (200 * (t + 1) + 5 * b + j).toUInt64
def colT (t x : Nat) : List UInt64 :=
  (List.range 2).map fun b => Fmt.M1.symF Tc x (msgOfT c t b) (tlOfT t b)

/-! ## The folds -/

def lay : VectorLay := vectorLay tinyCodes (tinyLink.side false 1).u true
def wts : Array E := eqTable gamma
def foldF (l : Nat → UInt64) : E :=
  sumE ((List.range 2).map fun b => mulE (wts.getD b zeroE) (ofF (l b)))
/-- the vector of table t: message, tail, a free entry, the pad -/
def vecOf (t : Nat) : Array E :=
  ((List.range 8).map (fun j =>
      addE (foldF fun b => (msgOfT c t b).getD j 0)
        (if t == 0 && j == 0 then eN c.wrongH 0 0 else zeroE)) ++
    (List.range 2).map (fun j => foldF fun b => (tlOfT t b).getD j 0) ++
    [eN (70 + t) 1 1, eN (80 + t) 2 2]).toArray
def tabOf (t : Nat) (idx : Nat) : E := (vecOf c t).getD (lay.entryAt idx) zeroE

def evalMain (r : Row) (o : Nat) (tab : Nat → E) (n : Nat) : E :=
  sumE ((List.range n).map fun i => mulE (r.coefficient o .main i) (tab i))

/-! ## The keys -/

/-- Table t's OOD answers, one for each of its two rows; zeroE where Desc.K14.recGamma gives none.
-/
def recOfT (t : Nat) : Array E :=
  ((List.range 2).map fun b =>
    match Desc.K14.recGamma tinyLink.table ⟨recZ t, recB t⟩ 0 #[oneE, oneE] #[zeroE, zeroE]
      ⟨0, lay⟩ with
    | some row => evalMain row 0 (fun idx =>
        if lay.entryAt idx < 8 then ofF ((msgOfT c t b).getD (lay.entryAt idx) 0) else zeroE) 16
    | none => zeroE).toArray
def keyOfT (t : Nat) : TableKey := ⟨t, recOfT c t, [⟨recZ t, recB t⟩]⟩

/-! ## The front -/

def frontRounds (a0 a1 : E) : List Fmt.RoundView :=
  [⟨[], dr gamma⟩, ⟨[], dr (seedZ ++ [seedB])⟩,
   ⟨[.answer a0.triple, .answer a1.triple], dr []⟩, ⟨[], dr [] (qs c)⟩, ⟨[], dr phi⟩]
def storedCols : Cols :=
  (sortU ((qs c).take 2)).map (fun x => (Fmt.storedKey 0, x, colT c 0 x)) ++
    (sortU ((qs c).drop 2)).map (fun x => (Fmt.storedKey 1, x, colT c 1 x))
def frontRun (a0 a1 : E) : Except String (St × List Fmt.RoundView × Cols) :=
  foldBlocks 0 (blocksT.take 6) (first tinyCodes (keyOfT c 0, keyOfT c 1))
    (frontRounds c a0 a1) (storedCols c)
/-- The answer of table t: its first stored sample row at the table; zeroE where frontRun refuses or
no sample row stands. -/
def ansOf (t : Nat) : E :=
  match frontRun c zeroE zeroE with
  | .ok (s, _, _) =>
    match (s.st.oracles.getD t default).sampleRows[0]? with
    | some row => evalMain row t (tabOf c t) 16
    | none => zeroE
  | .error _ => zeroE
/-- which of the open rows and stored sample rows hold at the two tables; [] where frontRun refuses
-/
def rowsHold : List Bool :=
  match frontRun c (ansOf c 0) (ansOf c 1) with
  | .ok (s, _, _) =>
    ((s.st.groups.toList.flatMap fun (g : OnBytes.Group) => g.rows.toList) ++
      (s.st.oracles.toList.flatMap fun (o : OnBytes.Oracle) => o.sampleRows.toList)).map fun r =>
        decide ((addE (evalMain r 0 (tabOf c 0) 16) (evalMain r 1 (tabOf c 1) 16)).triple =
          r.target.triple)
  | .error _ => []

/-! ## The test -/

def rowOfMem (t ρ : Nat) : List X3 :=
  (List.range 4).map fun pl => ((vecOf c t).getD (ρ * 4 + pl) zeroE).triple
/-- The tail of row ρ of table t: coin at the tag 300 + 10 * t + ρ, at the indices 0 and 1. The tag
300 (t = 0, ρ = 0) is read again by Fmt.M1.Own.nextSt at i = 3, b = 0 (its Rh: the tag 100 * i + b).
-/
def tailOfMem (t ρ : Nat) : List X3 := (List.range 2).map fun j => coin (300 + 10 * t + ρ) j
def zs (n : Nat) : List X3 := List.replicate n Fmt.Fld.zeroE
def p1 : Fmt.M1.Own.PSt :=
  let rd := Fmt.M1.Own.riders fl coin 1 (stagesT.getD 0 default) false
  { M := (List.range 3).map (rowOfMem c 0) ++ [zs 4] ++ (List.range 3).map (rowOfMem c 1) ++
      [zs 4]
    Rh := (List.range 3).map (tailOfMem 0) ++ [[x3 c.junkH 0 0, Fmt.Fld.zeroE]] ++
      (List.range 3).map (tailOfMem 1) ++ [zs 2]
    W := [zs 8], Sg := [zs 2], P := rd.1, Pi := rd.2 }
def batRun : Except String (GroupRow × GroupLayout × Statement) :=
  match frontRun c (ansOf c 0) (ansOf c 1) with
  | .ok (s, _, _) =>
    First.Close.bat s.st s.loc.g ((linkDeclaredRounds tinyP).getD 5 default).entry ⟨[], dr [theta0]⟩
  | .error e => .error e
/-- The batched claim, written out; default where batRun refuses. -/
def G1 : Fmt.M1.GRow :=
  match batRun c with
  | .ok (row, _, _) => ⟨(row.c.writeOut 5).map (·.triple), row.d.map (·.triple), row.target.triple⟩
  | .error _ => default
def claimHolds : Bool :=
  decide (Fmt.M1.Own.lhs fl (G1 c) (Fmt.M1.Own.tabOf (p1 c).M 4)
    (Fmt.M1.Own.tabOf (p1 c).W 8) = (G1 c).t)
def out : Fmt.M1.Own.Out := Fmt.M1.Own.go Fmt.M1.blocks fl coin (vsT c) stagesT 1 0 (p1 c) (G1 c)
def col0 (x : Nat) : List UInt64 :=
  [0, 1, 2, 4, 5, 6, 9].flatMap fun i =>
    ((((out c).cols.getD 0 fun _ => []) x).drop (3 * i)).take 3
def testRounds : List Fmt.RoundView :=
  (List.range 12).map fun j =>
    let l := (out c).sent.getD j []
    ⟨if ((linkDeclaredRounds tinyP).getD (6 + j) default).entry.name == "CS" then l.map .answer else l.map .e,
      ⟨((vsT c).getD j default).els, ((vsT c).getD j default).poss, [], none⟩⟩
def ownCols : Cols :=
  (sortU ((vsT c).getD 5 default).poss).map (fun x => (0, x, col0 c x)) ++
    (sortU ((vsT c).getD 9 default).poss).map
      (fun x => (1, x, ((out c).cols.getD 1 fun _ => []) x)) ++
    (sortU ((vsT c).getD 11 default).poss).map fun x => (2, x, ((out c).cols.getD 2 fun _ => []) x)
def viewT : Fmt.View :=
  ⟨frontRounds c (ansOf c 0) (ansOf c 1) ++ [⟨[], dr [theta0]⟩] ++ testRounds c,
    storedCols c ++ ownCols c⟩

end

/-! ## Turning a view -/

def up (g : Fmt.ItemValue) : Fmt.ItemValue :=
  match g with
  | .e x => .e (x.1 + 1, x.2)
  | .answer x => .answer (x.1 + 1, x.2)
  | g => g
/-- item j of round i, by f -/
def atVal (i j : Nat) (f : Fmt.ItemValue → Fmt.ItemValue) (v : Fmt.View) : Fmt.View :=
  { v with rounds := v.rounds.modify i fun r => { r with vals := r.vals.modify j f } }
/-- word w of column number i made one larger -/
def atCol (i : Nat) (w : Nat := 0) (v : Fmt.View) : Fmt.View :=
  { v with opened := v.opened.modify i fun x => (x.1, x.2.1, x.2.2.modify w (· + 1)) }
/-- The decision's words. At the second set of draws the view is not turned. -/
def say (c : Cfg) (turn : Fmt.View → Fmt.View) : String :=
  F.say (keyOfT c 0, keyOfT c 1) (if c.alt then viewT c else turn (viewT c))
def sayKey : String :=
  F.say
    ({ keyOfT {} 0 with record := (keyOfT {} 0).record.modify 0 fun e => addE e oneE }, keyOfT {} 1)
    (viewT {})

/-! ## The tests -/

def atBase : String :=
  "no: the chain: refused at the proximity test (chain 1, piece 6): the base case: the linear " ++
    "claim, or a symbol at a position"
def inTest (w : String) : String :=
  "no: the chain: refused at the proximity test (chain 1, piece 6): " ++ w

#guard F.planWord == none
#guard rowsHold {} == List.replicate 9 true
#guard claimHolds {}
#guard say {} id == "yes"
#guard rowsHold { bend := 1 } == [true, true, true, true, true, true, false, true, true]
#guard !claimHolds { bend := 1 }
#guard say { bend := 1 } id == atBase
#guard say {} (atVal 2 0 up) == atBase
#guard say {} (atVal 6 0 up) == atBase
#guard say {} (atVal 8 1 up) == atBase
#guard say {} (atVal 11 0 up) == atBase
#guard say {} (atVal 17 0 up) == atBase
#guard say {} (atCol 4) == atBase
#guard say {} (atCol 6) == atBase
#guard say {} (atCol 8) == atBase
#guard say {} (atCol 0) == atBase
#guard sayKey == atBase
#guard say {} (atVal 17 3 fun _ => .e (18446744069414584321, 0, 0)) ==
  "no: a word of the view is not below the prime"
#guard say {} (fun v => { v with opened := v.opened.dropLast }) == inTest "the columns"
#guard say {} (fun v =>
  { v with rounds := v.rounds.modify 8 fun r => { r with vals := r.vals.take 1 } }) ==
    inTest "the rounds"

#guard say {} (atCol 4 18) == atBase
#guard say {} (atCol 6 6) == atBase
#guard say {} (atCol 6 12) == atBase
#guard say {} (atCol 8 3) == atBase
#guard say {} (atCol 8 6) == atBase
#guard say {} (atCol 8 9) == atBase
#guard rowsHold { junk := 1 } == List.replicate 9 true
#guard say { junk := 1 } id == atBase
#guard rowsHold { wrong := 1 } == [false, true, false, false, true, true, false, true, true]
#guard !claimHolds { wrong := 1 }
#guard say { wrong := 1 } id == atBase
#guard rowsHold { alt := true } == List.replicate 9 true
#guard (viewT { alt := true }).opened.map (fun x => (x.1, x.2.1)) ==
  [(65536, 3), (65537, 6), (0, 9), (1, 7), (2, 41)]
#guard say { alt := true } id == "yes"

end Johnson.Prover.Link.Toy
