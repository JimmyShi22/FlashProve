-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Plan.lean: what the prover sends and the verifier draws in each round of the first toy (a
product test), computed from the toy's sizes, as the record that the reader of a proof file takes
(`Fmt.Spec`).

Generic in the sizes. Definitions that compute, with tests that run when the file compiles. No
Mathlib.
(In this head "the programs" are the C++ implementation that comes with this Lean code, and "the
format page" is docs/format/FORMAT.md, which comes with the programs.)

The words. The first toy is a small test protocol of the programs ("the prover knows a, b, c with
a_i b_i = c_i"). A chain is one non-interactive transcript as it stands in a file (this toy's proof
is one chain): here its random bytes, then the prover's messages, nonces and openings in the order
of the protocol. A stage (`Stage`, Fmt/M1Types.lean) is a stage of the toy's proximity test: main
code C, mask code Z, 2^k main rows, 2^h mask rows, t drawn positions.

Written from the programs' description of that toy (its sections 0 to 3: the five conditions, the
  statement, the plan's table of 30 rounds, the trees, the file's order; its part on the first
  sending for the number of a sample's coordinates)
and from the format page: an edition that is not the one that ships (R4.3, R5.1, R6.2, R6.9, R8.7,
and its section on the first types
  and the first toy run, R12.1 to R12.10), which rules the names, the kinds, the rounds, the cut of
  each message into items and the widths as they stand here.
The sizes are the record `Par` of Fmt/M1Types.lean. The number of a sample's coordinates is
`Stage.na` of Fmt/M1Dec.lean. The number of rounds is held against `nRounds` of the same file.
Below, "the text" is the programs' description of the toy.
Their table numbers the rounds from 0; the format (R5.1) and the chain from 1: the table's round i
is the chain's round i + 1, and the entry at place i of the lists here.

The rounds, for stages s_1, .., s_n (n ≥ 2), the rows a, b, c of 2^K entries. In brackets: what the
prover sends; what the verifier draws; in CS and BASE also the proof of work, in CS the rows
batched.
  the first sending: SEND seed (the root of tree 0; a seed: the coordinates of s_1's sample, then a
    factor that is not 0); SEND answer (one answer; nothing is drawn)
  a b = c: ZERO (nothing is sent; K elements); PSC epsilon (a hiding sum; one element); K times PSC
    round (two coefficients; one element); PSC Y (two coefficients; one element that is not 0); PSC
    values (two values; nothing is drawn)
  BAT: nothing is sent; one element; four rows are batched
  for each stage s_i but the last: FOLD epsilon (a hiding sum; one element); s_i.k times FOLD round
    (two coefficients; one element); SEND seed (the root of tree i; the seed of s_(i+1)'s sample);
    CS (one answer; proof of work; s_i.t positions below 2^(s_i.C.a), then one element; 3 s_i.t + 2
    rows are batched); after its nonce the opening of tree i − 1
  the last stage: BASE lambda (one element is sent; one element); BASE (the last stage's messages
    and tails in the clear; proof of work; s_n.t positions); after its nonce the opening of tree
    n − 1

Main names:
  `wFirst`, `wMid`, `wLast`: a column's width in elements of the base field: the first tree: 3
    symbols of the base field, then 2^h mask symbols and 2^h fresh mask symbols of the extension
    field; a later tree: 2^k main, 2^h mask, 2^h fresh mask symbols of the extension field; the
    last: twice 2^k main and twice 2^h mask symbols (the text has k = h = 0 there).
  `headRounds`, `laterRounds`, `roundsOf P`, `planOf P nonceB`, `specOf P cfg others nonceB`: these
    build the description. It has label 1; the statement's bytes are empty; 32 random bytes stand at
    the file's head; there are no listed positions (`posB` is 0); there is one answer to a sample
    (`samples` is 1).
  `Par.planOK`: at least two stages (with one stage the first tree would be the last: the text has
    no such run).
  `noticeBytes`, `stagesBytes`, `choicesBytes`: three of the format's first types (R12.3: seven
    words; R12.4: the number of stages and four words a stage: base code, mask code, k, h; R12.5:
    one word): with the page's known answers.
  `toyPar`, `tinyPar`:
    the toy's sizes, with the six codes of Fmt/M1Codes.lean (`Full`: by report: the answers to
      questions about the programs; and read off the programs' own bytes: Fmt/M1Theirs.lean);
    tiny sizes of this library's own (rows of 2^4 entries, three positions, 4 bits of work): no
    run of the
      programs stands behind it (files of a second program, this library's own, in Python, at
      these
      sizes: Fmt/M1Files.lean, read in Fmt/M1PlanKnown.lean).

Tests. At the toy's sizes the thirty rounds are the table in a wording of the text, line
for line (name, kind, prover's bytes, roots, answers, elements drawn, positions, range, work, rows
batched: the table is put in by a program from that wording); the four drawn elements that must not
be 0 stand in the table's rounds 0, 16, 22, 26; the trees' depths 15, 14, 14, widths 9, 18, 12, and
the rounds after which they are opened, 23, 27, 29; 3,220 elements in the clear; `Spec.ok` at the
toy's and at the tiny sizes. That wording has not been held against the description as it ships.

What is taken where the text is silent, and is confirmed (the answers; R12.8):
  a round's name in the plan is the table's column "name" alone;
  a nonce has 8 bytes in a file;
  the word "rows" and the word k are 0 where the table has a blank;
  the plan's sixth word (answers to a sample) is 1.

Notation:
  ZERO: the zero-check;
  PSC: the sum-check;
  BAT: the batching block;
  FOLD: a fold;
  CS: the code switch;
  BASE: the last block
  (the heads of Fmt/M1Dec.lean and Fmt/M1Ref.lean);
  a round's kind: what the verifier's message of the round consists of (`Kind`, Fmt/Plan.lean, which
    tells each kind);
  `saved`: whether a sum-check's message leaves out the coefficient that the check fixes (0 or 1)
    (`Plan`, Fmt/Plan.lean).

Limits: this file has no theorem. The parameters' other items (codes, the oracle message's notice,
the stages and the choices of the proximity test) and the configuration's digest are arguments here:
Fmt/M1ParOf.lean spells the items from the sizes (`itemsOf`), and Fmt/M1Theirs.lean holds the whole
of the parameters' bytes against the programs' own. This file does not say what the decision is:
Fmt/M1Dec.lean. This file's sources include no proof file of the programs.
The programs' own files of the first toy are held as bytes, or listed, in Fmt/M1ProgPTFiles.lean,
Fmt/M1ProgPRFiles.lean and Fmt/M1ProgPFFiles.lean;
the honest proof of each set is read by the strict reader, with the values taken from the programs'
lists of the plan, the digests and the chain read from the file or recomputed, in
Fmt/M1EnginePT.lean, Fmt/M1EnginePR.lean and Fmt/M1EnginePF.lean; and all are judged in
Fmt/M1FullProg.lean, Run/PlanQSFProg.lean and files Run/M1Engine*.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Dec

namespace Fmt
namespace M1

def wFirst (s : Stage) : Nat := 3 + 3 * 2 ^ s.h + 3 * 2 ^ s.h
def wMid (s : Stage) : Nat := 3 * 2 ^ s.k + 3 * 2 ^ s.h + 3 * 2 ^ s.h
def wLast (s : Stage) : Nat := 2 * (3 * 2 ^ s.k) + 2 * (3 * 2 ^ s.h)

/-- the elements that the last message shows in the clear -/
def clearN (s : Stage) : Nat := s.C.l + s.Z.l + s.C.r + s.Z.r

/-! ## The kinds of rounds -/

def rSeed (s : Stage) : Round :=
  { entry := { name := "SEND seed", msg := 32, roots := 1, drawE := s.na + 1, drawNZ := 1 },
    kind := .seeds, items := [.root] }
def rAnswer : Round :=
  { entry := { name := "SEND answer", msg := 24, answers := 1 },
    kind := .nothing, items := [.answer] }
def rZero (K : Nat) : Round := { entry := { name := "ZERO", drawE := K }, kind := .elems }
def rEps (name : String) : Round :=
  { entry := { name := name, msg := 24, drawE := 1 }, kind := .join, items := [.e] }
def rTwo (name : String) : Round :=
  { entry := { name := name, msg := 48, drawE := 1 }, kind := .elems, items := [.e, .e] }
def rY : Round :=
  { entry := { name := "PSC Y", msg := 48, drawE := 1, drawNZ := 1 },
    kind := .elems, items := [.e, .e] }
def rValues : Round :=
  { entry := { name := "PSC values", msg := 48 }, kind := .nothing, items := [.e, .e] }
def rBat : Round := { entry := { name := "BAT", drawE := 1, rows := 4 }, kind := .elems }
def rCs (work : Nat) (s : Stage) (tree W : Nat) : Round :=
  { entry :=
    { name := "CS", work := work, msg := 24, answers := 1, drawE := 1, poss := s.t,
      logN := s.C.a, rows := 3 * s.t + 2 },
    kind := .positions, items := [.answer],
    opens := [({ a := s.C.a, W := W, tree := tree }, .own tree)] }
def rLambda : Round :=
  { entry := { name := "BASE lambda", msg := 24, drawE := 1 }, kind := .elems, items := [.e] }
def rBase (work : Nat) (s : Stage) (tree : Nat) : Round :=
  { entry := { name := "BASE", work := work, msg := 24 * clearN s, poss := s.t, logN := s.C.a },
    kind := .positions, items := List.replicate (clearN s) .e,
    opens := [({ a := s.C.a, W := wLast s, tree := tree }, .own tree)] }

/-- the first sending, a b = c, the batching -/
def headRounds (K : Nat) (s : Stage) : List Round :=
  [rSeed s, rAnswer, rZero K, rEps "PSC epsilon"] ++
    List.replicate K (rTwo "PSC round") ++ [rY, rValues, rBat]

/-- from the stage "old", whose tree has the number "tree" and columns of W elements, to the end -/
def laterRounds (work : Nat) : Nat → Nat → Stage → List Stage → List Round
  | tree, _, old, [] => [rLambda, rBase work old tree]
  | tree, W, old, new :: rest =>
    [rEps "FOLD epsilon"] ++ List.replicate old.k (rTwo "FOLD round") ++
      [rSeed new, rCs work old tree W] ++ laterRounds work (tree + 1) (wMid new) new rest

/-- The rounds. -/
def roundsOf (P : Par) : List Round :=
  match P.stages with
  | [] => []
  | s :: rest => headRounds P.K s ++ laterRounds P.work 0 (wFirst s) s rest

def Par.planOK (P : Par) : Bool := decide (2 ≤ P.stages.length)

/-- The plan. -/
def planOf (P : Par) (nonceB : Nat := 8) : Plan where
  field := P.fld
  salt := P.salt
  nonce := nonceB
  posB := 0
  samples := 1
  saved := 1
  entries := (roundsOf P).map (·.entry)

/-- The description (`Spec`, Fmt/Rules8.lean). -/
def specOf (P : Par) (cfg : ByteArray) (others : List (String × ByteArray)) (nonceB : Nat := 8) :
    Spec where
  label := 1
  plan := planOf P nonceB
  params := paramsBytes (planOf P nonceB) cfg others
  statement := ByteArray.empty
  rand := .inFile
  cfg := cfg
  rounds := roundsOf P

/-- the bytes of a file but for its openings: the random bytes, the messages, the nonces -/
def fixedLen (P : Par) (nonceB : Nat := 8) : Nat :=
  32 + ((roundsOf P).map fun r => r.entry.msg + (if r.entry.work = 0 then 0 else nonceB)).sum

/-! ## Three of the format's first types -/

/-- an oracle message's notice: seven words -/
def noticeBytes (code maskCode mainRows degree maskRows answers leafClass : Nat) : ByteArray :=
  cat ([code, maskCode, mainRows, degree, maskRows, answers, leafClass].map u64n)

/-- "no code" -/
def noCode : Nat := 2 ^ 32 - 1

/-- stages: their number, then four words each -/
def stagesBytes (l : List (Nat × Nat × Nat × Nat)) : ByteArray :=
  u64n l.length ++ cat (l.map fun s => cat ([s.1, s.2.1, s.2.2.1, s.2.2.2].map u64n))

/-- The choices of a proximity test are one word: whether the later stages' masks go out with the
switch.  (The answers to a sample have their one home in the plan's eight words) -/
def choicesBytes (masksRide : Bool) : ByteArray := bool masksRide

-- the page's known answers (not at the edition that ships, made-up values of the first types)
#guard hex (choicesBytes true) = "0100000000000000"
#guard hex (noticeBytes 0 0 3 1 1 1 0) = "0000000000000000000000000000000003000000000000000100000000000000010000000000000001000000000000000000000000000000"
#guard hex (noticeBytes 0 noCode 3 1 0 1 0) = "0000000000000000ffffffff0000000003000000000000000100000000000000000000000000000001000000000000000000000000000000"
#guard hex (stagesBytes [(0, 0, 2, 0), (1, 0, 0, 0)]) = "020000000000000000000000000000000000000000000000020000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000"

/-! ## The toy's sizes, and tiny sizes of this library's own -/

/-- The toy's sizes -/
def toyPar : Par where
  fld := .two
  K := 12
  stages := [⟨Full.main1, Full.mask1, 2, 0, 73⟩,
    ⟨Full.main2, Full.mask2, 1, 1, 74⟩, ⟨Full.main3, Full.mask3, 0, 0, 74⟩]

/-- tiny sizes of this library's own -/
def tinyPar : Par where
  fld := .two
  K := 4
  stages := [⟨⟨9, 16, 3⟩, ⟨9, 16, 3⟩, 2, 0, 3⟩,
    ⟨⟨8, 8, 3⟩, ⟨8, 32, 3⟩, 1, 1, 3⟩, ⟨⟨8, 8, 3⟩, ⟨8, 128, 3⟩, 0, 0, 3⟩]
  work := 4

/-- The conditions on sizes that Fmt/M1Codes.lean tests on its six codes (`Full`), from one stage to
the next: the main tables have one size; the next mask table has room. `codeFits`: a code has room
for message and tail. `Par.fits`: and a stage's two codes have one length. -/
def stepFits (old new : Stage) : Bool :=
  2 ^ new.k * new.C.l == old.C.l &&
    decide (2 * old.Z.l + old.C.r + 2 * old.Z.r + 1 ≤ 2 ^ new.h * new.Z.l)
def codeFits (c : Code) : Bool := decide (c.l + c.r ≤ 2 ^ c.a)
def stagesFit : List Stage → Bool
  | a :: b :: l => stepFits a b && stagesFit (b :: l)
  | _ => true
def Par.fits (P : Par) : Bool :=
  stagesFit P.stages && P.stages.all fun s => codeFits s.C && codeFits s.Z && s.C.a == s.Z.a

/-- a round as a line of the table below: name, kind, prover's bytes, roots, answers, elements
drawn, positions, range, work, rows batched -/
def line (r : Round) : String × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (r.entry.name, r.kind.num, r.entry.msg, r.entry.roots, r.entry.answers, r.entry.drawE,
    r.entry.poss, r.entry.logN, r.entry.work, r.entry.rows)

-- the table of thirty rounds in a wording of the text, line for line
#guard (roundsOf toyPar).map line == [
  ("SEND seed", 3, 32, 1, 0, 16, 0, 0, 0, 0),
  ("SEND answer", 7, 24, 0, 1, 0, 0, 0, 0, 0),
  ("ZERO", 1, 0, 0, 0, 12, 0, 0, 0, 0),
  ("PSC epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC Y", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("PSC values", 7, 48, 0, 0, 0, 0, 0, 0, 0),
  ("BAT", 1, 0, 0, 0, 1, 0, 0, 0, 4),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 14, 0, 0, 0, 0),
  ("CS", 4, 24, 0, 1, 1, 73, 15, 20, 221),
  ("FOLD epsilon", 2, 24, 0, 0, 1, 0, 0, 0, 0),
  ("FOLD round", 1, 48, 0, 0, 1, 0, 0, 0, 0),
  ("SEND seed", 3, 32, 1, 0, 13, 0, 0, 0, 0),
  ("CS", 4, 24, 0, 1, 1, 74, 14, 20, 224),
  ("BASE lambda", 1, 24, 0, 0, 1, 0, 0, 0, 0),
  ("BASE", 4, 77280, 0, 0, 0, 74, 14, 20, 0)]
-- the drawn elements that must not be 0: one each in the table's rounds 0, 16, 22, 26
#guard ((roundsOf toyPar).zipIdx.filter fun x => x.1.entry.drawNZ != 0).map (fun x => (x.2, x.1.entry.drawNZ)) = [(0, 1), (16, 1), (22, 1), (26, 1)]
-- the roots: in the table's rounds 0, 22, 26, one each
#guard ((roundsOf toyPar).zipIdx.filter fun x => x.1.entry.roots != 0).map (fun x => (x.2, x.1.entry.roots)) = [(0, 1), (22, 1), (26, 1)]
-- the trees: after which round each is opened; its number, depth, width
#guard ((roundsOf toyPar).zipIdx.flatMap fun x => x.1.opens.map fun o => (x.2, o.1.tree, o.1.a, o.1.W)) = [(23, 0, 15, 9), (27, 1, 14, 18), (29, 2, 14, 12)]
-- two rounds have an empty verifier's message, two an empty prover's message
#guard ((roundsOf toyPar).zipIdx.filter fun x => x.1.kind == .nothing).map (·.2) = [1, 17]
#guard ((roundsOf toyPar).zipIdx.filter fun x => x.1.entry.msg == 0).map (·.2) = [2, 18]
-- the elements in the clear; the coordinates of the three samples
#guard toyPar.stages.map clearN = [4274, 2452, 3220]
#guard toyPar.stages.map Stage.na = [15, 13, 12]
-- The description's own conditions hold, at the toy's sizes and at the tiny ones. At the toy's
-- sizes they are tried at two choices of the configuration's 32 bytes and of the further items. By
-- their form the conditions look at neither, but for the configuration's length, 32; the length of
-- the parameters' bytes, in `Spec.small`; and the beginning of these bytes, which `specOf` makes
-- from the same plan and configuration.
#guard toyPar.planOK && (specOf toyPar zero32 []).ok
#guard (specOf toyPar (pattern 32) [("codes", pattern 8)]).ok
#guard tinyPar.planOK && (specOf tinyPar zero32 []).ok
-- both records of sizes fit from stage to stage; the first mask table has room for what the
-- sum-check takes and a pad (1 + 2 K + 2 + 2, and 1)
#guard toyPar.fits && tinyPar.fits
#guard [toyPar, tinyPar].all fun P => P.stages.head?.any fun s => decide (1 + 2 * P.K + 2 + 2 + 1 ≤ s.Z.l) && s.C.l == 2 ^ P.K
#guard (roundsOf tinyPar).length = 22
-- as many rounds as the decision takes off its list (Fmt/M1Dec.lean)
#guard [toyPar, tinyPar].all fun P => (roundsOf P).length == nRounds P
-- the bytes of a file but for its three openings: the random bytes, the sum of the table's column
-- of the prover's bytes (added up by the program that put the table in), three nonces of 8 bytes
-- (taken by this library: the text does not say how many bytes a nonce has in a file);
-- confirmed (R12.8)
#guard fixedLen toyPar = 32 + 78360 + 3 * 8

end M1
end Fmt
