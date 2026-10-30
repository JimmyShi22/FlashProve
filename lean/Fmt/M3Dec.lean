-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Dec.lean: the algebraic part of the verifier for an entry file: the verifier's decision on
what the reader has read.

An entry file holds the messages of a protocol, the link, whose purpose is to show that a further
stored copy of a committed table holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). The file has that protocol in its non-interactive
form, in bytes. A reader (Fmt/Rules8X.lean) cuts the file, recomputes the hash chain and checks the
Merkle openings. It hands on a view: for every round what was sent and what was drawn, and the
opened columns. This file is the algebraic part of the check, as a function of that view.
Definitions that compute. Core Lean, no Mathlib.

Sources. Written from the programs' description of the entry file (its part 10) and from the
answers to questions about it; this file's sources include no file made by the programs (the C++
implementation that comes with this Lean code) for this protocol. The rounds as rendered here are
those of the format page
(docs/format/FORMAT.md, which comes with the programs; here in an edition that is not the one that
ships), rule R13.10, at one answer to a sample and with the first fold's mask sent ahead. This
file's sources do not include the rule; its text, in that edition, was compared with `decBy`, row by
row, in a second, independent reading.






The course of the decision. Five rounds test nothing but their numbers of elements and positions,
and give the data of the rows. The five, in order:
   "LINK point":  nothing is sent; gamma is drawn, v elements.
   "SEND seed":   one root is sent; the seed is drawn, that is the coordinates of the members' cube
                  (`seedLen` counts these) and then beta.
   "SEND answer": the two answers are sent; nothing is drawn.
   "LINK":        nothing is sent; nu0 + nuj positions and no element are drawn.
   "LINK phi":    nothing is sent; phi is drawn, clog l elements.
Then the round "BAT" draws theta, and all rows are combined under the powers of theta
(Fmt/M3Link.lean, `batchLit`). Then follows the proximity test on the one group (Fmt/M2Last.lean,
`lastAt`), whose tree is the chain's tree number 0, with one row of a fresh mask in the same tree
(the argument 1 of `lastAt`).

1. What the file contains.
   `sizesOK`            The conditions on the sizes. Here l and r are the message length and the
                        tail length of the tables' code T, l_u is the message length of the group's
                        code C, and l_zk that of a stage's code Z. The other sizes (s, v, nu0, nuj,
                        R, t0, and the layout word, the field `high`) are those of `Par`,
                        Fmt/M3Types.lean; k and h are those of `Stage`, Fmt/M1Types.lean.
                        The conditions, in the order of the code:
                        - s = 0: a table with a record (FORMAT.md, R4.8; s > 0) is not rendered.
                        - The group's two codes have message lengths that are powers of two.
                        - There is at least one row.
                        - The folded tail ends before the sample's pad: t0 + r + 1 ≤ R l_u
                          (by an answer to questions, the programs' test on the public files
                          asks the same, at one sample). The head of Fmt/M2Send.lean says what a
                          pad is.
                        - Without the layout word, R is a power of two (by an answer too).
                        - The first stage is the group (its codes; k and h as the members give
                          them).
                        - The stages fit each other, as in the second toy (a chain of three links).
                          In full, that is every condition below but the one on the mask row:
                          - There are at least two stages.
                          - Neighbours fit (`fitsAll`, Fmt/M1Dec.lean).
                          - The two codes of every stage have message lengths that are powers of
                            two.
                          - 1 ≤ k in every stage but the last.
                          - In every stage but the last the public vector of the hiding polynomial
                            fits the mask row: h + 2 (k - h) + 1 ≤ l_zk. (Why this clause:
                            Fmt/M1Fold.lean's `hideVec` is cut silently where the row is shorter,
                            and here k grows with R.)
                          - k = h = 0 in the last stage.
                        That l ≤ 2^(clog l) needs no test.
   `decBy`, `decWith`, `dec`
                        The decision: given a way of combining the rows; with the literal one, which
                        writes every row out; and at the first toy's blocks, from the reader's view.
                        What the first toy is: the head of Fmt/M1Types.lean.
   What is tested before the last block (the field `base` of `M1.Blocks`): the sizes (`sizesOK`);
   the numbers of elements and positions of each round; that each drawn column of a stored table was
   opened and has 2^v words; inside the proximity test, that each drawn column of one of the chain's
   own trees was opened and has its width. No equation between field elements is tested before the
   last block.

2. What is checked when the file compiles. No test stands in this file.




   This decision is run on no file of the programs.

3. Theorems. None in this file.

4. What is not claimed.
   It is not claimed that this is the decision that the programs compute. It is a reading of their
   description.
   No statement on soundness follows from this file. In Fmt/ and Run/ no soundness statement is made
   for the protocol that it checks. The library has a link protocol with such statements
   (Cb/Ld/LdLink.lean); no theorem of Fmt/ or Run/ relates this decision to it. Which conditions of
   the library's compilation theorems the entry file's protocol meets, and which it does not, is the
   subject of Run/PlanQXDoor.lean.
   These are not here, because they are the reader's and the compiled verifier's part: the head of
   the file, the copy's root, the statement, the proof of work, the openings up to their roots.
   A refusal of public files that are not admitted is not here either.
   The programs' verdict "yes, with its work counted" is a statement about the plan, not about a
   file.
   Tables with a record (s > 0) are not covered.
   Neither are the other settings that FORMAT.md, R13.10 allows: more than one answer to a sample,
   and a first fold's mask that is not sent ahead.

Compared outside this development, not on the programs' files (so these runs are not tests that are
made when a file compiles). The decision was run against a reference verifier of this library's own
in
Python, written from the same description by another writer, but not independently of this file.
At four sets of small sizes (l and R not powers of two; a position drawn twice within a part and in
both parts; a second stage with k = 2): the 4 honest entries accepted, 32 false ones of eight kinds
refused, the 28 intermediate values equal on each of the 36; and, behind the reader of
Fmt/Rules8X.lean, 108 whole files with the verdicts predicted.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M3Link
import Fmt.M2Last
import Fmt.M1All

set_option autoImplicit false

namespace Fmt.M3
open Fmt.M1 Fmt.M2

/-- The sizes fit: the test on the sizes whose conditions the head tells under 1. -/
def sizesOK (B : M1.Blocks) (P : Par) : Bool :=
  P.s == 0 && P.C.l == 2 ^ lg P.C.l && P.Z.l == 2 ^ lg P.Z.l && decide (1 ≤ P.R) &&
    decide (P.t0 + P.T.r + 1 ≤ P.R * P.C.l) && (P.high || P.R == 2 ^ clog P.R) &&
  (match P.stages.head? with
    | some s => s.C == P.C && s.Z == P.Z && s.k == kOf P.mems && s.h == hOf P.mems
    | none => false) &&
  decide (2 ≤ P.stages.length) && fitsAll B P.stages &&
  P.stages.all (fun s => s.C.l == 2 ^ lg s.C.l && s.Z.l == 2 ^ lg s.Z.l) &&
    P.stages.dropLast.all
      (fun s => decide (1 ≤ s.k) && decide (s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l)) &&
  (match P.stages.getLast? with
    | some s => s.k == 0 && s.h == 0
    | none => false)

/-- A way of combining the rows into one. Its arguments: gamma; the seed (the point, then beta); the
two answers; the positions; phi; theta. -/
abbrev Batch : Type := List E → List E → E → E → E → List Nat → List E → E → Option KRow

/-- The decision, given the blocks `B` and a way `bt` of combining the rows. -/
def decBy (B : M1.Blocks) (P : Par) (V : View) (bt : Batch) : Bool :=
  sizesOK B P &&
  match nextN 0 P.v 0 V.rounds with
  | some (vg, rs1) =>
    match seedOf (seedLen (lg P.C.l) (lg P.Z.l) P.mems) rs1 with
    | some (z, beta, rs2) =>
      match nextN 2 0 0 rs2 with
      | some (⟨[y0, yj], _, _⟩, rs3) =>
        match nextN 0 0 (P.nu0 + P.nuj) rs3 with
        | some (vx, rs4) =>
          match nextN 0 P.aPhi 0 rs4 with
          | some (vp, rs5) =>
            match nextN 0 1 0 rs5 with
            | some (⟨_, [theta], _⟩, rs6) =>
              match bt vg.els z beta y0 yj vx.poss vp.els theta with
              | some R => lastAt B P.fld P.stages P.mems 1 0 V.own R.toG rs6
              | none => false
            | _ => false
          | none => false
        | none => false
      | _ => false
    | none => false
  | none => false

/-- The decision, given the blocks: every row is written out (`batchLit`, Fmt/M3Link.lean). -/
def decWith (B : M1.Blocks) (P : Par) (V : View) : Bool := decBy B P V (batchLit P V)

/-- The decision, at the first toy's blocks, from the reader's view. -/
def dec (P : Par) (V : _root_.Fmt.View) : Bool := decWith M1.blocks P (ofView (M1.ofView V))

/-- The number of rounds that the decision reads. -/
def nRounds (P : Par) : Nat := 6 + ((P.stages.dropLast.map fun s => s.k + 3).sum) + 2

/-! ## Tests on numbers -/

namespace DecT
end DecT







end Fmt.M3
