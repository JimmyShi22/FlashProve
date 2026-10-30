-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/Plan0.lean: the plan of the first proof chain as data, and the hypothesis on the
proof file's protocol from named hypotheses by family.

Definitions, guards by evaluation, statements and proofs. The table `plan0` was made by a program,
outside Lean, from a print of the verifier's plan at the full configuration (made at the three
shipped files of prover/examples/target_full_f2; by the
printing tool's own account it reads these three files alone): the blocks of the first proof chain,
the blocks of each lookup merged into one: 521 places. For each place: its family (17), its number
of entries of the plan, the family of the seam behind it (74, by the names of the two neighbours;
the last one leads into the tail step).

Main names:
  `KObj.PFam`, `KObj.plan0`, `KObj.seamNames`, `KObj.fam0`, `KObj.sfam0`, `KObj.ent0`: the table.
  `KObj.PFile.FitsPlan0`: the block at each place has as many rounds as the plan has entries there
    (data; no premise of the theorem).
  `KObj.PFile.Families`: the named hypotheses by family. `KObj.proofSound_plan0`: from them the
    hypothesis `proofSound` (Johnson/Top/OnFilesAt.lean), word for word, at the passed object.
Limits: K is a parameter: the families' names and doc comments bind nothing until K is written;
logically the form by family is `PFile.Fields` again, with labels. The counts of entries stand in
doc comments and guards alone and no hypothesis reads them: a sentence "so many entries stand under
a proved kind" is a sentence on the table, not on W and not on the theorem. The 521 seams are
sorted by 74 names: that the seams of one name are one proposition is not said. No theorem ties
`plan0` to the verifier's planner. W, the written proof file, is a parameter: no block is written
here, and `isOf` is a hypothesis. That a family's kind is the step that the programs run is not
said.
-/
import Johnson.E.KObj.PFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb Compile Compile.Batch Compile.Batch.Cms
open scoped ENNReal

/-- the families of blocks of the first proof chain -/
inductive PFam
  /-- a sub-proof's lookup of all calls, with its shift -/
  | lookupCalls
  /-- the lookup of a smallness test's digits, with its shift -/
  | lookupDigits
  /-- a masked sumcheck -/
  | psc
  /-- a product level: a masked sumcheck and a line draw -/
  | level
  /-- hidden scalars, a batching draw, then a masked sumcheck -/
  | batPsc
  /-- the batching of a group and its fold -/
  | batFold
  /-- a sending of oracle messages -/
  | send
  /-- hidden scalars (or none) and a batching draw -/
  | batSigma
  /-- a proximity stage: fold, sending, consistency -/
  | foldSendCs
  /-- the draw of a point -/
  | zero
  /-- the smallness test's draw -/
  | rng
  /-- the locations -/
  | loc
  /-- the draw of a joining point -/
  | join
  /-- the reply, then a sending -/
  | replySend
  /-- the last proximity stage -/
  | base
  /-- a batching draw before the proximity stages -/
  | bat
  /-- the chain's seal -/
  | sealR
  deriving DecidableEq, Repr

/-- place by place: the family, the entries of the plan, the family of the seam behind the place -/
def plan0 : List (PFam × ℕ × ℕ) :=
  [(.send, 2, 0), (.lookupCalls, 1046, 1), (.zero, 1, 2),
   (.zero, 1, 3), (.zero, 1, 4), (.batSigma, 1, 5),
   (.join, 1, 6), (.level, 30, 7), (.batPsc, 14, 8),
   (.psc, 13, 9), (.batSigma, 1, 10), (.psc, 26, 11),
   (.level, 30, 12), (.join, 1, 13), (.level, 28, 14),
   (.batPsc, 22, 15), (.send, 2, 16), (.rng, 1, 17),
   (.send, 2, 18), (.lookupDigits, 746, 19), (.batSigma, 1, 20),
   (.batFold, 10, 21), (.send, 1, 22), (.loc, 1, 23),
   (.lookupCalls, 984, 24), (.psc, 37, 25), (.psc, 16, 26),
   (.batSigma, 1, 27), (.psc, 19, 28), (.psc, 16, 29),
   (.zero, 1, 30), (.batSigma, 1, 31), (.psc, 23, 32),
   (.batSigma, 1, 33), (.psc, 26, 34), (.batPsc, 21, 35),
   (.send, 2, 36), (.rng, 1, 37), (.send, 2, 38),
   (.lookupDigits, 716, 39), (.batSigma, 1, 40), (.batFold, 9, 41),
   (.send, 1, 42), (.loc, 1, 43), (.lookupCalls, 1046, 1),
   (.zero, 1, 44), (.batSigma, 1, 5), (.join, 1, 6),
   (.level, 30, 7), (.batPsc, 14, 8), (.psc, 13, 9),
   (.batSigma, 1, 10), (.psc, 26, 11), (.level, 30, 12),
   (.join, 1, 13), (.level, 28, 14), (.batPsc, 22, 15),
   (.send, 2, 16), (.rng, 1, 17), (.send, 2, 18),
   (.lookupDigits, 746, 19), (.batSigma, 1, 20), (.batFold, 10, 21),
   (.send, 1, 22), (.loc, 1, 23), (.lookupCalls, 984, 24),
   (.psc, 37, 25), (.psc, 16, 26), (.batSigma, 1, 27),
   (.psc, 19, 28), (.psc, 16, 29), (.zero, 1, 30),
   (.batSigma, 1, 31), (.psc, 23, 32), (.batSigma, 1, 33),
   (.psc, 26, 34), (.batPsc, 21, 35), (.send, 2, 36),
   (.rng, 1, 37), (.send, 2, 38), (.lookupDigits, 716, 39),
   (.batSigma, 1, 40), (.batFold, 9, 41), (.send, 1, 42),
   (.loc, 1, 43), (.lookupCalls, 1046, 1), (.zero, 1, 44),
   (.batSigma, 1, 5), (.join, 1, 6), (.level, 30, 7),
   (.batPsc, 14, 8), (.psc, 13, 9), (.batSigma, 1, 10),
   (.psc, 26, 11), (.level, 30, 12), (.join, 1, 13),
   (.level, 28, 14), (.batPsc, 22, 15), (.send, 2, 16),
   (.rng, 1, 17), (.send, 2, 18), (.lookupDigits, 746, 19),
   (.batSigma, 1, 20), (.batFold, 10, 21), (.send, 1, 22),
   (.loc, 1, 23), (.lookupCalls, 984, 24), (.psc, 37, 25),
   (.psc, 16, 26), (.batSigma, 1, 27), (.psc, 19, 28),
   (.psc, 16, 29), (.zero, 1, 30), (.batSigma, 1, 31),
   (.psc, 23, 32), (.batSigma, 1, 33), (.psc, 26, 34),
   (.batPsc, 21, 35), (.send, 2, 36), (.rng, 1, 37),
   (.send, 2, 38), (.lookupDigits, 716, 39), (.batSigma, 1, 40),
   (.batFold, 9, 41), (.send, 1, 42), (.loc, 1, 43),
   (.lookupCalls, 1046, 1), (.zero, 1, 44), (.batSigma, 1, 5),
   (.join, 1, 6), (.level, 30, 7), (.batPsc, 14, 8),
   (.psc, 13, 9), (.batSigma, 1, 10), (.psc, 26, 11),
   (.level, 30, 12), (.join, 1, 13), (.level, 28, 14),
   (.batPsc, 22, 15), (.send, 2, 16), (.rng, 1, 17),
   (.send, 2, 18), (.lookupDigits, 746, 19), (.batSigma, 1, 20),
   (.batFold, 10, 21), (.send, 1, 22), (.loc, 1, 23),
   (.lookupCalls, 984, 24), (.psc, 37, 25), (.psc, 16, 26),
   (.batSigma, 1, 27), (.psc, 19, 28), (.psc, 16, 29),
   (.zero, 1, 30), (.batSigma, 1, 31), (.psc, 23, 32),
   (.batSigma, 1, 33), (.psc, 26, 34), (.batPsc, 21, 35),
   (.send, 2, 36), (.rng, 1, 37), (.send, 2, 38),
   (.lookupDigits, 716, 39), (.batSigma, 1, 40), (.batFold, 9, 41),
   (.send, 1, 42), (.loc, 1, 43), (.lookupCalls, 1046, 1),
   (.zero, 1, 44), (.batSigma, 1, 5), (.join, 1, 6),
   (.level, 30, 7), (.batPsc, 14, 8), (.psc, 13, 9),
   (.batSigma, 1, 10), (.psc, 26, 11), (.level, 30, 12),
   (.join, 1, 13), (.level, 28, 14), (.batPsc, 22, 15),
   (.send, 2, 16), (.rng, 1, 17), (.send, 2, 18),
   (.lookupDigits, 746, 19), (.batSigma, 1, 20), (.batFold, 10, 21),
   (.send, 1, 22), (.loc, 1, 23), (.lookupCalls, 984, 24),
   (.psc, 37, 25), (.psc, 16, 26), (.batSigma, 1, 27),
   (.psc, 19, 28), (.psc, 16, 29), (.zero, 1, 30),
   (.batSigma, 1, 31), (.psc, 23, 32), (.batSigma, 1, 33),
   (.psc, 26, 34), (.batPsc, 21, 35), (.send, 2, 36),
   (.rng, 1, 37), (.send, 2, 38), (.lookupDigits, 716, 39),
   (.batSigma, 1, 40), (.batFold, 9, 41), (.send, 1, 42),
   (.loc, 1, 43), (.lookupCalls, 1046, 1), (.zero, 1, 44),
   (.batSigma, 1, 5), (.join, 1, 6), (.level, 30, 7),
   (.batPsc, 14, 8), (.psc, 13, 9), (.batSigma, 1, 10),
   (.psc, 26, 11), (.level, 30, 12), (.join, 1, 13),
   (.level, 28, 14), (.batPsc, 22, 15), (.send, 2, 16),
   (.rng, 1, 17), (.send, 2, 18), (.lookupDigits, 746, 19),
   (.batSigma, 1, 20), (.batFold, 10, 21), (.send, 1, 22),
   (.loc, 1, 23), (.lookupCalls, 984, 24), (.psc, 37, 25),
   (.psc, 16, 26), (.batSigma, 1, 27), (.psc, 19, 28),
   (.psc, 16, 29), (.zero, 1, 30), (.batSigma, 1, 31),
   (.psc, 23, 32), (.batSigma, 1, 33), (.psc, 26, 34),
   (.batPsc, 21, 35), (.send, 2, 36), (.rng, 1, 37),
   (.send, 2, 38), (.lookupDigits, 716, 39), (.batSigma, 1, 40),
   (.batFold, 9, 41), (.send, 1, 42), (.loc, 1, 43),
   (.lookupCalls, 1046, 1), (.zero, 1, 44), (.batSigma, 1, 5),
   (.join, 1, 6), (.level, 30, 7), (.batPsc, 14, 8),
   (.psc, 13, 9), (.batSigma, 1, 10), (.psc, 26, 11),
   (.level, 30, 12), (.join, 1, 13), (.level, 28, 14),
   (.batPsc, 22, 15), (.send, 2, 16), (.rng, 1, 17),
   (.send, 2, 18), (.lookupDigits, 746, 19), (.batSigma, 1, 20),
   (.batFold, 10, 21), (.send, 1, 22), (.loc, 1, 23),
   (.lookupCalls, 984, 24), (.psc, 37, 25), (.psc, 16, 26),
   (.batSigma, 1, 27), (.psc, 19, 28), (.psc, 16, 29),
   (.zero, 1, 30), (.batSigma, 1, 31), (.psc, 23, 32),
   (.batSigma, 1, 33), (.psc, 26, 34), (.batPsc, 21, 35),
   (.send, 2, 36), (.rng, 1, 37), (.send, 2, 38),
   (.lookupDigits, 716, 39), (.batSigma, 1, 40), (.batFold, 9, 41),
   (.send, 1, 42), (.loc, 1, 43), (.lookupCalls, 1046, 1),
   (.zero, 1, 44), (.batSigma, 1, 5), (.join, 1, 6),
   (.level, 30, 7), (.batPsc, 14, 8), (.psc, 13, 9),
   (.batSigma, 1, 10), (.psc, 26, 11), (.level, 30, 12),
   (.join, 1, 13), (.level, 28, 14), (.batPsc, 22, 15),
   (.send, 2, 16), (.rng, 1, 17), (.send, 2, 18),
   (.lookupDigits, 746, 19), (.batSigma, 1, 20), (.batFold, 10, 21),
   (.send, 1, 22), (.loc, 1, 23), (.lookupCalls, 984, 24),
   (.psc, 37, 25), (.psc, 16, 26), (.batSigma, 1, 27),
   (.psc, 19, 28), (.psc, 16, 29), (.zero, 1, 30),
   (.batSigma, 1, 31), (.psc, 23, 32), (.batSigma, 1, 33),
   (.psc, 26, 34), (.batPsc, 21, 35), (.send, 2, 36),
   (.rng, 1, 37), (.send, 2, 38), (.lookupDigits, 716, 39),
   (.batSigma, 1, 40), (.batFold, 9, 41), (.send, 1, 42),
   (.loc, 1, 43), (.lookupCalls, 1046, 1), (.zero, 1, 44),
   (.batSigma, 1, 5), (.join, 1, 6), (.level, 30, 7),
   (.batPsc, 14, 8), (.psc, 13, 9), (.batSigma, 1, 10),
   (.psc, 26, 11), (.level, 30, 12), (.join, 1, 13),
   (.level, 28, 14), (.batPsc, 22, 15), (.send, 2, 16),
   (.rng, 1, 17), (.send, 2, 18), (.lookupDigits, 746, 19),
   (.batSigma, 1, 20), (.batFold, 10, 21), (.send, 1, 22),
   (.loc, 1, 23), (.lookupCalls, 984, 24), (.psc, 37, 25),
   (.psc, 16, 26), (.batSigma, 1, 27), (.psc, 19, 28),
   (.psc, 16, 29), (.zero, 1, 30), (.batSigma, 1, 31),
   (.psc, 23, 32), (.batSigma, 1, 33), (.psc, 26, 34),
   (.batPsc, 21, 35), (.send, 2, 36), (.rng, 1, 37),
   (.send, 2, 38), (.lookupDigits, 716, 39), (.batSigma, 1, 40),
   (.batFold, 9, 41), (.send, 1, 42), (.loc, 1, 43),
   (.lookupCalls, 1046, 1), (.zero, 1, 44), (.batSigma, 1, 5),
   (.join, 1, 6), (.level, 30, 7), (.batPsc, 14, 8),
   (.psc, 13, 9), (.batSigma, 1, 10), (.psc, 26, 11),
   (.level, 30, 12), (.join, 1, 13), (.level, 28, 14),
   (.batPsc, 22, 15), (.send, 2, 16), (.rng, 1, 17),
   (.send, 2, 18), (.lookupDigits, 746, 19), (.batSigma, 1, 20),
   (.batFold, 10, 21), (.send, 1, 22), (.loc, 1, 23),
   (.lookupCalls, 984, 24), (.psc, 37, 25), (.psc, 16, 26),
   (.batSigma, 1, 27), (.psc, 19, 28), (.psc, 16, 29),
   (.zero, 1, 30), (.batSigma, 1, 31), (.psc, 23, 32),
   (.batSigma, 1, 33), (.psc, 26, 34), (.batPsc, 21, 35),
   (.send, 2, 36), (.rng, 1, 37), (.send, 2, 38),
   (.lookupDigits, 716, 39), (.batSigma, 1, 40), (.batFold, 9, 41),
   (.send, 1, 42), (.loc, 1, 43), (.lookupCalls, 1046, 1),
   (.zero, 1, 44), (.batSigma, 1, 5), (.join, 1, 6),
   (.level, 30, 7), (.batPsc, 14, 8), (.psc, 13, 9),
   (.batSigma, 1, 10), (.psc, 26, 11), (.level, 30, 12),
   (.join, 1, 13), (.level, 28, 14), (.batPsc, 22, 15),
   (.send, 2, 16), (.rng, 1, 17), (.send, 2, 18),
   (.lookupDigits, 746, 19), (.batSigma, 1, 20), (.batFold, 10, 21),
   (.send, 1, 22), (.loc, 1, 23), (.lookupCalls, 984, 24),
   (.psc, 37, 25), (.psc, 16, 26), (.batSigma, 1, 27),
   (.psc, 19, 28), (.psc, 16, 29), (.zero, 1, 30),
   (.batSigma, 1, 31), (.psc, 23, 32), (.batSigma, 1, 33),
   (.psc, 26, 34), (.batPsc, 21, 35), (.send, 2, 36),
   (.rng, 1, 37), (.send, 2, 38), (.lookupDigits, 716, 39),
   (.batSigma, 1, 40), (.batFold, 9, 41), (.send, 1, 42),
   (.loc, 1, 43), (.lookupCalls, 1046, 1), (.zero, 1, 44),
   (.batSigma, 1, 5), (.join, 1, 6), (.level, 30, 7),
   (.batPsc, 14, 8), (.psc, 13, 9), (.batSigma, 1, 10),
   (.psc, 26, 11), (.level, 30, 12), (.join, 1, 13),
   (.level, 28, 14), (.batPsc, 22, 15), (.send, 2, 16),
   (.rng, 1, 17), (.send, 2, 18), (.lookupDigits, 746, 19),
   (.batSigma, 1, 20), (.batFold, 10, 21), (.send, 1, 22),
   (.loc, 1, 23), (.lookupCalls, 984, 24), (.psc, 37, 25),
   (.psc, 16, 26), (.batSigma, 1, 27), (.psc, 19, 28),
   (.psc, 16, 29), (.zero, 1, 30), (.batSigma, 1, 31),
   (.psc, 23, 32), (.batSigma, 1, 33), (.psc, 26, 34),
   (.batPsc, 21, 35), (.send, 2, 36), (.rng, 1, 37),
   (.send, 2, 38), (.lookupDigits, 716, 39), (.batSigma, 1, 40),
   (.batFold, 9, 45), (.replySend, 2, 46), (.loc, 1, 47),
   (.lookupCalls, 1080, 48), (.zero, 1, 49), (.batSigma, 1, 50),
   (.level, 27, 51), (.batPsc, 14, 52), (.psc, 13, 53),
   (.psc, 26, 54), (.send, 2, 55), (.rng, 1, 56),
   (.send, 2, 57), (.lookupDigits, 746, 58), (.batPsc, 22, 59),
   (.batSigma, 1, 60), (.batFold, 10, 61), (.send, 1, 62),
   (.loc, 1, 63), (.bat, 1, 64), (.foldSendCs, 4, 65),
   (.foldSendCs, 7, 66), (.foldSendCs, 6, 67), (.foldSendCs, 6, 68),
   (.foldSendCs, 7, 69), (.base, 2, 70), (.batPsc, 20, 71),
   (.send, 2, 72), (.sealR, 1, 73)]

/-- the seams' families, by the names of the two neighbours -/
def seamNames : List (String × String) :=
  [("G# | (its own rounds) :: SEND",
    "G# | LOOKUP calls"),
   ("G# | LOOKUP calls",
    "G# | the norms' token point :: ZERO"),
   ("G# | the norms' token point :: ZERO",
    "G# | the embedding's point :: ZERO"),
   ("G# | the embedding's point :: ZERO",
    "G# | the embedding's feature point :: ZERO"),
   ("G# | the embedding's feature point :: ZERO",
    "G# | limbs :: BAT-sigma"),
   ("G# | limbs :: BAT-sigma",
    "G# | norm instances :: JOIN"),
   ("G# | norm instances :: JOIN",
    "G# | sums of squares :: PSC+LINE"),
   ("G# | sums of squares :: PSC+LINE",
    "G# | row products :: BAT-sigma+PSC"),
   ("G# | row products :: BAT-sigma+PSC",
    "G# | terms :: PSC"),
   ("G# | terms :: PSC",
    "G# | start of the inner products :: BAT-sigma"),
   ("G# | start of the inner products :: BAT-sigma",
    "G# | inner products :: PSC"),
   ("G# | inner products :: PSC",
    "G# | gated products :: PSC+LINE"),
   ("G# | gated products :: PSC+LINE",
    "G# | layers with routed experts :: JOIN"),
   ("G# | layers with routed experts :: JOIN",
    "G# | routed gated products :: PSC+LINE"),
   ("G# | routed gated products :: PSC+LINE",
    "G# | weight claims :: BAT-sigma+PSC"),
   ("G# | weight claims :: BAT-sigma+PSC",
    "G# | (its own rounds) :: SEND"),
   ("G# | (its own rounds) :: SEND",
    "G# | smallness test :: RNG"),
   ("G# | smallness test :: RNG",
    "G# | (its own rounds) :: SEND"),
   ("G# | (its own rounds) :: SEND",
    "G# | LOOKUP digits"),
   ("G# | LOOKUP digits",
    "G# | claims :: BAT-sigma"),
   ("G# | claims :: BAT-sigma",
    "G# | (its own rounds) :: BAT+FOLD"),
   ("G# | (its own rounds) :: BAT+FOLD",
    "A# | (its own rounds) :: SEND"),
   ("A# | (its own rounds) :: SEND",
    "G# | (its own rounds) :: LOC"),
   ("G# | (its own rounds) :: LOC",
    "attention # | LOOKUP calls"),
   ("attention # | LOOKUP calls",
    "attention # | scores :: PSC"),
   ("attention # | scores :: PSC",
    "attention # | Z o :: PSC"),
   ("attention # | Z o :: PSC",
    "attention # | numerator and denominator :: BAT-sigma"),
   ("attention # | numerator and denominator :: BAT-sigma",
    "attention # | value product, off the diagonal :: PSC"),
   ("attention # | value product, off the diagonal :: PSC",
    "attention # | value product, diagonal :: PSC"),
   ("attention # | value product, diagonal :: PSC",
    "attention # | the maximum is attained; the index bits are bits :: ZERO"),
   ("attention # | the maximum is attained; the index bits are bits :: ZERO",
    "attention # | maxima :: BAT-sigma"),
   ("attention # | maxima :: BAT-sigma",
    "attention # | q k at the index :: PSC"),
   ("attention # | q k at the index :: PSC",
    "attention # | keys at the index :: BAT-sigma"),
   ("attention # | keys at the index :: BAT-sigma",
    "attention # | the key at the index :: PSC"),
   ("attention # | the key at the index :: PSC",
    "attention # | index bits :: BAT-sigma+PSC"),
   ("attention # | index bits :: BAT-sigma+PSC",
    "A# | (its own rounds) :: SEND"),
   ("A# | (its own rounds) :: SEND",
    "attention # | smallness test :: RNG"),
   ("attention # | smallness test :: RNG",
    "A# | (its own rounds) :: SEND"),
   ("A# | (its own rounds) :: SEND",
    "attention # | LOOKUP digits"),
   ("attention # | LOOKUP digits",
    "attention # | all rows :: BAT-sigma"),
   ("attention # | all rows :: BAT-sigma",
    "A# | (its own rounds) :: BAT+FOLD"),
   ("A# | (its own rounds) :: BAT+FOLD",
    "G# | (its own rounds) :: SEND"),
   ("G# | (its own rounds) :: SEND",
    "A# | (its own rounds) :: LOC"),
   ("A# | (its own rounds) :: LOC",
    "G# | LOOKUP calls"),
   ("G# | the norms' token point :: ZERO",
    "G# | limbs :: BAT-sigma"),
   ("A# | (its own rounds) :: BAT+FOLD",
    "H | (its own rounds) :: REPLY+SEND"),
   ("H | (its own rounds) :: REPLY+SEND",
    "A# | (its own rounds) :: LOC"),
   ("A# | (its own rounds) :: LOC",
    "head | LOOKUP calls"),
   ("head | LOOKUP calls",
    "head | the norm's point :: ZERO"),
   ("head | the norm's point :: ZERO",
    "head | limbs :: BAT-sigma"),
   ("head | limbs :: BAT-sigma",
    "head | sum of squares :: PSC+LINE"),
   ("head | sum of squares :: PSC+LINE",
    "head | row products :: BAT-sigma+PSC"),
   ("head | row products :: BAT-sigma+PSC",
    "head | stream times reciprocal :: PSC"),
   ("head | stream times reciprocal :: PSC",
    "head | activations times head :: PSC"),
   ("head | activations times head :: PSC",
    "H | (its own rounds) :: SEND"),
   ("H | (its own rounds) :: SEND",
    "head | smallness test :: RNG"),
   ("head | smallness test :: RNG",
    "H | (its own rounds) :: SEND"),
   ("H | (its own rounds) :: SEND",
    "head | LOOKUP digits"),
   ("head | LOOKUP digits",
    "head | merge :: BAT-sigma+PSC"),
   ("head | merge :: BAT-sigma+PSC",
    "head | all rows :: BAT-sigma"),
   ("head | all rows :: BAT-sigma",
    "H | (its own rounds) :: BAT+FOLD"),
   ("H | (its own rounds) :: BAT+FOLD",
    "last group | (its own rounds) :: SEND"),
   ("last group | (its own rounds) :: SEND",
    "H | (its own rounds) :: LOC"),
   ("H | (its own rounds) :: LOC",
    "last group | (its own rounds) :: BAT"),
   ("last group | (its own rounds) :: BAT",
    "last group | stage 1 :: FOLD+SEND+CS"),
   ("last group | stage 1 :: FOLD+SEND+CS",
    "last group | stage 2 :: FOLD+SEND+CS"),
   ("last group | stage 2 :: FOLD+SEND+CS",
    "last group | stage 3 :: FOLD+SEND+CS"),
   ("last group | stage 3 :: FOLD+SEND+CS",
    "last group | stage 4 :: FOLD+SEND+CS"),
   ("last group | stage 4 :: FOLD+SEND+CS",
    "last group | stage 5 :: FOLD+SEND+CS"),
   ("last group | stage 5 :: FOLD+SEND+CS",
    "last group | last stage :: BASE"),
   ("last group | last stage :: BASE",
    "rows on the table | (its own rounds) :: BAT-sigma+PSC"),
   ("rows on the table | (its own rounds) :: BAT-sigma+PSC",
    "table | W :: SEND"),
   ("table | W :: SEND",
    "first chain | (its own rounds) :: SEAL"),
   ("first chain | (its own rounds) :: SEAL",
    "(the tail step)")]

def fam0 (i : ℕ) : PFam := (plan0.getD i (.sealR, 0, 0)).1
def sfam0 (i : ℕ) : ℕ := (plan0.getD i (.sealR, 0, 0)).2.2
/-- the entries of the plan under a family -/
def entriesOf (f : PFam) : ℕ := ((plan0.filter fun x => x.1 = f).map fun x => x.2.1).sum
def placesOf (f : PFam) : ℕ := (plan0.filter fun x => x.1 = f).length

#guard plan0.length = 521
#guard (plan0.map fun x => x.2.1).sum = 48293
#guard seamNames.length = 74
#guard plan0.all fun x => x.2.2 < seamNames.length
#guard (placesOf .lookupCalls, entriesOf .lookupCalls) = (25, 25440)
#guard (placesOf .lookupDigits, entriesOf .lookupDigits) = (25, 18290)
#guard (placesOf .psc, entriesOf .psc) = (98, 2151)
#guard (placesOf .level, entriesOf .level) = (37, 1083)
#guard (placesOf .batPsc, entriesOf .batPsc) = (39, 740)
#guard (placesOf .batFold, entriesOf .batFold) = (25, 238)
#guard (placesOf .send, entriesOf .send) = (76, 128)
#guard (placesOf .batSigma, entriesOf .batSigma) = (86, 86)
#guard (placesOf .foldSendCs, entriesOf .foldSendCs) = (5, 30)
#guard (placesOf .zero, entriesOf .zero) = (27, 27)
#guard (placesOf .rng, entriesOf .rng) = (25, 25)
#guard (placesOf .loc, entriesOf .loc) = (25, 25)
#guard (placesOf .join, entriesOf .join) = (24, 24)
#guard (placesOf .replySend, entriesOf .replySend) = (1, 2)
#guard (placesOf .base, entriesOf .base) = (1, 2)
#guard (placesOf .bat, entriesOf .bat) = (1, 1)
#guard (placesOf .sealR, entriesOf .sealR) = (1, 1)

/-- the entries of the plan at a place -/
def ent0 (i : ℕ) : ℕ := (plan0.getD i (.sealR, 0, 0)).2.1

/-- the written proof file's block at each place has as many rounds as the plan has entries there
(DATA; no premise of the theorem below) -/
def PFile.FitsPlan0 (W : PFile) : Prop := ∀ i ≤ W.n, (W.row.blk i).R.shape.length = ent0 i

/-- The named hypotheses of `proofSound`, by family. K f, the kind of the family f, is a parameter:
the names bind nothing until K is written. -/
structure PFile.Families (W : PFile) (K : PFam → KFam.{1}) : Prop where
  /-- the written proof file has the plan's 521 places -/
  places : W.n + 1 = plan0.length
  /-- DATA: the block at each place is a value of its family's kind -/
  isOf   : ∀ i ≤ W.n, (W.row.blk i).IsOf (K (fam0 i))
  /-- every block of the kind "a sub-proof's lookup of all calls, with its shift" has its property
  (25 places, 25,440 entries) -/
  lookupCalls : (K .lookupCalls).Good
  /-- every block of the kind "the lookup of a smallness test's digits, with its shift" has its
  property (25 places, 18,290 entries) -/
  lookupDigits : (K .lookupDigits).Good
  /-- every block of the kind "a masked sumcheck" has its property (98 places, 2,151 entries) -/
  psc : (K .psc).Good
  /-- every block of the kind "a product level: a masked sumcheck and a line draw" has its property
  (37 places, 1,083 entries) -/
  level : (K .level).Good
  /-- every block of the kind "hidden scalars, a batching draw, then a masked sumcheck" has its
  property (39 places, 740 entries) -/
  batPsc : (K .batPsc).Good
  /-- every block of the kind "the batching of a group and its fold" has its property (25 places,
  238 entries) -/
  batFold : (K .batFold).Good
  /-- every block of the kind "a sending of oracle messages" has its property (76 places, 128
  entries) -/
  send : (K .send).Good
  /-- every block of the kind "hidden scalars (or none) and a batching draw" has its property (86
  places, 86 entries) -/
  batSigma : (K .batSigma).Good
  /-- every block of the kind "a proximity stage: fold, sending, consistency" has its property (5
  places, 30 entries) -/
  foldSendCs : (K .foldSendCs).Good
  /-- every block of the kind "the draw of a point" has its property (27 places, 27 entries) -/
  zero : (K .zero).Good
  /-- every block of the kind "the smallness test's draw" has its property (25 places, 25 entries)
  -/
  rng : (K .rng).Good
  /-- every block of the kind "the locations" has its property (25 places, 25 entries) -/
  loc : (K .loc).Good
  /-- every block of the kind "the draw of a joining point" has its property (24 places, 24 entries)
  -/
  join : (K .join).Good
  /-- every block of the kind "the reply, then a sending" has its property (1 places, 2 entries) -/
  replySend : (K .replySend).Good
  /-- every block of the kind "the last proximity stage" has its property (1 places, 2 entries) -/
  base : (K .base).Good
  /-- every block of the kind "a batching draw before the proximity stages" has its property (1
  places, 1 entries) -/
  bat : (K .bat).Good
  /-- every block of the kind "the chain's seal" has its property (1 places, 1 entries) -/
  sealR : (K .sealR).Good
  /-- the seams, family by family (seamNames) -/
  seams  : ∀ g < seamNames.length, ∀ i ≤ W.n, sfam0 i = g → W.row.SeamAt i
  /-- every block hands the record and the encoded index on -/
  hands  : ∀ i ≤ W.n, (W.row.seated i).Hands (W.rd i) (W.rd (i + 1))
  /-- the head and the tail step -/
  head   : W.head.Good
  headH  : W.head.Hands ⟨Prod.snd, id⟩ (W.rd 0)
  tail   : W.tail.Good
  tailH  : W.tail.Hands (W.rd (W.n + 1)) ⟨Prod.snd, Prod.fst⟩
  /-- the shared and the second proof chain: every batch block has its property -/
  linOn  : W.linOn.Each

theorem sfam0_lt (i : ℕ) : sfam0 i < seamNames.length := by
  unfold sfam0
  by_cases h : i < plan0.length
  · rw [List.getD_eq_getElem _ _ h]
    exact of_decide_eq_true ((List.all_eq_true.1
      (by decide +kernel : (plan0.all fun x => decide (x.2.2 < seamNames.length)) = true)) _
      (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    decide +kernel

theorem PFile.fields_of_families (W : PFile) (K : PFam → KFam.{1}) (F : W.Families K) : W.Fields
    where
  head := F.head
  headH := F.headH
  blocks := W.blocks_by_family fam0 K F.isOf fun f => by
    cases f
    · exact F.lookupCalls
    · exact F.lookupDigits
    · exact F.psc
    · exact F.level
    · exact F.batPsc
    · exact F.batFold
    · exact F.send
    · exact F.batSigma
    · exact F.foldSendCs
    · exact F.zero
    · exact F.rng
    · exact F.loc
    · exact F.join
    · exact F.replySend
    · exact F.base
    · exact F.bat
    · exact F.sealR
  seams := fun i hi => F.seams (sfam0 i) (sfam0_lt i) i hi rfl
  hands := F.hands
  tail := F.tail
  tailH := F.tailH
  linOn := F.linOn

/-- `proofSound` at the passed object of a written proof file, from its hypotheses by family. -/
theorem proofSound_plan0 (W : PFile) (K : PFam → KFam.{1}) (F : W.Families K) (H : W.objB.obj.Hon)
    (Nn : Type) [Inhabited Nn] (σT : Samplers (W.objB.obj.S H).lhr.offline.shape)
    (σL : Samplers (W.objB.obj.S H).lhr.link.shape) (σB : Samplers (W.objB.obj.S
        H).lhr.onlineBatch.loc.shape)
    (g : (W.objB.obj.S H).Bits) (κs Kb κ : ℝ≥0∞) (gdB : σB.Good κs Kb)
    (b1 : Err.BelowG g.req (W.req.blk W.C.cells0).err κ) (b2 : Err.BelowG g.linOn W.linOn.blk.b.err
        κ) :
    ∃ (wit : W.C.X × ((W.objB.obj.S H).lhrW Nn σT σL σB g).Rec →
        (oneExternalString ((W.objB.obj.S H).lhrW Nn σT σL σB g).wordLength ((W.objB.obj.S H).lhrW Nn σT σL σB g).Symbol).Str
            →
        Tr ((W.objB.obj.S H).lhrW Nn σT σL σB g).onlineBatch.loc.shape → W.C.Cells) (ε : _),
      Err.Below ε (κs * κ) ∧ ∀ rec, (((W.objB.obj.S H).lhrW Nn σT σL σB g).batAt rec).SndBKT
        ((W.objB.obj.S H).lhrW Nn σT σL σB g).maxBatchSize ((W.objB.obj.S H).lhrW Nn σT σL σB g).early
        ((W.objB.obj.S H).lhrW Nn σT σL σB g).late (((W.objB.obj.S H).lhrW Nn σT σL σB g).relB
            W.C.Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  W.objB.proofSound_lhrW H (W.proofBlocks (W.fields_of_families K F)) Nn σT σL σB g κs Kb κ gdB b1
      b2

#print axioms KObj.PFile.fields_of_families
#print axioms KObj.proofSound_plan0

end KObj
