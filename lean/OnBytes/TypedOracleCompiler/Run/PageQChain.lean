-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageQChain.lean.
Run/PageQChain.lean: THE CHAIN'S DATA AND THE LEAVES' CODE OF THE ENCODING OF THE QUERIES
(Run/CodingPage.lean: PageC) AT THE GENERIC CONSTRUCTION (Run/PlanQS.lean): BY RECURSION ON THE
ROUNDS' DATA. Definitions that compute, with their laws. After the format page: R5.2, R8.2 (a
round's message), R7.1, R7.3, R7.4 (a column, a leaf's bytes, its label).
Every parameter is the choice C, the rounds' data ds, a number: no round, shape, protocol or
interface is a parameter (shapes stand in types alone): this development's principle for what stands
on a run's path.
   PBL C ds             the type of a plain part of some round behind the trivial round
   rcL C ds i       the partial code of (root or none, plain part) at the round with the number i in
                    ds (from 0): the plain part must be THAT round's slot part; it writes
                    Run/PageQMsg.lean's pRound; a number beyond ds: nothing; rcL_ge: at least 64
                    bits
   pVec W               a column of W words
   PCode.sumF p q       a code on a sum with no condition: a point of the right summand is written
                        only if its string is none of the left code's
   leafCL C salt ds the partial code of a symbol with its position: the word (leaves' number) + 2^16
   (tree's number) + 2^32 (the column's words) + 2^56 (the salt's words) (the format page: R2.1,
   R7.3, R7.4); the word 2^depth + position; the column; the fill's zero bytes
   tagsOK salt ds       A TEST, to be evaluated at a closed description: for each round with a tree,
                        the word with the tree's number has the leaves' number in its low 16 bits;
                        leafCL_tag: then every string begins with these 16 bits
WHAT IS NOT SAID. That the strings are those of Run/PlanQS.lean's spellings (msgSL, nonceSL,
leafSL): another file's tie.

Terms: lean/GLOSSARY.md.

-/
import Run.PageQChain
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage162
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingImpl
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage
import OnBytes.TypedOracleCompiler.Run.PageQMsg
import Run.PlanQS
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: RD, SL, uL are the sibling's (a list of trees a round)
import OnBytes.TypedOracleCompiler.Run.CodingTag
import Run.ToyCode

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ

/-- a plain part of some round behind the trivial round -/
abbrev PBL (C : CK) (ds : List RD) : Type := PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds))

section
variable {R A B : Type}

end

/-- A round's message, at the round with the number i. -/
def rcL (C : CK) : (ds : List RD) → ℕ → PCode (List (Dig 256) × PBL C ds)
  | [], _ => PCode.empty _
  | d :: _, 0 => inL (inR (pRound d.entry.work d.items))
  | _ :: ds, i + 1 => inR (rcL C ds i)

theorem rcL_ge (C : CK) :
    ∀ (ds : List RD) (i : ℕ) (y : List (Dig 256) × PBL C ds) (s : List Bool),
      (rcL C ds i).put y = some s → 64 ≤ s.length
  | [], _, _, _, h => by cases h
  | d :: _, 0, y, s, h => by
      obtain ⟨y1, h1⟩ := inL_put _ y s h
      obtain ⟨y2, h2⟩ := inR_put _ y1 s h1
      rw [pRound_len d.entry.work d.items y2 s h2]
      omega
  | _ :: ds, i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact rcL_ge C ds i y1 s h1

/-! ### Leaves -/

end TypedOracleCompiler.Run.PQ

namespace TypedOracleCompiler.Run.PCode
variable {A B : Type}

end TypedOracleCompiler.Run.PCode

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ

end TypedOracleCompiler.Run.PQ
