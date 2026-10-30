-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsReaders.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIsReaders.lean (only what the entry's clause holds
and stands on a declaration that the sibling says again), then turned by hand where it had to be.
THE HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT
HERE, and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
own_of_ok.

Run/PageIsReaders.lean: the lenient reader against the strict reader: what the lenient reader's
output is, and that it reads whatever the strict reader reads.

Run/PageIs.lean compares two verifiers of a proof file: our rendering in Lean (Fmt/Rules8.lean) of
the verifier of the format page (FORMAT.md, which comes with the programs, that is, with the C++
implementation that accompanies this Lean code), and the compiled verifier behind a lenient reader
that only cuts the file into its parts. This file proves the two statements of that comparison that
concern the readers alone, Spec.pi_facts and Spec.pi_strict1. No typed protocol term occurs: only
the format's readers (Fmt/Rules5.lean, Rules7.lean, Rules8.lean) and the lenient reader
(Run/ParseLax.lean), in the identity monad, at a variable hash function h. The statements ask that
the answers of h have the format's lengths; these proofs do not use that.

1. What the file contains. Theorems with their proofs, and two definitions with which they are
stated (stripO, stripR).
   pi_facts             What the lenient reader's output is. Within the limits of the generic
                        construction (Run.PQ.ok): laxWhole h S b = some o implies LaxFacts h S o.
                        That is: the parameters' digest, the run's value made from 32 random bytes,
                        and the chain's first value are as the format has them; and round by round
                        (TraceL) the data of the query are admitted, the items are the message as
                        read, what was drawn is the format's draw on the row made again from the
                        message and the nonce, and each opening stands at the draw's list of
                        positions, which is an admissible list, under the root that was sent, in the
                        right shape.
   pi_strict1           What the strict reader reads, the lenient one reads. wholeChain h S b = some
                        o' implies that there are o and run with laxWhole h S b = some o, the same
                        view, every round's proof-of-work test passed (passL), and every opening
                        leading to the root that was sent (rootsAll). There is no condition on the
                        roots here: the strict reader's record of the vertices met (FORMAT.md,
                        R7.14) can only add refusals, and the lemmas below hold for any such
                        records.
   The steps. rdOpening_len, open_ok, laxOpens_facts: the openings as cut. laxQuery_some,
   cutStep_facts, cutFold_facts: one round, all rounds. startChain_some. bytes_beq, bytes_beq_self:
   the test "==" on byte strings is equality. stripO, stripR: an opening and a round without the
   vertices met, which is what the lenient reader hands out. readOpening_some, readOpens_lax (on
   reader_id of Run/WalkTieProofs.lean: the root that the strict reader computes is the walk of
   rootOf in Run/PageIs.lean), query_lax, step_lax, fold_lax. own_of_ok, rand_of_ok: within the
   limits every opening is of one of the chain's own trees, and the random bytes stand in the file.
   view_strip.

2. What is checked when the file compiles. No tests (#guard) in this file.

3. Theorems. All of the above; the two that other files use are pi_facts and pi_strict1.

4. What is not claimed.
   The converse (Spec.pi_strict2: what the lenient reader reads, with all proof-of-work tests passed
   and all openings leading to their roots, the strict reader reads) IS NOT HERE. It is proved in
   Run/PageIsStrict2.lean, under the condition that the roots that the file sends differ; it depends
   on the key of the strict reader's record.
   Nothing about the hash function, and NO STATEMENT ON SOUNDNESS.

Terms: lean/GLOSSARY.md.

-/
import Run.PageIsReaders
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseLaws
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import OnBytes.TypedOracleCompiler.Run.PageIs
import Run.LaxDomProofs
import Run.OpenDomProofs
import OnBytes.TypedOracleCompiler.Run.Toy1TieTree

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (rdOpening_len open_ok laxOpens_facts laxQuery_some cutStep_facts cutFold_facts
    startChain_some bytes_beq bytes_beq_self stripO stripR readOpening_some readOpens_lax query_lax
    step_lax fold_lax view_strip)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src St)

/-! ## The lenient reader's openings -/

/-! ## One round, all rounds -/

section
variable (h : HId)

end

/-! ## The strict reader against the lenient one: what the strict reader reads, the lenient one
reads -/

section
variable (h : HId)

end

section
variable (h : HId)

end

theorem own_of_ok (S : _root_.Fmt.Spec) (hok : ok S = true) :
    ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n := by
  simp only [ok, Bool.and_eq_true, and_assoc] at hok
  obtain ⟨-, -, ho, -, -⟩ := hok
  intro r hr x hx
  have := List.all_eq_true.1 ho x (List.mem_flatMap.2 ⟨r, hr, hx⟩)
  unfold ownNo at this
  split at this
  · rename_i n hn
    exact ⟨n, hn⟩
  · cases this

end TypedOracleCompiler.Run.PQ
