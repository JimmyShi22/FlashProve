-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQXLaws.lean.
TWO: CUT BY PROGRAM out of the library's Run/PlanQXLaws.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
okX_own, xWanted_len, psofX_local, wqX_okg.

Run/PlanQXLaws.lean: the protocol with two stored tables has a local verifier, and its wiring obeys
the library's laws wherever the wiring without stored tables does.

1. What the file contains. Five statements about Run/PlanQX.lean's protocol skeletonOverBothExternalStrings and wiring wqX,
for every C, list ds of rounds, depth a, list xs of openings of stored tables, and decision dec. The
proofs are in Run/PlanQXLawsProofs.lean.

2. What is checked when the file compiles.  Only the types.

3. Theorems stated.
   okX_own              okX ds a xs = true → every own tree that is opened has a number below 2^16
                        (from 2^16 on stand the keys of stored columns).
   weX_ok               The wiring of the two strings obeys the laws of an external wiring
                        (Iop/Wire.lean: WireE.OK). By the library's WireE.two_ok: no law reads the
                        flag for pruned sets or the depth.
   xWanted_len          If own trees have numbers below 2^16, the two strings together are read at
                        no more positions than the openings' counts add up to. Why the hypothesis:
                        xWanted tells a stored column by its key, and an own tree with a number from
                        2^16 on could be taken for one.
   psofX_local          (skeletonOverBothExternalStrings C ds a xs dec).up.loc.IsLocal (Iop/InteractiveOracleProof.lean): the decision depends
                        on the prover's oracles and on the two external strings only at the
                        positions read. This holds for every dec, by the form of the view and of the
                        tests everyOpeningHasItsDraws and symbolsCarryTheirPositions.
   wqX_okg              If own trees have numbers below 2^16 and (wqS C K chal ds dec₀).OKG, then
                        (wqX C K chal ds a xs dec).OKG. The laws of the own trees' wiring are those
                        of Run/PlanQS.lean's wiring, unchanged; own reads plus external reads are at
                        most nOpen ds plus the sum of the counts; depths.

4. What is not claimed.
   The laws of a whole wiring of the interface (QueryLayout.OKG), of which wqX_okg is the clause on Link:
   Run/PlanQXDoor.lean.
   That Run/PlanQS.lean's wiring obeys the laws at a given C: Run/PlanQSLaws.lean (wqS_okg),
   Run/PlanPull.lean (planPull_okg).
   NO STATEMENT ON SOUNDNESS.

Terms: lean/GLOSSARY.md.

-/
import Run.PlanQXLaws
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
import OnBytes.TypedOracleCompiler.Run.PlanPull
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Run.PlanQX
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open Run.Twin (RS PS)

namespace Spec

def okX_own : Prop :=
  ∀ (ds : List RD) (a : Nat) (xs : List XO),
    okX ds a xs = true → ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16

def xWanted_len : Prop :=
  ∀ (a : Nat) (ds : List RD) (xs : List XO) (Ds : List _root_.Fmt.Drawn),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) → (xWanted a ds xs Ds).length ≤ (xs.map (·.count)).sum

/-- THE VERIFIER IS LOCAL. -/
def psofX_local : Prop :=
  ∀ (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool),
    (skeletonOverBothExternalStrings C ds a xs dec).up.loc.IsLocal

/-- THE WIRING OBEYS THE LAWS. -/
def wqX_okg : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) (a : Nat)
      (xs : List XO) (dec dec₀ : View → Bool),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
    (wqS C K chal ds dec₀).OKG → (wqX C K chal ds a xs dec).OKG

end Spec
end TypedOracleCompiler.Run.PQ
