-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIs.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIs.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY: rtSL,
pi_chain.

Run/PageIs.lean: the compiled verifier behind the lenient reader, compared with the format's own
strict verifier. DEFINITIONS AND STATEMENTS ONLY.

Two verifiers for a proof file are compared, for every description S of a file format within the
limits of the generic construction, every choice of challenge types that fits (the parameter C : CK:
for each round the type of the verifier's message, and the map from such a message to the format's
record of what was drawn), every decision dec, and every oracle O on byte strings with answers of 32
bytes (h := Fmt.HO O is the format's hash function built from O).
   laxV O S C K chal dec file. The lenient reader at h, then the evaluable form of the compiled
   verifier (verifyP, Run/ThinDefs.lean; proved equal to the run of Compile.Batch.verifyOneProtocol:
   thin_verify, Run/ThinTie.lean) at the typed oracle functions that O induces (Run/CodingFn.lean:
   famOf O (PDS ..)), at the data made from S, that choice and dec (Run/PlanQS.lean). The lenient
   reader (laxWhole, Run/ParseLax.lean; "lax" in names) only cuts the file into its parts. It still
   recomputes the hash chain, because the drawn positions say how long the parts are; it tests no
   proof of work, walks no path and compares no root. Behind it the compiled verifier makes these
   checks itself.
   Fmt.verifyW (m := Id) h S (fun _ => dec) () file (Fmt/M1View.lean). The format's side: the strict
   reader of Fmt/Rules8.lean (form, spellings, proof of work, listed positions, every opening
   against its root, one value at a vertex under one root), then dec on what was read. It is our
   rendering of the verifier that the format page (FORMAT.md, which comes with the programs)
   prescribes.

THIS FILE PROVES NOTHING. Its statements were written first, as a plan of what was expected to hold,
cut into parts that were then proved separately. All parts and all four main statements are proved,
as stated here:
   pi_typed: Run/PageIsTopProofs.lean. pi_chain: Run/PageIsChain.lean. pi_facts, pi_strict1:
   Run/PageIsReaders.lean. pi_after: Run/PageIsAfter.lean. pi_strict2: Run/PageIsStrict2.lean.
   pi_formula, pi_half, pi_kits: Run/PageIsProofs.lean, where PiFit is also shown to hold at the
   format's oracle at both choices of challenge types in use. pi_core (F2):
   Run/PageIsCoreProofs.lean.
   What follows for the run functions that tests (#guard) evaluate: Run/PageIsRun.lean (over typed
   oracle functions), Run/StrictDom.lean (Fmt.formatHash for Fmt.HO Fmt.oracle on the strict side),
   Run/PageIsCore.lean, Run/PageIsOne.lean [not in this library] and Run/PageIsCoreOne.lean
   [not in this library] (over a single oracle, and the run of the tree of queries).

Sources. Two editions of the format page are compared here, neither the one that ships; this file
follows the second. By a comparison by program of every rule's text in these two editions, of the
rules that the middle term below renders these differ: the leaf's label (R2.1, R7.3, R7.4: through
the leaves' hash); the record of vertices (R7.14); as conditions on the public description: a salt's
length (R7.3), sizes (R2.7), a tree's depth (R7.16), which are clauses of Fmt.Spec.ok under the
names ok_salt, ok_small, ok_depth (Fmt/Rules8Ok.lean); kind 2 with exactly one element and kind 4
with at least one position (R6.2, R6.10), conditions on an entry: whether Entry.fits (ok_fits) tests
both has not been looked up for this head; R4.6 differs for stored tables alone, which the limits of
the generic construction shut out; R7.7 in words alone. The same in these two editions: R4.4, R4.5,
R5.2, R5.4, R5.5, R6.1, R6.6, R6.11, R7.9, R7.15, R8.8. By a comparison of the same kind with a
third edition (also not the one that ships; not held against the page that ships): none of these
eleven differs there; of the rules named above as differing, R7.4, R7.14 and R4.6 (for stored
tables) differ there from the second edition. R7.14 is treated below.



1. What the file contains.
   The middle term: what the lenient reader hands out, o, and three tests on it that hash.
      rowBs, nextOf        A round's blocks and the chain value behind it, made again from o's
                           message and nonce.
      passL                Every round's proof-of-work test.
      rootOf, rootsAll     Every opening walks to the root that was sent.
      TraceL, LaxFacts     What o is: each round's items are its message read; what was drawn is the
                           format's draw on the round's blocks; each opening stands at the list of
                           the draw, under the root sent, in the right shape.
      rootsDiffer          A test that can be run: the lenient reader is run on the file (at the
                           hash function h), and the roots that it finds are compared as bytes. It
                           is true if they are pairwise different, and also where the reader reads
                           nothing.
      KitFits              The view that the choice of challenge types gives of the wiring's message
                           is the format's draw on the first blocks. This is true of both choices in
                           use: challenges as sampled values (ck: a round's verifier message is the
                           field elements and positions that the format draws; the wiring applies
                           the sampling rule) and challenges as hash blocks (ckP: the message is the
                           round's 256-bit blocks themselves; reads and decision apply the sampling
                           rule) (Run/PlanDraws.lean: planDraws_tie; Run/PlanPull.lean:
                           planPull_view).
   VO, laxV, rtSL, PiFit and the statements listed under 3.

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. None is proved here; the statements (Run.PQ.Spec.pi_*) are these.
   The parts:
      pi_facts     laxWhole h S b = some o → LaxFacts h S o.
      pi_strict1   wholeChain h S b = some o' → there is o with laxWhole h S b = some o, the same
                   view, passL, rootsAll.
      pi_strict2   laxWhole h S b = some o, passL, rootsAll, rootsDiffer → there is o' with
                   wholeChain h S b = some o' and the same view.
      pi_chain     On the argument string made from the reader's output the verifier's chain yields:
                   what was drawn is o's; its test bits pass iff passL; each round's root is o's; it
                   has not joined.
      pi_after     Given what the chain yields: the strict format holds, and what follows the chain
                   is rootsAll ∧ (the test bits pass) ∧ dec on o's view.
      pi_typed     The step that types the reader's output does not refuse: LaxFacts, the limits →
                   toBPrfP gives a string, its list the one digest.
   The main statements. pi_formula, pi_half, pi_core and pi_kits each have the hypothesis PiFit O S
   C K chal (for pi_kits: at both choices), which the lines below leave out: O's answers have 32
   bytes; S lies within the limits (PQ.ok); KitFits; every round's blocks number at most K.
      pi_formula   laxV .. file = (if laxWhole gives nothing: false; if it gives o: passL ∧ rootsAll
                   ∧ dec (viewOf S.firstTree o)).
      pi_half      (F1) Fmt.verifyW h S .. file = true → laxV .. file = true. What the format's
                   verifier accepts, the compiled verifier behind the lenient reader accepts.
      pi_core      (F2) rootsDiffer → laxV .. file = Fmt.verifyW h S .. file. Where the roots that
                   the file sends differ, the two give one verdict.
      pi_kits      Two choices of challenge types that both fit give one verdict on every file: laxV
                   O S C K chal dec file = laxV O S C' K' chal' dec file. (pi_formula's right side
                   does not name the choice.)

   Two hypotheses for pi_strict2 and pi_core: (1) is a clause of the limits, which both assume;
   (2) is a premise of both.
      (1) saltLenOK S.plan.salt. Without this hypothesis the two statements are false: the format
        page's bounds on the length of a leaf's salt are then tested inside the strict reader of an
        opening alone, so that at a plan which breaks them the strict side refuses every file and
        the other side need not. The test is a clause of Fmt.Spec.ok, and so of the limits.


      (2) rootsDiffer. The strict reader's record of the vertices met is keyed by the root's 32
        bytes (R7.14 in the edition named under "Why"). In several other editions of the format
        page, none the one that ships, R7.14 speaks of a tree as it was sent (the first of them is
        known here by a restatement, the others by reading the page's own list of changes): with the
        record kept under the start of a tree's leaves and the number in their labels it never
        refuses within the limits, and the hypothesis is not needed. (That Fmt/Rules8.lean has the
        page's rule on the record in general is not said.)

   Why rootsDiffer. By R7.14 at a further edition of the page, the strict reader keeps one
   record of the vertices met for every root, keyed by the root's 32 bytes, and refuses a second
   value at a vertex. Within the limits each tree is opened at most once; but two trees may be sent
   with the same bytes as roots, and then the record joins them, while the compiled verifier walks
   each tree by itself. A file on which the two sides give different verdicts holds two openings
   that end in one root and differ at a vertex: a collision of the vertices' hash, which an
   arbitrary oracle may have (this follows the rule's letter; it is not stated in Lean). A RECORD
   CAN ONLY ADD REFUSALS. SO THE DIRECTION (F1), pi_half, NEEDS NO SUCH HYPOTHESIS, AND NEITHER DO
   pi_formula, pi_kits AND THE OTHER PARTS; pi_strict2 AND pi_core (F2) ALONE HAVE IT. The test asks
   more than the page's own condition, which speaks of the roots that are read: it asks that all
   roots that the file sends differ, which is simple to run.

   TRIED, NOT PROVED (one evaluation, not part of these files, at Fmt.formatHash).
   At the description of the first toy at the programs' own parameters, tiny parameters
   (Fmt/M1PlanKnownT.lean), on 47 files of another form of the set of Fmt/M1FilesT.lean:
   the run function runLaxS (with challenges as sampled values; challenges as hash blocks
   were not tried) says "accepted", the right side of pi_formula is true, and Fmt.verify is true on
   the same files (the honest one alone); rootsDiffer holds on all 47; each of the three tests is
   the only one to fail on some file (passL on the three files cut anew behind a failing nonce;
   rootsAll on the two files named alt-05, alt-06; the decision on 30).

4. What is not claimed.
   NO STATEMENT ON SOUNDNESS FOLLOWS.
   OF A TREE THAT THE CHAIN SENDS AND NEVER OPENS (the limits allow it) these theorems know 32 bytes
   that enter the hash chain, and nothing of what was committed under them: in the protocol its
   oracle is one word that nobody reads. That a later chain opens that root is outside them.
   Fmt.formatHash in the place of Fmt.HO O is the matter of other files (the hash function's domain, bounds
   on sizes: Run/LaxDom.lean, Run/StrictDom.lean).
   That Fmt/Rules8.lean renders the format page is not a theorem. One place that is not settled: by
   R2.7 a verifier refuses beyond R2.3's bounds on sizes (Run/LaxDom.lean's smallB is that test for
   the lenient reader's calls). Sizes are a clause of Fmt.Spec.ok (ok_small, see "Sources"); whether
   that clause is all of R2.7 has not been looked up for this head.



Terms: lean/GLOSSARY.md.

-/
import Run.PageIs
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
import OnBytes.TypedOracleCompiler.Run.PlanQS
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
import Run.WalkTieProofs
import Run.LaxDom
import OnBytes.TypedOracleCompiler.Run.ParseLaws
import Fmt.M1View

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (rowBs nextOf passL rootOf rootsAll OpenFacts TraceL LaxFacts
    KitFits rootsDiffer)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-! ## The middle term -/

section
variable (h : HId)

end

/-! ## The verifier's side -/

section
variable (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)

/-- what the chain yields for the roots, round by round: TWO: ALL the roots of a round's items, in
their order (the library: the FIRST, "right within the road's limits (PQ.ok: at most one root a
round)") -/
def rtSL : (ds : List RD) → List RoundOut → RootsOfChain 256 (uL C ds)
  | [], _ => ()
  | _ :: ds, [] => ((none, some []), rtSL ds [])
  | _ :: ds, ro :: ros =>
    ((none, some ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)), rtSL ds ros)

end

namespace Spec

def pi_chain : Prop :=
  ∀ (Bd : Type) (leaf : Bd → Option (Nat × Nat × ByteArray))
      (O : ByteArray → ByteArray), (∀ s, (O s).size = 32) →
    ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
        (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool),
      ok S = true → KitFits S.plan.field C K chal →
      (∀ r ∈ S.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      ∀ (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S))),
        LaxFacts (_root_.Fmt.HO O) S o → o.run = some run →
        plainsSL C (rds S) o.rounds.toList = some pl →
        ∃ (ρ : Rho (uL C (rds S))) (v : Bits),
          chainP (fun _ => LbS Bd C (rds S) dec) (famOf O (PDS Bd S C dec leaf) (K + 1)) id none
              .onl
              [bytesToDig o.pd] (some () : Option Unit) (bytesToBits run) (fun _ => false)
              (SOf C (rds S)) (allLo (SOf C (rds S))) (wqS C K chal (rds S) dec).sh
              (embPS Bd C (rds S) dec) 0 .first ((rootsB o).map bytesToDig) ((), pl) =
            some ((default, ρ), ((none, some []), rtSL C (rds S) o.rounds.toList), .loc v) ∧
          drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn) ∧
          passSL C (rds S) ρ = passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩

end Spec
end TypedOracleCompiler.Run.PQ
