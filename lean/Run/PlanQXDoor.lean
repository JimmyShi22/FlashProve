-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXDoor.lean: under the hypotheses below, the entry file's protocol meets formal side
conditions of the library's compilation theorems (the record `FormX`); the two conditions on
soundness hold under them too; but for one clause, the last of `low` with its event Bad, they are
empty here (below, "What is not claimed").

What this file contains. The protocol that checks an entry file reads two stored tables as external
oracles. In the library's terms it is the Link protocol of an interface (Run/PlanQX.lean: `LkX`).
The library's compilation theorems require a list of conditions of an interface and of its wiring,
that is, of the data that say how deep the trees are, where a position stands among a tree's leaves,
and how blocks of a hash answer give a verifier message. This file states that the ten conditions of
`FormX`, which concern the wiring, the format and the form of the interface, hold here, under four
hypotheses:
   (1) Link's own wiring wL obeys the laws of a wiring (`wL.OKG`);
   (2) its external wire is `weX a`;
   (3) its bound on depths is at least a (`a ≤ wL.maxDepth`);
   (4) the trees whose roots the prover sends in the proof itself (the chain's own trees, as opposed
       to the two stored tables' trees) have numbers below 2^16 (exactly: every number in a round's
       list `opens` is below 2^16).
It does so for every choice of challenge types C (for each round the type of the verifier's message,
and the map from such a message to the format's record of what was drawn; `CK` in the code), list ds
of rounds, tree depth a, list xs of openings of the stored tables, and decision function dec. (The
format's record of what was drawn: `Fmt.Drawn`, Fmt/Rules6Round.lean: what a round draws: elements,
positions as drawn, matrix entries, the seal's digest.) The proofs are in Run/PlanQXDoorProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

   `Lu C ds a xs dec`: the interface that Run/PlanQXRun.lean's run function `runEntry` uses (its
     `D.L dec`, by definition). The index type is Unit, the encoding sends a position to (the
     position, no word), and the decoder accepts every string. These three are placeholders.
   `WkX K wL`: the whole wiring of `Lu`: Test and Batch have no rounds; the external trees have
     depth a; a batch has one proof in it (one slot).
   `FormX q0 q1 L W`: the ten conditions that do not mention a language: the laws of the whole
     wiring (okg); decoding undoes encoding, and the honest sides' external strings are encodings of
     the index (wired); Link reads at most q0 positions of the first string and at most q1 of the
     second, Test and Batch read none, and the record's clause on hiding of the encoding is asked
     for 0 positions, where it is trivial (reads); the three verifiers depend on the oracles only at
     the positions read (localT, localL, localB); the batch's annotation is coherent (cohB); the
     three shapes are read symbol by symbol (pointT, pointL, pointB).
   `MetX q0 q1 L W`: `FormX`, together with two conditions at the language that contains everything:
     sound (`L.Sound`) and low (`Compile.Batch.BcsAt`, the conclusion of the library's theorem
     `bcsSoundBatchG`).

What is checked when it compiles. Only the types. There are no guards.

Theorems stated.
   `Spec.xSide_len`: if the chain's own trees have numbers below 2^16, then one string is read at no
     more positions than the counts of its own openings add up to.
   `Spec.okgWkX`: wL.OKG → wL.ext = weX a → a ≤ wL.maxDepth → (WkX K wL).OKG.
   `Spec.formX`: if the chain's own trees have numbers below 2^16 and the three hypotheses of
     `okgWkX` hold, then FormX (cntOf false xs) (cntOf true xs) (Lu ..) (WkX K wL).
   `Spec.metX`: under the same hypotheses, `MetX` at the same numbers.

Why there are two records. If an encoding and a decoder with content replace the placeholders,
`FormX` is the part that carries over: wired and reads mention the encoding and have to be looked at
again, the other eight conditions do not see it. The conditions sound and low are then statements
with content, which this file does not prove.

Notation:
  `L.Reads b qT qpar qch qon`: the numbers in its fields `hidE`, `cntT`, `cntLp`, `cntLc`, `cntB`,
    in order (Iop/Batch.lean);
  the last 0 of `L.Sound All 0`: `εs`, the second argument of `Err.Below` in its three fields
    (`BatchProtocol.Sound`, Iop/Batch.lean);
  the last 0 of `BcsAt W All 0`: its argument `εs` (Compile/Batch/SpecSoundG.lean);
  `All`: the relation `fun _ _ => True` (Run/M1Door.lean);
  `cntOf`: the sum of the counts of the openings of one string;
  `K`: the number of blocks from which a verifier message is made (`WireRB.chal`,
    Iop/BatchWire.lean).

What is not claimed. No statement on soundness follows from this file. The conditions sound and low
hold here under the hypotheses of `Spec.metX`. Of them one clause has content: the last of `low`,
with its event Bad (`Compile.Batch.BcsAt`, Compile/Batch/SpecSoundG.lean; `extEnc`, `Announced`,
Compile/Batch/Events.lean). Beyond it they are empty. Link's language is "the first string does not
decode, or the second decodes to the same index as the first". With the placeholder decoder every
string decodes to the one index, so no statement lies outside the language, nothing is asked of any
round, and the library's clause on an accepted Link string says nothing. What is missing is the
content: an encoding and a decoder that belong to a code (a decoder within a named radius), and
round-by-round soundness of Link for that language. For the protocol of this file they are stated
nowhere in Run/ or Fmt/. The library has a link protocol with statements of that kind
(Cb/Ld/LdLink.lean); nothing in Run/ or Fmt/ connects the two. Completeness is not shown, and cannot
be: the honest sides of the interface are placeholders. Hiding (the field `hidden` of `BatchProtocol.Props`,
Iop/Batch.lean) is not shown of this interface, in this file or elsewhere in Run/. `GrFitB W Ryes`
(Compile/Batch/SpecFit.lean), `L.onlineBatch.ann.Fmt` (Iop/BatchFmt.lean) and `WireBP.OK`
(Iop/BatchWireP.lean), which the library's statement on completeness `completeBatchUGr`
(Compile/Batch/SpecUGr.lean) also asks, among other premises, are not stated here. Nothing is said
about bytes or about a run, nor that a given wL obeys the laws (for that see Run/PlanQXLaws.lean:
`wqX_okg`).

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQXLaws
import Run.M1Door

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.M1Door (All)

/-- The interface of the run function `runEntry` (Run/PlanQXRun.lean): Link is the protocol; index,
encoding and decoder are placeholders. -/
abbrev Lu (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) : BatchProtocol Unit Unit :=
  LkX (I := Unit) (RI := Unit) C ds a xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())

/-- the wiring of a protocol without a round on one string -/
def wq1 (K a : Nat) : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (pT1 (2 ^ a))) :=
  ⟨(), WireE.one (2 ^ a) SgX (0, []), inferInstanceAs (DecidableEq Empty), 0, a⟩

/-- The whole wiring. -/
def WkX {C : CK} {ds : List RD} {a : Nat} {xs : List XO} {dec : View → Bool} (K : Nat)
    (wL : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (Lu C ds a xs dec).link)) :
    QueryLayout 256 (Lu C ds a xs dec) where
  K := K
  T := wq1 K a
  Lk := wL
  B := wq1 K a
  depth := a
  depthReq := 0

/-- The conditions that look at no language; `Spec.formX` states when they are met. -/
structure FormX (q0 q1 : Nat) (L : BatchProtocol Unit Unit) (W : QueryLayout 256 L) : Prop where
  okg    : W.OKG
  wired  : L.Wired
  reads  : L.Reads 0 0 q0 q1 0
  localT : L.offline.IsLocal
  localL : L.link.IsLocal
  localB : L.onlineBatch.loc.IsLocal
  cohB   : L.onlineBatch.ann.Coherent
  pointT : Nonempty L.offline.shape.IsPoint
  pointL : Nonempty L.link.shape.IsPoint
  pointB : Nonempty L.onlineBatch.loc.shape.IsPoint

/-- `FormX` with the two conditions at the language "everything". At `Lu` they are true under the
hypotheses of `Spec.metX`; there one clause of them has content, the last of `low`, with its event
Bad, and beyond it they are empty (the head, "What is not claimed"). -/
structure MetX (q0 q1 : Nat) (L : BatchProtocol Unit Unit) (W : QueryLayout 256 L) : Prop where
  form   : FormX q0 q1 L W
  sound  : L.Sound All 0
  low    : BcsAt W All 0

/-- the sum of the counts of the openings of one string -/
def cntOf (b : Bool) (xs : List XO) : Nat := ((xs.filter fun o => o.which == b).map (·.count)).sum

namespace Spec

def xSide_len : Prop :=
  ∀ (a : Nat) (ds : List RD) (xs : List XO) (Ds : List _root_.Fmt.Drawn) (b : Bool),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
    ((xWanted a ds xs Ds).filter fun wx => wx.1 == b).length ≤ cntOf b xs

def okgWkX : Prop :=
  ∀ (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) (K : Nat)
      (wL : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (Lu C ds a xs dec).link)),
    wL.OKG → wL.ext = weX a → a ≤ wL.maxDepth → (WkX K wL).OKG

/-- States that, under the hypotheses below, the ten conditions of `FormX` are met. -/
def formX : Prop :=
  ∀ (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) (K : Nat)
      (wL : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (Lu C ds a xs dec).link)),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) → wL.OKG → wL.ext = weX a → a ≤ wL.maxDepth →
    FormX (cntOf false xs) (cntOf true xs) (Lu C ds a xs dec) (WkX K wL)

def metX : Prop :=
  ∀ (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) (K : Nat)
      (wL : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (Lu C ds a xs dec).link)),
    (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) → wL.OKG → wL.ext = weX a → a ≤ wL.maxDepth →
    MetX (cntOf false xs) (cntOf true xs) (Lu C ds a xs dec) (WkX K wL)

end Spec
end Run.PQ
