-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyWalk.lean: what the honest committer of the compiled scheme asks, oracle name by
oracle name, on every path, at any wire: rounds may have a search for a nonce.

This file is about the cost of making a key: upper bounds on the number of oracle queries of the
honest committer, where rounds may have proof of work.
Definitions and statements (the proofs: CompileK/HonestKeyWalkProofs.lean). Generic: any interface,
any wire: no hypothesis on it beside whatever the arguments hold as proofs (among them `WireRB.pt`,
Iop/BatchWire.lean: every round's oracle part is a string that is read symbol by symbol:
`Round.IsPoint`, Iop/Shape.lean). Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.

Why: the library's counts of the honest committer either ask that no round has a search
(CompileK/CountsHonest.lean) or are made for a passage to one oracle (an exit) that reads the first
block of an answer first (Compile/Batch/OneCallCostS.lean: weights at most that rule's; an oracle
with empty answers is not seen).
A scheme may have searches and the
plain exit (`schemeOverOneHashFunction`, Rom/Family.lean). And a statement on an honest key (`Spec.honestSoundBK`,
CompileK/HonestKeySound.lean) needs to know which oracles the honest committer asks, not only how
many queries it makes.

The form: u : OracleName → ℕ is a price for each oracle name. On every path of C(i), whatever the answers
and the coins, the prices of its queries add up to at most `hkCom W p u` (`CostBound`,
Rom/Cost.lean).

Main names:
  `hkSlot u t`, `hkShared u t Ns`: the analogues of `cSlotW`, `cSharedW`
    (Compile/Batch/OneCallCostR.lean) with the oracle names kept apart.
  `Spec.honestKey_cost`: the bound told above, for every price u.
  `Spec.honestKey_typed`: the typed count (`hkCom W p fun _ => 1`): a query counts 1, a long answer
    once.
  `Spec.honestKey_notOnl`: C(i) asks no query at the chain oracle of sessions, `OracleName.fb Tag.onl`
    (`OnlyQ`, `NotFb`: Compile/Batch/CompleteUnif.lean). Other heads call it the sessions'
    Fiat-Shamir oracle.
  `Spec.honestKey_strings`: over one oracle of λ > 0 bits, for every coding m, the committer of
    `schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))` asks at most `hkCom W p (blk W.K)` strings. A
    chain query, a failed try too, costs W.K + 1 of them: the plain exit asks for all blocks of
    every answer.
  `Spec.honestKey_sum`: the typed count is the library's sum (`cCBW`) at "a failed try 1, a chain
    query 1", so its closed forms (`cCBW_le`, Compile/Batch/OneCallCostClosed.lean) serve.

Limits: upper bounds on every path: the worst case over the oracle: every search runs to its cap. On
the path on which every try fails the committer does make that many tries: so no bound "on every
path" lies below (tries at the caps) · (price of a try). The usual number of tries is smaller by the
factor cap · 2^-bits.
No lower bound is proved. This file says nothing on the value of any number, nothing on the mean,
and nothing on the prover or the verifier. A component without a tree is charged a tree of its
depth. A query counts as one however long its string. This file does not say that the committer's
key is good.

Terms: lean/GLOSSARY.md: chain query, coding, committer, interface, link, proof of work, session,
slot, string (in the row of `Spec.honestKey_strings`), tries, typed query, wire.
-/
import Compile.Batch.OneCallCostR
import Compile.Batch.StarKE
import Compile.Batch.CompleteUnif
import Rom.Cost
import CompileK.GenWit

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (PhK)
open Compile.Batch.CompleteUnif (OnlyQ NotFb)
open Compile.Batch.OneCall (cCBW)

/-- A tree with 2^d leaves, at the prices u. -/
def hkTr (u : OracleName → ℕ) (d : ℕ) : ℕ := 2 ^ d * u .leaf + (2 ^ d - 1) * u .node

section Counts
variable {lam K : ℕ} (u : OracleName → ℕ) (t : Tag)

/-- One slot of an execution of the protocol with the tag t: in a local round its tree and all tries
of its chain query; in the joining round its tree, its query to g, its leaf of the request tree. -/
def hkSlot : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PhK → ℕ
  | [], _, _, _ => 0
  | _ :: s, (an, A), (w, W), ph =>
      match an.kind, ph with
      | .lo, ph => (hkTr u w.depthJ + triesOf w.grJ * u (.fb t)) + hkSlot s A W ph.afterLo
      | .sh, .loc => (hkTr u w.depthJ + u (.g t) + u .rleaf) + hkSlot s A W .shr
      | .sh, ph => hkSlot s A W ph

/-- The shared part, for Ns slots. -/
def hkShared (Ns : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PhK → ℕ
  | [], _, _, _ => 0
  | _ :: s, (an, A), (w, W), ph =>
      match an.kind, ph with
      | .lo, ph => hkShared Ns s A W ph.afterLo
      | .sh, .loc => ((Ns - 1) * u .rnode + hkTr u w.depth0 + triesOf w.gr0 * u (.fb t)) + hkShared Ns s A W .shr
      | .sh, .shr => (hkTr u w.depth0 + triesOf w.gr0 * u (.fb t)) + hkShared Ns s A W .shr
      | .sh, ph => hkShared Ns s A W ph

/-- One execution with one slot. -/
def hkProve1 {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) : ℕ :=
  hkShared u t 1 Q.loc.shape Q.ann wq.sh .first + hkSlot u t Q.loc.shape Q.ann wq.sh .first

end Counts

/-- The honest committer, at the prices u: the root's tree and its test; M + 1 further trees, each
with its link. -/
def hkCom {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (u : OracleName → ℕ) : ℕ :=
  hkTr u W.depth + hkProve1 u .test W.T + (p.M + 1) * (hkTr u W.depth + hkProve1 u .link W.Lk)

namespace Spec

/-- States, name by name: on every path the prices of the honest committer's queries add up to at
most `hkCom W p u`. -/
def honestKey_cost : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L)
      (p : Params) (u : OracleName → ℕ) (i : I),
    (C W WP p i).CostBound u (hkCom W p u)

/-- The typed count. -/
def honestKey_typed : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I),
    (C W WP p i).QueryBound (hkCom W p fun _ => 1)

/-- States: the honest committer asks no query at the chain oracle of sessions. -/
def honestKey_notOnl : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I), OnlyQ (S := spec lam W.K L) (NotFb Tag.onl) (C W WP p i)

/-- In strings, over one oracle, for every coding. (not all hypotheses are named here: see the
statement below) -/
def honestKey_strings : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Wn : Type)
      (m : OracleCoding (spec lam W.K L) lam) (i : I),
    0 < lam → ((schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))).C i).QueryBound (hkCom W p (blk W.K))

/-- States: the typed count is the library's sum at "a failed try 1, a chain query 1". -/
def honestKey_sum : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p : Params),
    hkCom W p (fun _ => 1) = cCBW W p 1 (fun _ _ => 1)

end Spec
end Compile.Batch
