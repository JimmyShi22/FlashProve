-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean: a form of Compile/Batch/Verifier.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/Verifier.lean, comments apart: definitions: `Body`,
`OneProtocolProof`, `OneProtocolProof.withPaths`, `actOf`, `RtC`, `takeRt`, `recomputeChain`, `checksOpt`, `checksB`, `reqCheck`,
`forestsB`, `rootAt`, `mkTr`, `afterB`, `reqPart`, `RootsOfChain.count`, `strictSB`, `proofHasStrictFormat`, `vT`, `vL`,
`vB`, `vTS`, `vLS`, `vBS`, `strictTrees`; only here: `forestsT`. Every other
declaration has that file's text.

The scope: wires with at most `maxRt` = 2 trees a component; at more this verifier rejects
everything, while the programs' byte format has no such cap (its limit is 2^16 trees a chain; no
shipped setting sends more than two roots in a round). A component without a tree has the empty list
of depths (the `has0`, `hasJ` of the head below are not here). In the request tree the leaf's input
is the slot value with the string `rsalt` behind it. If the chain does not join (a protocol with
local rounds only), `verifyB` never looks at the fields `rtreq`, `slot`, `path` and `rsalt`; the
strict format wants `slot` below 2^depthReq, and `path` and `rsalt` empty. Beside the things that
the head below names as left free by `verifyOneProtocol`: not tested, though no place that can be changed
freely (another `rsalt` is another leaf): if the chain joins, the length of `rsalt`; and nothing
inside `rsalt` is compared with the field `slot`. Compile/Batch/Star.lean, which the head below
names for the scheme and for `V`, has no file of that name in this folder. Test and Link are run as
`L.batT`, `L.batL`, with their own annotations, at the depths `W.depthReqT`, `W.depthReqL` (`vT`,
`vL`, `vTS`, `vLS`).

The rest of this head is the head of Compile/Batch/Verifier.lean, read with these differences; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Verifier.lean: the compiled verifier of one slot of a batch protocol.

One definition serves the protocols Test, Link and Batch (the fields `offline`, `link`, `onlineBatch` of `BatchProtocol`,
Iop/Batch.lean). A slot is one request's part of Batch. A round of Batch is shared if its challenge
is one for all slots, and local if each slot has its own. A protocol with one Fiat-Shamir chain is a
batch protocol with local rounds only.

The verifier is given the roots of the external strings, an instance and a proof string (`OneProtocolProof`). A
proof string holds a salt, roots, plain parts (what the prover messages send in the clear) and
openings. It also holds the request root, the slot number and a path in the request tree, the Merkle
tree over the slots of a batch; but for the strict-format check, these three are used only if there
is a joining round (the first shared round after the local ones).

The verifier recomputes the chain, which yields the challenges (`recomputeChain`). It checks the openings
under the roots. If the chain has passed the joining round, it checks the slot value (the answer of
g in that round) under the request root. Then it runs the decision of the slot's verifier, that of
the interactive protocol, on the opened symbols.

The format of a round's query, (F1) to (F5) of Compile/Batch/Oracles.lean, follows from the round's
kind, local or shared, and a phase (`Phase`, `actOf`). A protocol whose rounds do not come in the
order local (at least one), then perhaps shared, then perhaps local, is rejected (but not one
without rounds), so the soundness theorem (`bcsSoundBatchG`) does not need this order as a
hypothesis, but where `L.late = some n`, its hypothesis `L.Sound` asks that 0 < n and that the
rounds 0 to n of Batch exist and are local (`BatchInteractiveOracleProof.SndBL`, `RoundSplits.LocalTo`, Iop/Batch.lean);
other theorems assume the order (`RoundSplits.Fmt`, Iop/BatchFmt.lean).

  `verifyB`   checks each opening along its own path (`afterB`).
              (a) It ignores surplus roots and the length of the salt;
              (b) it does not check openings at positions that are not read: the decision is still
              run on their symbols, in a prover message only where the component has a root; where
              the decision is local (`InteractiveOracleProof.IsLocal`, Iop/InteractiveOracleProof.lean) and `WireE.OK` (Iop/Wire.lean)
              holds, `verifyB` ignores these openings;
              (c) it ignores without a joining round the fields rtreq, slot and path.
              Under the hypotheses of its statement (`Spec.bcsSoundBatchG`,
              Compile/Batch/SpecSoundG.lean), soundness (`bcsSoundBatchG`, Compile/Batch/Sound.lean)
              is proved for it.
  `verifyOneProtocol`  is the verifier that the scheme uses (Compile/Batch/Star.lean). After the chain it
              makes the strict-format check (`proofHasStrictFormat`, no query). Then (`checkPrunedOpenings`), in a tree that
              the wire record (parameters of the compiler, Iop/BatchWire.lean) marks as pruned
              (`pr0`, `prJ`, `pr`), it verifies all opened leaves together (Hash/Octopus.lean) and
              reads of their paths only the sibling digests that it cannot compute; elsewhere it
              follows each path. If the wire record is well-formed and `verifyOneProtocol` accepts a proof
              string with its queries answered from a trace (a list of queries with their answers),
              then `verifyB` accepts that string with other paths in its openings, with its queries
              answered from the same trace (`runsIn_verifyB_of_strict`,
              Compile/Batch/ForestSound.lean). Where a tree is marked, neither verifier accepts all
              that the other accepts.

Components that are not sent. A component of a prover message for which the query of its round has
no field (the shared one in a local round; a slot's in a shared round other than the joining round)
has no root. `verifyB` ignores what the proof string holds for it; `verifyOneProtocol` rejects an opening
there and ignores the plain part. The decision is run with the fixed symbol 0 at its positions and
the plain part of a fixed message. A sent component without a tree (`has0`, `hasJ` false) takes no
root, and its plain part is hashed as usual. A well-formed wire record gives it no oracle position;
if an ill-formed one gave it any, the symbol 0 is used there too, so the proof of soundness does not
use that condition on the wire record (its statement assumes `W.OKG` whole).

Notation: `lam`: a natural number: "Digests have `lam` bits"; `K`: a natural number: an answer of
`fb t` "is K hash blocks, from which the challenge is made, and a chaining value"; g: `OracleName.g t`, a
constructor of `OracleName`: "in the joining round (the first shared round after the local ones), the slot
value: the hash of a slot's chain that becomes its leaf in the request tree" (all three: the head of
Compile/Batch/Oracles.lean); V: `V` (Compile/Batch/Star.lean).

Limits. The tests of `proofHasStrictFormat` reach every position if the wire record is well-formed
(`WireRB.OKG`, Iop/BatchWire.lean; `WireE.OK`, Iop/Wire.lean), which the theorems that use them
assume. `verifyOneProtocol` leaves three things free. (i) An accepted proof string stays accepted under any
change of the plain part of a component that is not sent, and, without a joining round, of rtreq
(any digest) and slot (any number below 2^depthReq). (ii) The root of a component under which V
opens nothing is checked against nothing; it is a field of a query of its round: the Fiat-Shamir
query, or, for the slot's root in the joining round, the query to g. Its value is free, so it is
room for trying again, which the binding bound charges query by query. (iii) In a tree that is
marked as pruned, the digests of the paths that the joint verification does not use are free: where
two nodes on opened paths are siblings and, the left one first, neighbours in the list of their
level (`Octopus.up`, Hash/Octopus.lean), the digest of that level in the left one's path, and the
right one's path from that level upwards. Only their number is tested. In the format of
Compile/Batch/Pruned.lean they do not exist. That an accepted proof string cannot be changed into
another accepted one elsewhere is proved nowhere.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles
import Compile.Bcs
import Hash.Octopus

noncomputable section   -- Lean generates code for the definitions of this file that it can
-- compile; the marker tags only what it cannot. The marker says nothing of choice:
-- equality of oracle queries is decided classically only in the semantics of runs (Rom/OSpec.lean:
-- OSpec.decDom, Table.set), not by the verifier

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

abbrev TypedOracleComputation (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (α : Type) : Type := OComp (typedOracleFamily lam K L) α
abbrev Body (L : BatchProtocolWithLeafBody I X) : Type := L.Bd

/-! ## The argument string of one slot -/

/-- The argument string of one slot j. Its fields: a salt; the roots of the hash trees; the messages
that the verifier reads whole; for each position that is opened, in the slot's own messages
(`opens`) and in the strings from outside (`ext`), the symbol there with its salt and its path; and
what ties the slot to its batch: the root of the tree over the batch's requests, the slot's number,
the slot's path in that tree, and a string that stands behind the slot's value in that tree's leaf
(`rsalt`). -/
structure OneProtocolProof (lam : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) where
  salt : Bits
  roots : List (Dig lam)
  plains : Plains Q.loc.shape
  opens : (p : OPos Q.loc.shape) → Option (Opening lam (OSym Q.loc.shape p))
  ext : E.Pos → Option (Opening lam E.Sym)
  rtreq : Dig lam
  slot : ℕ
  path : List (Dig lam)
  /-- what stands behind the slot value in the input of the request tree's leaf: the prover's free
  choice. (In the programs' byte format that leaf is salted and holds its slot's number: a typing
  of a proof file lays both in here.) -/
  rsalt : Bits

/-- the openings f with their paths replaced by those of P -/
def reP {ι : Type} {σ : ι → Type}
    (f : (p : ι) → Option (Opening lam (σ p))) (P : ι → List (Dig lam)) :
    (p : ι) → Option (Opening lam (σ p)) :=
  fun p => (f p).map fun op => ⟨op.sym, op.salt, P p⟩

/-- the argument string π with other paths in its openings -/
def OneProtocolProof.withPaths {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (π : OneProtocolProof lam Q)
    (P1 : OPos Q.loc.shape → List (Dig lam)) (P2 : E.Pos → List (Dig lam)) : OneProtocolProof lam Q :=
  ⟨π.salt, π.roots, π.plains, reP π.opens P1, reP π.ext P2, π.rtreq, π.slot, π.path, π.rsalt⟩

/-! ## Phases -/

/-- how far the chain of a slot has come -/
inductive Phase (lam : ℕ)
  | first
  | loc (ρ : Bits)
  | shr (ρ0 : Bits) (c : Dig lam)
  | aft (ρ : Bits) (c : Dig lam)

/-- the slot value, once the chain has passed the joining round -/
def Phase.slotVal : Phase lam → Option (Dig lam)
  | .first => none
  | .loc _ => none
  | .shr _ c => some c
  | .aft _ c => some c

/-- what the verifier does in a round -/
inductive Act (lam : ℕ) (X : Type)
  /-- one Fiat-Shamir query with this header; it holds the root and the plain part of the slot's
  component (own = true) or of the shared one; the next phase is a function of the chaining value
  in the answer -/
  | one (h : Head lam X) (own : Bool) (next : Bits → Phase lam)
  /-- the joining round: a query to g with the slot's component, then (F4) with the shared one -/
  | join (ρ : Bits)

/-- Kind and phase fix the format. none: the verifier rejects. -/
def actOf (cms : List (Dig lam)) (x : Option X) (salt : Bits) :
    Kind → Phase lam → Option (Act lam X)
  | .lo, .first => some (.one (.f1 cms x salt) true .loc)
  | .lo, .loc ρ => some (.one (.f2 none ρ) true .loc)
  | .sh, .loc ρ => some (.join ρ)
  | .sh, .shr ρ0 c => some (.one (.f5 ρ0) false fun v => .shr v c)
  | .lo, .shr ρ0 c => some (.one (.f3 ρ0 (List.ofFn c)) true fun v => .aft v c)
  | .lo, .aft ρ c => some (.one (.f2 none ρ) true fun v => .aft v c)
  | .sh, .first => none
  | .sh, .aft _ _ => none

/-- what the chain yields for one component of one round: none: the component is not sent; some
[]: it is sent and has no tree (only its plain part is sent); some rts: it is sent, and rts are
the roots of its trees -/
abbrev RtC (lam : ℕ) : Type := Option (List (Dig lam))

/-- for each round: what the chain yields for the shared component, and for the slot's component -/
def RootsOfChain (lam : ℕ) : Shape → Type
  | [] => Unit
  | _ :: s => (RtC lam × RtC lam) × RootsOfChain lam s

/-! ## The chain -/

def askTypedOracle (o : OracleName) (q : domOf lam L o) : TypedOracleComputation lam K L (rngOf lam K o) :=
  OComp.ask (S := typedOracleFamily lam K L) o q

/-- The roots of a component with n trees, from the list of roots: the first n of the list. none: a
root is missing, or the component has more than maxRt trees. -/
def takeRt (n : ℕ) (rts : List (Dig lam)) : Option (List (Dig lam) × List (Dig lam)) :=
  if n ≤ maxRt ∧ n ≤ rts.length then some (rts.take n, rts.drop n) else none

/-- Recompute the chain of the slot: the verifier messages of the local transcript, the roots round
by round, and the last phase; none if the format of a round is not defined or a root is missing. x
is the whole instance (none: offline, link). Of it (F1) holds L.early x, and the query (F2) of the
round L.late holds x (Compile/Batch/Oracles.lean: lateInstancePart). Here also: none if a sent component has
more than maxRt trees (`takeRt`). -/
def recomputeChain (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ →
    Phase lam → List (Dig lam) → Plains s → TypedOracleComputation lam K L (Option (Rho s × RootsOfChain lam s × Phase lam))
  | [], _, _, _, _, ph, _, _ => pure (some ((), (), ph))
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map L.early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.depthJ.length rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h.withLate (lateInstancePart L i x), rt,
                  embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              let r ← recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2))
          | none => pure none
      | some (.one h false next) =>
          match takeRt w.depth0.length rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              let r ← recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2))
          | none => pure none
      | some (.join ρ) =>
          match takeRt w.depthJ.length rts with
          | some (rtj, rts1) =>
              match takeRt w.depth0.length rts1 with
              | some (rt0, rts') => do
                  let c ← askTypedOracle (L := L) (K := K) (OracleName.g t)
                    (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)
                  let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                    (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                      embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
                  let r ← recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                    (.shr (List.ofFn ans.2) c) rts' pls
                  pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2))
              | none => pure none
          | none => pure none
      | none => pure none

/-! ## Checks of openings -/

/-- one check of an opening in a tree over oracles: leaf input, number of the leaf, path, root, and
the depth of the tree, which the format fixes: the path must have exactly that length and the leaf
must exist (else a shallower tree is accepted and the extractor, which goes depth levels down, finds
nothing) -/
structure Check (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  inp : LeafIn L
  j : ℕ
  path : List (Dig lam)
  root : Dig lam
  depth : ℕ

/-- the check c with another path -/
def Check.withPath (c : Check lam L) (path : List (Dig lam)) : Check lam L :=
  ⟨c.inp, c.j, path, c.root, c.depth⟩

def Check.wellFormed (c : Check lam L) : Bool :=
  decide (c.path.length = c.depth) && decide (c.j < 2 ^ c.depth)

def hashTreeNode (a b : Dig lam) : TypedOracleComputation lam K L (Dig lam) :=
  askTypedOracle (L := L) (K := K) OracleName.node (List.ofFn a, List.ofFn b)
def rnodeV (a b : Dig lam) : TypedOracleComputation lam K L (Dig lam) :=
  askTypedOracle (L := L) (K := K) OracleName.rnode (List.ofFn a, List.ofFn b)

def runCheck (c : Check lam L) : TypedOracleComputation lam K L Bool := do
  let d ← askTypedOracle (L := L) (K := K) OracleName.leaf c.inp
  let r ← climbM hashTreeNode c.path c.j d
  pure (decide (r = c.root))

def runChecks : List (Check lam L) → TypedOracleComputation lam K L Bool
  | [] => pure true
  | c :: cs => do
      let a ← runCheck c
      let b ← runChecks cs
      pure (a && b)

/-- the checks that the read positions of one component of one round call for; none if an opening is
missing. Here it is called once for each tree of a component (`checksTrees`): so read: one tree of
one component. -/
def checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    List ℕ → Option (List (Check lam L))
  | [] => some []
  | j :: js =>
      match posAt j with
      | some p =>
          if isRead p then
            match f p, checksComp posAt depth emb rt isRead f js with
            | some op, some cs => some (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ :: cs)
            | _, _ => none
          else checksComp posAt depth emb rt isRead f js
      | none => checksComp posAt depth emb rt isRead f js

/-- The same tree by tree, from tree number k on: for each tree that has a depth and a root,
its depth, its root and its checks. Where the depths or the roots end (the component is not sent, or
has no further tree) nothing more is checked. -/
def checksTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ℕ → List ℕ → List (Dig lam) → Option (List (ℕ × Dig lam × List (Check lam L)))
  | k, d :: ds, c :: cs =>
      match checksComp (posAt k) d emb c isRead f (List.range (2 ^ d)),
        checksTrees posAt emb isRead f (k + 1) ds cs with
      | some a, some b => some ((d, c, a) :: b)
      | _, _ => none
  | _, _, _ => some []

/-- the checks of all trees of a component; it may have no root (it is not sent, or has no tree):
then nothing is checked -/
def checksOpt {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : Option (List (Check lam L)) :=
  (checksTrees posAt emb isRead f 0 depth rt).map fun l => l.flatMap fun z => z.2.2

def checksB :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) → RootsOfChain lam s →
    (OPos s → Bool) → ((p : OPos s) → Option (Opening lam (OSym s p))) → Option (List (Check lam L))
  | [], _, _, _, _, _, _ => some []
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f =>
      match checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksB s A W (fun p => emb (.inr p)) rts
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c => some (a ++ b ++ c)
      | _, _, _ => none

def checksExt {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    List E.Pos → Option (List (Check lam L))
  | [] => some []
  | p :: ps =>
      if isRead p then
        match g p, checksExt we emb cms isRead g ps with
        | some op, some cs =>
          some (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
                cms.getD (we.which p) default, we.depth⟩ :: cs)
        | _, _ => none
      else checksExt we emb cms isRead g ps

/-- The check in the tree over the batch's requests: the path has the tree's depth, the slot's
number is below 2 ^ depth, and climbing from the slot's leaf along the path gives the root `rtreq`.
The input of a leaf is the slot value c with the string rs behind it. -/
def reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam)
    (rs : Bits) : TypedOracleComputation lam K L Bool :=
  if path.length = depthReq ∧ slot < 2 ^ depthReq then do
    let d ← askTypedOracle (L := L) (K := K) OracleName.rleaf (List.ofFn c ++ rs)
    let r ← climbM rnodeV path slot d
    pure (decide (r = rtreq))
  else pure false

/-! ## The same checks, tree by tree: pruned sets of paths -/

/-- The checks in some trees of one depth ("a forest"; mostly one tree): each check with the number
of its tree; treeRoot t is the root of tree number t. Leaf j of tree number t has the number t *
2^depth + j (Hash/Octopus.lean). -/
structure Forest (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  depth : ℕ
  treeRoot : ℕ → Dig lam
  cs : List (ℕ × Check lam L)

/-- the numbers of the opened leaves -/
def Forest.idx (F : Forest lam L) : List ℕ := F.cs.map fun e => e.1 * 2 ^ F.depth + e.2.j
/-- how many sibling digests the joint verification of these leaves needs -/
def Forest.need (F : Forest lam L) : ℕ := Octopus.need F.depth F.idx
/-- these digests, read off the full paths of the checks -/
def Forest.reads (F : Forest lam L) : List (Dig lam) :=
  Octopus.reads F.depth (F.cs.map fun e => (e.1 * 2 ^ F.depth + e.2.j, e.2.path))

/-- all checks of a list of forests -/
def flatF (Fs : List (Forest lam L)) : List (Check lam L) := Fs.flatMap fun F => F.cs.map Prod.snd
def needF (Fs : List (Forest lam L)) : ℕ := (Fs.map Forest.need).sum
def readsF (Fs : List (Forest lam L)) : List (Dig lam) := Fs.flatMap Forest.reads

/-- the digests of the opened leaves -/
def leavesV : List (ℕ × Check lam L) → TypedOracleComputation lam K L (List (Dig lam))
  | [] => pure []
  | e :: es => do
      let d ← askTypedOracle (L := L) (K := K) OracleName.leaf e.2.inp
      let r ← leavesV es
      pure (d :: r)

/-- All checks of a forest at once, with the sibling digests s: the leaves are hashed; then level by
level two neighbours that are siblings are hashed together, and a node without its sibling is hashed
with the next digest of s (Hash/Octopus.lean: octC); every node that is left after depth levels must
be the root of its tree. The paths of the checks are not read. -/
def runForest (F : Forest lam L) (s : List (Dig lam)) : TypedOracleComputation lam K L Bool := do
  let v ← leavesV F.cs
  let out ← Octopus.octC hashTreeNode F.depth F.idx v s
  pure (((Octopus.upN F.depth F.idx).zip out).all fun m => decide (m.2 = F.treeRoot m.1))

/-- forest after forest; each takes from s as many digests as it needs -/
def runForests : List (Forest lam L) → List (Dig lam) → TypedOracleComputation lam K L Bool
  | [], _ => pure true
  | F :: Fs, s => do
      let a ← runForest F (s.take F.need)
      let b ← runForests Fs (s.drop F.need)
      pure (a && b)

/-- A forest as the format asks for it: whole, if its opened leaves are checked together (pr =
true); or split into one forest for each check. The verification of a forest with one leaf follows a
full path: it takes one digest at every level. -/
def Forest.split (pr : Bool) (F : Forest lam L) : List (Forest lam L) :=
  if pr then [F] else F.cs.map fun e => ⟨F.depth, F.treeRoot, [e]⟩

/-- Here: the forests of the trees of one component: each tree whole or cut, as the flag says -/
def forestsT (pr : Bool) (l : List (ℕ × Dig lam × List (Check lam L))) : List (Forest lam L) :=
  l.flatMap fun z => Forest.split pr ⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩

/-- the checks of checksB, tree by tree: for each round the trees over the shared component, then
the trees over the slot's; each whole or cut, as the flags pr0 and prJ of the wire say -/
def forestsB :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → OSym s p → Body L) → RootsOfChain lam s → (OPos s → Bool) →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Option (List (Forest lam L))
  | [], _, _, _, _, _, _ => some []
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f =>
      match checksTrees w.posAt0 (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []),
        checksTrees w.posAtJ (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []),
        forestsB s A W (fun p => emb (.inr p)) rts
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c => some (forestsT w.pr0 a ++ (forestsT w.prJ b ++ c))
      | _, _, _ => none

/-- the checks of checksExt, each with the number of its tree -/
def checksExtW {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    List E.Pos → Option (List (ℕ × Check lam L))
  | [] => some []
  | p :: ps =>
      if isRead p then
        match g p, checksExtW we emb cms isRead g ps with
        | some op, some cs =>
          some ((we.which p,
                ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
                  cms.getD (we.which p) default, we.depth⟩) :: cs)
        | _, _ => none
      else checksExtW we emb cms isRead g ps

/-- the trees over the external oracles: one forest, whole or split, as the flag pr of the wire
record says -/
def forestExt {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    Option (List (Forest lam L)) :=
  (checksExtW we emb cms isRead g we.all).map fun cs =>
    Forest.split we.pr ⟨we.depth, fun t => cms.getD t default, cs⟩

/-! ## The local transcript that the verifier builds -/

/-- is there a root for the tree of this position (its component is sent and has that tree) -/
def rootAt {r : Round} {a : RAnn r} (w : WireRB lam K r a) (rt : RtC lam × RtC lam) (p : r.Pos) :
    Bool :=
  if a.own p then ((rt.2.getD [])[w.tree p]?).isSome else ((rt.1.getD [])[w.tree p]?).isSome

/-- the plain part of a round: of each component what the proof string holds, if the component is
sent, and else that of the fixed message -/
def effPlain {r : Round} (a : RAnn r) (rt : RtC lam × RtC lam) (pl : r.Plain) : r.Plain :=
  a.plain.symm (if rt.1.isSome then (a.plain pl).1 else (a.plain r.dPlain).1,
    if rt.2.isSome then (a.plain pl).2 else (a.plain r.dPlain).2)

def effPlains : (s : Shape) → RoundSplits s → RootsOfChain lam s → Plains s → Plains s
  | [], _, _, _ => ()
  | _ :: s, (a, A), (rt, rts), (pl, pls) => (effPlain a rt pl, effPlains s A rts pls)

/-- a transcript from the argument string: opened symbols where there are any and the tree of their
position has a root, the fixed symbol 0 elsewhere -/
def mkTr : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → RootsOfChain lam s → Plains s → Rho s →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Tr s
  | [], _, _, _, _, _, _ => ()
  | _ :: s, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f =>
      ((w.pt.ofSyms fun p => match rootAt w rt p, f (.inl p) with
          | true, some op => op.sym
          | _, _ => w.pt.zero p, effPlain a rt pl), c, mkTr s A W rts pls ρ fun p => f (.inr p))

/-! ## The verifier -/

/-- the chain of a proof string, recomputed -/
def recomputeChainOfProof (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    TypedOracleComputation lam K L (Option (Rho Q.loc.shape × RootsOfChain lam Q.loc.shape × Phase lam)) :=
  recomputeChain t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots π.plains

/-- what the compiled verifier does after the chain has yielded the verifier messages ρ, the roots
round by round and the last phase: the checks of the openings, the check in the request tree if the
chain has joined, and the decision of the local verifier -/
def afterB {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : TypedOracleComputation lam K L Bool :=
  haveI := wq.decO
  haveI := wq.ext.dec
  match checksB Q.loc.shape Q.ann wq.sh embS rts
      (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains))) π.opens,
    checksExt wq.ext embE cms (fun p => decide (p ∈ Q.loc.extReads x ρ)) π.ext wq.ext.all with
  | some a, some b =>
      if (a ++ b).length ≤ wq.nOpen ∧
          (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then do
        let ok ← runChecks (a ++ b)
        let okr ← match ph.slotVal with
          | none => pure true
          | some c => reqCheck depthReq π.rtreq π.slot π.path c π.rsalt
        pure (ok && okr && Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
          (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens))
      else pure false
  | _, _ => pure false

/-- the forests of a proof string: the trees over the prover's messages, round by round, then
the trees over the external oracles; none if an opening is missing -/
def forestsOf {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embE : E.Sym → Body L) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) : Option (List (Forest lam L)) :=
  haveI := wq.decO
  haveI := wq.ext.dec
  match forestsB Q.loc.shape Q.ann wq.sh embS rts
      (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains))) π.opens,
    forestExt wq.ext embE cms (fun p => decide (p ∈ Q.loc.extReads x ρ)) π.ext with
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- the check in the request tree, if the chain has joined -/
def reqPart {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (depthReq : ℕ)
    (π : OneProtocolProof lam Q) (ph : Phase lam) : TypedOracleComputation lam K L Bool :=
  match ph.slotVal with
  | none => pure true
  | some c => reqCheck depthReq π.rtreq π.slot π.path c π.rsalt

/-- the end of the verifier, once the forests Fs and the sibling digests s are fixed -/
def afterF {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ)
    (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)
    (Fs : List (Forest lam L)) (s : List (Dig lam)) : TypedOracleComputation lam K L Bool :=
  (runForests Fs s).bind fun ok =>
  (reqPart depthReq π ph).bind fun okr =>
  pure (ok && okr && Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
    (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens))

/-- afterB with pruned Merkle paths. The same tests without a query as in afterB (no opening is
missing; at most nOpen openings; every path has the length of its tree's depth, every leaf number is
one of its tree). Then, in place of one path followed for each opening, one joint verification for
each forest, with the sibling digests that it needs read off the paths (Forest.reads). So of the
paths of the string only these digests are used; the others are checked against nothing. -/
def checkPrunedOpenings {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : TypedOracleComputation lam K L Bool :=
  match forestsOf Q wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatF Fs).length ≤ wq.nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then
        afterF Q wq depthReq x π ρ rts ph Fs (readsF Fs)
      else pure false
  | none => pure false

/-- The compiled verifier of one slot, with the external roots cms as inputs, without the
strict-format check: the chain, then afterB. embS, embP, embE say how symbols and plain parts are
written into queries. -/
def verifyB (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    TypedOracleComputation lam K L Bool :=
  (recomputeChainOfProof t Q wq embP xin cms x π).bind fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) => afterB Q wq embS embE depthReq cms x π ρ rts ph

/-! ## The strict format -/

/-- how many roots the chain has taken from the list -/
def RootsOfChain.count : (s : Shape) → RootsOfChain lam s → ℕ
  | [], _ => 0
  | _ :: s, (rt, rts) => (rt.1.getD []).length + (rt.2.getD []).length + RootsOfChain.count s rts

/-- one component of one round: at every position that is the position of a leaf of its tree, an
opening is present only if the component has a root and the position is read, and its salt has
exactly sMT bits. Here it is called once for each tree of a component (`strictTrees`): so read: one
tree of one component, and whether that tree has a root. -/
def strictComp (sMT : ℕ) {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : Bool :=
  (List.range (2 ^ depth)).all fun j => match posAt j with
    | none => true
    | some p => match f p with
      | none => true
      | some op => hasRoot && isRead p && decide (op.salt.length = sMT)

/-- Here: the same for all trees of one component -/
def strictTrees (sMT : ℕ) {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : Bool :=
  (List.range depth.length).all fun k =>
    strictComp sMT (posAt k) (depth.getD k 0) (rt[k]?).isSome isRead f

/-- the same for both components of all rounds -/
def strictSB (sMT : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → RootsOfChain lam s → (OPos s → Bool) →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Bool
  | [], _, _, _, _, _ => true
  | _ :: s, (_, A), (w, W), (rt, rts), isRead, f =>
      strictTrees sMT w.posAt0 w.depth0 (rt.1.getD [])
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      strictTrees sMT w.posAtJ w.depthJ (rt.2.getD [])
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      strictSB sMT s A W rts (fun p => isRead (.inr p)) (fun p => f (.inr p))

/-- The strict format of the argument string of a slot, given what the chain yields: the chain's
salt has exactly sFS bits; there are at most as many roots as the chain has taken; an opening stands
only where V reads, in a tree that has a root, with a salt of exactly sMT bits; the slot number is
below 2^depthReq; if the chain has not joined, the request path and rsalt are empty. A function of
the instance, the string and what the chain yields: no query. -/
def proofHasStrictFormat (sMT sFS : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : Bool :=
  haveI := wq.decO
  haveI := wq.ext.dec
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ RootsOfChain.count Q.loc.shape rts) &&
    strictSB sMT Q.loc.shape Q.ann wq.sh rts
      (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains))) π.opens &&
    strictExt sMT wq.ext (fun p => decide (p ∈ Q.loc.extReads x ρ)) π.ext &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
    (ph.slotVal.isSome || π.rsalt.isEmpty)

/-- The compiled verifier of one slot with the strict-format check and pruned Merkle paths: the
chain; the check; then checkPrunedOpenings. -/
def verifyOneProtocol (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    TypedOracleComputation lam K L Bool :=
  (recomputeChainOfProof t Q wq embP xin cms x π).bind fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) =>
      if proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph then
        checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph
      else pure false

/-! ## The three verifiers: vT, vL, vB without the strict format; vTS, vLS, vBS, which the scheme
runs, with it -/

variable (W : QueryLayout lam L)

def vT (cm : Dig lam) (π : OneProtocolProof lam L.batT) : TypedOracleComputation lam W.K L Bool :=
  verifyB Tag.test L.batT W.T W.embT id
    (fun _ => none) W.embE W.depthReqT [cm] () π
def vL (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) : TypedOracleComputation lam W.K L Bool :=
  verifyB Tag.link L.batL W.Lk W.embL id
    (fun _ => none) W.embE W.depthReqL [cm, cm'] () π
/-- the compiled verifier of a slot of Batch on (x, π) with the external root cm -/
def vB (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) : TypedOracleComputation lam W.K L Bool :=
  verifyB Tag.onl L.onlineBatch W.B W.embB id some
    W.embE W.depthReq [cm] x π

/-! the same three with the strict format; sMT is the length of the salt of a leaf, sFS that of the
salt of a chain -/

def vTS (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam L.batT) :
    TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Tag.test L.batT W.T
    W.embT id (fun _ => none)
    W.embE W.depthReqT [cm] () π
def vLS (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) :
    TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Tag.link L.batL W.Lk
    W.embL id (fun _ => none) W.embE
    W.depthReqL [cm, cm'] () π
def vBS (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) : TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Tag.onl L.onlineBatch W.B W.embB id some
    W.embE W.depthReq [cm] x π

end TypedOracleCompiler.Compile.Batch
