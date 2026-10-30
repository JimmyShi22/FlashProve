-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Pruned.lean: proof strings with pruned Merkle paths.

The file has definitions; the lemmas are in Compile/Batch/PrunedFacts.lean and the schemes in
Compile/Batch/StarO.lean. A proof string (`OneProtocolProof`, Compile/Batch/Verifier.lean; words of this
library: lean/GLOSSARY.md) holds a full Merkle path for every opening, of which the verifier
`verifyOneProtocol` uses only the sibling digests that its verification needs (Hash/Octopus.lean). Here these
digests are in one list, and all others are dropped.

  `BPrfO`     The pruned proof string: the fields of `OneProtocolProof`, with openings without paths (`OpenO`),
              and the list `sibs`.
  `pruneO`    The map from `OneProtocolProof` to `BPrfO` that the honest prover applies. It depends only on the
              proof string and the wire record, on no oracle and no challenge.
  `verifyBO`  The verifier: the Fiat-Shamir chain and the strict-format check as in `verifyOneProtocol`. Then
              it tests without a query that no opening is missing, that there are at most `nOpen`,
              that every leaf number belongs to its tree, and that `sibs` has exactly as many
              digests as the verification consumes (`usedUp`). Then it verifies the trees, taking
              the digests from `sibs` in order.
  `fillO`     Back to `OneProtocolProof`, for the analysis only: full paths with the digests of `sibs` where the
              verification reads, and zeros elsewhere (conditions: the docstring of `refill`).

The wire record says which trees are pruned (`pr0`, `prJ` for the two trees of a round,
Iop/BatchWire.lean; `pr` for the trees over the external strings, Iop/Wire.lean). In a tree that is
not pruned each opening takes a full path from `sibs`, so with no tree pruned `sibs` is the
concatenation of the full paths. The digests are ordered group by group. A group is a pruned tree
over a prover message, or all trees over the external strings together if they are pruned, or one
opening of a tree that is not pruned (its full path). The groups come in the verifier's order: for
each round the tree of the shared component, then that of the slot's, and the external trees last.
In a group the digests go level by level from the leaves up, and in a level in the order of the
opened leaves: ascending in a tree over a prover message, in the order of the wire record's list
`all` in the external trees.

Notation:
  the fields of `BPrfO` are those of `OneProtocolProof` (Compile/Batch/Verifier.lean): `roots`; `plains`, the
    plain parts; `salt`; `opens` and `ext`, the openings in the prover's oracles and in the external
    strings; `rtreq`, the request root; `slot`; `path`; and `sibs`, the sibling digests for all
    trees
  `sMT`, `sFS`: sMT is the length of the salt of a leaf, sFS that of the salt of a chain; `cms`:
    List (Dig lam), the external roots (Compile/Batch/Verifier.lean)
  `embS`, `embP`, `embE` say how symbols and plain parts are written into queries (`verifyB`, the
    same file); `xin`: Y → Option X; at the three verifiers: the last section
  `ρ`, `rts`, `ph`: what the chain `recomputeChainOfProof` returns: Rho Q.loc.shape, RootsOfChain lam Q.loc.shape, Phase lam
    (the same file)

Limits: differences from the implementation. The two external trees of Link (under the root cm of
the key and under a copy's root cm') are verified as one group, so when they are pruned their
digests alternate level by level; the implementation writes one set after the other. Not modelled: a
truncated top layer (for some trees the implementation sends all 2^c nodes of one level and short
paths up to it), and repeated positions (here a position is opened once).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).

Two lemmas stand here all the same, after `planTrees`: `planTrees_one`, `planTrees_nil`.
-/
import Compile.Batch.Verifier

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## The verifier, on a proof string whose openings' paths it does not read and a list of sibling
digests -/

/-- "Used up exactly": the list of sibling digests has exactly as many digests as the verification
consumes. -/
def usedUp (n : ℕ) (s : List (Dig lam)) : Prop := s.length = n

instance (n : ℕ) (s : List (Dig lam)) : Decidable (usedUp n s) := by
  unfold usedUp
  infer_instance

/-- checkPrunedOpenings with the sibling digests given, in the place of reading them off the paths. The paths in
π's openings are not read. -/
def afterBC {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : TypedOracleComputation lam K L Bool :=
  match forestsOf Q wq embS embE cms x π ρ rts with
  | some Fs =>
      if ((flatF Fs).length ≤ wq.nOpen ∧
            (flatF Fs).all
              (fun c => decide (c.j < 2 ^ c.depth) && decide (c.depth ≤ wq.maxDepth))) ∧
          usedUp (needF Fs) s then
        afterF Q wq depthReq x π ρ rts ph Fs s
      else pure false
  | none => pure false

/-- the chain; the strict-format check; then afterBC -/
def verifyBC (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Q) (s : List (Dig lam)) : TypedOracleComputation lam K L Bool :=
  (recomputeChainOfProof t Q wq embP xin cms x π).bind fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) =>
      if proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph then
        afterBC Q wq embS embE depthReq cms x π s ρ rts ph
      else pure false

/-! ## The proof string -/

/-- an opened position: symbol and salt -/
structure OpenO (σ : Type) where
  sym : σ
  salt : Bits

/-- The proof string of one slot with pruned Merkle paths. -/
structure BPrfO (lam : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) where
  salt : Bits
  roots : List (Dig lam)
  plains : Plains Q.loc.shape
  opens : (p : OPos Q.loc.shape) → Option (OpenO (OSym Q.loc.shape p))
  ext : E.Pos → Option (OpenO E.Sym)
  /-- the sibling digests for all trees -/
  sibs : List (Dig lam)
  rtreq : Dig lam
  slot : ℕ
  path : List (Dig lam)

def Opening.strip {σ : Type} (op : Opening lam σ) : OpenO σ := ⟨op.sym, op.salt⟩
def OpenO.bare {σ : Type} (op : OpenO σ) : Opening lam σ := ⟨op.sym, op.salt, []⟩

/-- the proof string as a `OneProtocolProof`, with empty paths in its openings -/
def BPrfO.bare {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (π : BPrfO lam Q) : OneProtocolProof lam Q :=
  ⟨π.salt, π.roots, π.plains, fun p => (π.opens p).map OpenO.bare,
    fun p => (π.ext p).map OpenO.bare, π.rtreq, π.slot, π.path⟩

/-- The compiled verifier of one slot for proof strings with pruned Merkle paths. -/
def verifyBO (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : BPrfO lam Q) :
    TypedOracleComputation lam K L Bool :=
  verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π.bare π.sibs

/-! ## Pruning -/

/-- a forest as the proof string shows it: its depth; the numbers of the leaves at which the proof
string holds an opening, each with its path -/
abbrev Plan (lam : ℕ) : Type := ℕ × List (ℕ × List (Dig lam))

def Plan.idx (T : Plan lam) : List ℕ := T.2.map Prod.fst
def Plan.need (T : Plan lam) : ℕ := Octopus.need T.1 T.idx
def Plan.reads (T : Plan lam) : List (Dig lam) := Octopus.reads T.1 T.2

/-- whole, or split into one plan for each leaf (Compile/Batch/Verifier.lean: Forest.split) -/
def Plan.split (pr : Bool) (T : Plan lam) : List (Plan lam) :=
  if pr then [T] else T.2.map fun x => (T.1, [x])

/-- one tree over a component of a prover message -/
def planComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : Plan lam :=
  (depth, (List.range (2 ^ depth)).filterMap fun j =>
      (posAt j).bind fun p => (f p).map fun op => (j, op.path))

/-- The plans of the trees of one component with a list of trees, from tree number k on: each tree
whole or split, as the one flag of the component says. There is a plan for every depth, also for a
tree whose root is not there; `forestsOfTrees` (Compile/Batch/Verifier.lean) has no forest for such
a tree. -/
def planTrees {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ℕ → List ℕ → List (List (Plan lam))
  | _, [] => []
  | k, d :: ds => (planComp (posAt k) d f).split pr :: planTrees pr posAt f (k + 1) ds

theorem planTrees_one {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k d : ℕ) :
    planTrees pr posAt f k [d] = [(planComp (posAt k) d f).split pr] := rfl

theorem planTrees_nil {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) :
    planTrees pr posAt f k [] = [] := rfl

def planB :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → List (Plan lam)
  | [], _, _, _ => []
  | _ :: s, (_, A), (w, W), f =>
      (planComp w.posAt0 w.depth0 fun p => f (.inl p)).split w.pr0 ++
        ((planComp w.posAtJ w.depthJ fun p => f (.inl p)).split w.prJ ++
          planB s A W fun p => f (.inr p))

/-- the number of an external position in the forest of the external trees -/
def extIdx {E : ExtSpec} (we : WireE E) (p : E.Pos) : ℕ := we.which p * 2 ^ we.depth + we.leaf p

def planExt {E : ExtSpec} (we : WireE E) (g : E.Pos → Option (Opening lam E.Sym)) : Plan lam :=
  (we.depth, we.all.filterMap fun p => (g p).map fun op => (extIdx we p, op.path))

/-- all forests of a proof string -/
def planOf {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (π : OneProtocolProof lam Q) :
    List (Plan lam) :=
  planB Q.loc.shape Q.ann wq.sh π.opens ++ (planExt wq.ext π.ext).split wq.ext.pr

/-- the sibling digests for all trees, read off the paths of the proof string -/
def sibsOf {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (π : OneProtocolProof lam Q) :
    List (Dig lam) :=
  (planOf wq π).flatMap Plan.reads

/-- Pruning: the openings' paths are dropped; of their digests those that the verification uses
remain, in the order of their use (for a proof string that passes the strict-format check and lacks
no opening: `plan_forestsOf`, Compile/Batch/PrunedFacts.lean). -/
def pruneO {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (π : OneProtocolProof lam Q) :
    BPrfO lam Q :=
  ⟨π.salt, π.roots, π.plains, fun p => (π.opens p).map Opening.strip,
    fun p => (π.ext p).map Opening.strip, sibsOf wq π, π.rtreq, π.slot, π.path⟩

/-! ## Back to full paths (for the analysis) -/

/-- the plan T with the paths that filling makes from the digests s (Hash/Octopus.lean: fill) -/
def Plan.filled (T : Plan lam) (s : List (Dig lam)) : Plan lam :=
  (T.1, T.idx.zip (Octopus.fill T.1 T.idx s))

/-- the plans Ts, each filled with its segment of s -/
def filledAll : List (Plan lam) → List (Dig lam) → List (Plan lam)
  | [], _ => []
  | T :: Ts, s => T.filled s :: filledAll Ts (s.drop T.need)

def needAll (Ts : List (Plan lam)) : ℕ := (Ts.map Plan.need).sum

/-- the path of leaf number j, if Ts are the plans of one tree (or forest) and s their sibling
digests -/
def pathIn (Ts : List (Plan lam)) (s : List (Dig lam)) (j : ℕ) : List (Dig lam) :=
  (((filledAll Ts s).flatMap Prod.snd).lookup j).getD []

/-- the paths for the positions of the prover's messages: the trees are taken in the order of planB,
and each takes its digests from sb -/
def refPaths :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → List (Dig lam) → OPos s → List (Dig lam)
  | [], _, _, _, _ => fun _ => []
  | _ :: s, (a, A), (w, W), f, sb =>
      let T0 := (planComp w.posAt0 w.depth0 fun p => f (.inl p)).split w.pr0
      let TJ := (planComp w.posAtJ w.depthJ fun p => f (.inl p)).split w.prJ
      fun p => match p with
        | .inl q =>
          if a.own q then pathIn TJ (sb.drop (needAll T0)) (w.place q) else pathIn T0 sb (w.place q)
        | .inr q => refPaths s A W (fun p => f (.inr p)) (sb.drop (needAll T0 + needAll TJ)) q

/-- The proof string π with the paths in its openings replaced: full paths that hold the digests of
s where the verification reads, and zeros elsewhere (under `wq.OKG`, `ExtInj`, if s is long enough:
`sibsOf_refill`, Compile/Batch/PrunedFacts.lean). The old paths are not read. -/
def refill {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q)
    (π : OneProtocolProof lam Q) (s : List (Dig lam)) : OneProtocolProof lam Q :=
  π.withPaths (refPaths Q.loc.shape Q.ann wq.sh π.opens s) fun p =>
    pathIn ((planExt wq.ext π.ext).split wq.ext.pr)
      (s.drop (needAll (planB Q.loc.shape Q.ann wq.sh π.opens))) (extIdx wq.ext p)

def fillO {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (π : BPrfO lam Q) :
    OneProtocolProof lam Q :=
  refill wq π.bare π.sibs

/-! ## The three verifiers

`vTO`, `vLO`, `vBO`: `verifyBO` at Test (`Tag.test`, `W.T`), at Link (`Tag.link`, `W.Lk`) and at a
slot of Batch (`Tag.onl`, `W.B`) on (x, π), as `vTS`, `vLS`, `vBS` of Compile/Batch/Verifier.lean
are `verifyOneProtocol`. cm, cm': the external roots; for Link the root cm of the key and a copy's root cm'.
The instance of Test and of Link is (), and their `xin` is fun _ => none; that of Batch is
`some`. -/

variable (W : QueryLayout lam L)

def vTO (sMT sFS : ℕ) (cm : Dig lam) (π : BPrfO lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    TypedOracleComputation lam W.K L Bool :=
  verifyBO sMT sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) W.T
    (fun p a => some (.inr ⟨Tag.test, ⟨p, a⟩⟩)) id (fun _ => none)
    (fun s => some (.inl s)) W.depthReq [cm] () π
def vLO (sMT sFS : ℕ) (cm cm' : Dig lam) (π : BPrfO lam (BatchInteractiveOracleProof.ofProto L.link)) :
    TypedOracleComputation lam W.K L Bool :=
  verifyBO sMT sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk
    (fun p a => some (.inr ⟨Tag.link, ⟨p, a⟩⟩)) id (fun _ => none) (fun s => some (.inl s))
    W.depthReq [cm, cm'] () π
def vBO (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : BPrfO lam L.onlineBatch) : TypedOracleComputation lam W.K L Bool :=
  verifyBO sMT sFS Tag.onl L.onlineBatch W.B (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) id some
    (fun s => some (.inl s)) W.depthReq [cm] x π

end Compile.Batch
