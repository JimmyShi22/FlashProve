-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Wire.lean: a file with three joined hash chains as the compiler takes it: its
protocol with the wire record and the maps into the typed queries; the type of its proof string; its
compiled verifier. Definitions only.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Compile/Joined/Types.lean has the rounds of a file (`Chains`) and its verifier (`Desc`), which give
one batch protocol (`Desc.batch`). Here that protocol meets the compiler over wire records with
lists of trees (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean).

Main names:
  `Written W Y E`   a batch protocol as it is written into the typed queries of the oracles: the
                    arguments of `verifyOneProtocol`
  `Written.verify`, `Written.verifyLax`   the compiled verifier with and without the strict-format
                    check
  `FileW W G Y E`   the same for a file over the rounds G; `FileW.written`
  `FileW.Prf`       the proof string of a file: `OneProtocolProof` at the file's protocol
  `FileW.trees`     the file's trees in the order in which their roots are sent, each by the round
                    that sent it (`TreeRef`): read off the wire record, by the rule of `recomputeChain`
  `FileW.refOf`, `FileW.numOf`   the tree of a position; its number over the whole file

What stands between the chains, and where it is in these types (π : a proof string, `OneProtocolProof`):
  chain 1's salt                 `π.salt`: it stands in (F1)
  the roots of all three chains  `π.roots`: one list, in the order of sending
  SEAL 1, the slot's value       the answer to (G) at the joining round: `Phase.slotVal`
  the slot, its salt, its path   `π.slot`, `π.rsalt`, `π.path`: the leaf of the binding tree holds
                                 the slot's value and, behind it, `π.rsalt` (`reqCheck`)
  the binding root               `π.rtreq`: it stands in (F4), chain 2's first call
  SEAL 2                         the chaining value behind chain 2's last round: ρ0 of `Phase.shr`;
                                 it stands in (F3), chain 3's first call, with the slot's value
  the run's values of chain 2 and chain 3; the answers of the record over the three chains
                                 in the plain parts of the joining round and of the seam:
                                 `G.plJ π.plains`, `G.pl3 π.plains`
  a tree taken over              an opening `π.opens p` at a position p of the sender's round: it is
                                 checked under the root that the sender's round sent

Limits: nothing here is proved. No law ties a run's value, or the record's answers, to anything:
they are free data of the proof string that are hashed. That `FileW.trees` lists the trees as
`recomputeChain` takes their roots is proved in OnBytes/TypedOracleCompiler/Joined/RootsTrees.lean (the number) and
RootsAt.lean (entry by entry). That a proof string's list of roots is these and no more is shown
there where `verify`, with the strict-format check, says yes; under `verifyLax` more entries may
stand behind them. The number in the label of a tree's
leaves is no field: it belongs to `embS`, a public function of the position, which may be given
through `refOf` and `numOf`. The run's value that salts a tree's leaves (the sender's) is the proof
string's own datum: it can ride in the salt of an opening alone (`Opening.salt`), of which the
strict-format check tests the length; nothing ties it to the plain parts of the joining round and
the seam. The depth of the binding tree is `W.dReq t`, one number for each tag t: two files whose
binding trees differ in depth are written at two tags. Where the byte format's leaf of the binding
tree holds the slot's number too, a typing lays it into `π.rsalt`, with the salt: the verifier takes
any bits there. Nothing compares a number in `π.rsalt` with `π.slot`, from which the check climbs;
and once the chain has joined, the length of `π.rsalt` is not tested.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Compile.Joined.Types

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc TreeRef)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## A written protocol -/

/-- A batch protocol as it is written into the typed queries of the oracles: the arguments of
`verifyOneProtocol` but for the two lengths of salts, the depth of the request tree (it goes by the tag:
`W.dReq t`), the outer roots, the instance and the string. -/
structure Written (W : QueryLayout lam L) (Y : Type) (E : ExtSpec) where
  /-- the tag of its queries -/
  t : Tag
  /-- the protocol -/
  Q : BatchInteractiveOracleProof Y E
  /-- its wire record -/
  wq : ProtocolQueryLayout lam W.K Q
  /-- how a symbol of a prover's oracle is written into a leaf -/
  embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L
  /-- how a plain part is written into a query -/
  embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)
  /-- what of an instance is written into a query -/
  xin : Y → Option X
  /-- how a symbol of an external string is written into a leaf -/
  embE : E.Sym → Body L

namespace Written
variable {W : QueryLayout lam L} {Y : Type} {E : ExtSpec} (Z : Written W Y E)

/-- the compiled verifier with the strict-format check, at a written protocol -/
def verify (sMT sFS : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Z.Q) : TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Z.t Z.Q Z.wq Z.embS Z.embP Z.xin Z.embE (W.dReq Z.t) cms x π

/-- the compiled verifier without that check, on whole paths -/
def verifyLax (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Z.Q) : TypedOracleComputation lam W.K L Bool :=
  verifyB Z.t Z.Q Z.wq Z.embS Z.embP Z.xin Z.embE (W.dReq Z.t) cms x π

end Written

/-! ## The trees of a wire record -/

/-- n trees of one component of round number i -/
def refs (i : ℕ) (own : Bool) (n : ℕ) : List TreeRef := (List.range n).map fun k => ⟨i, own, k⟩

/-- The trees of the rounds s, from round number i on, in the order in which `recomputeChain` takes their
roots from the list: in a local round those of the slot's component; in the joining round, the first
shared round, those of the slot's component and then those of the shared one; in a later shared
round those of the shared component. joined: has the joining round passed. -/
def treesSB {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → Bool → List TreeRef
  | [], _, _, _, _ => []
  | _ :: s, (a, A), (w, W), i, joined =>
    match a.kind with
    | .lo => refs i true w.depthJ.length ++ treesSB s A W (i + 1) joined
    | .sh =>
      (if joined then [] else refs i true w.depthJ.length) ++
        (refs i false w.depth0.length ++ treesSB s A W (i + 1) true)

/-- the tree in which a position stands -/
def refSB {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → OPos s → TreeRef
  | [], _, _, _, p => nomatch p
  | _ :: _, (a, _), (w, _), i, .inl p => ⟨i, a.own p, w.tree p⟩
  | _ :: s, (_, A), (_, W), i, .inr q => refSB s A W (i + 1) q

/-! ## A written file -/

/-- A file over the rounds G as it is written into the typed queries of the oracles. -/
structure FileW (W : QueryLayout lam L) (G : Chains) (Y : Type) (E : ExtSpec) where
  /-- the file's verifier -/
  D : Desc G Y E
  /-- the tag of its queries -/
  t : Tag
  /-- the wire record of the whole: all three chains' rounds, the joining round and the seam -/
  wq : ProtocolQueryLayout lam W.K D.batch
  /-- how a symbol of a prover's oracle is written into a leaf -/
  embS : (p : OPos G.sh) → OSym G.sh p → Body L
  /-- how a plain part is written into a query -/
  embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)
  /-- what of an instance is written into a query -/
  xin : Y → Option X
  /-- how a symbol of an external string is written into a leaf -/
  embE : E.Sym → Body L

namespace FileW
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)

/-- the file as a written protocol -/
@[reducible] def written : Written W Y E := ⟨F.t, F.D.batch, F.wq, F.embS, F.embP, F.xin, F.embE⟩

/-- The proof string of a file: one salt, one list of roots, the plain parts and the openings of all
rounds of the three chains, the openings of the external strings, and the binding root with the
slot, its path and its salt. -/
abbrev Prf : Type := OneProtocolProof lam F.D.batch

/-- The file's trees, in the order in which their roots stand in a proof string's list. -/
def trees : List TreeRef := treesSB G.sh G.ann F.wq.sh 0 false

/-- the tree in which a position stands, its own chain's or one that an earlier chain sent -/
def refOf (p : OPos G.sh) : TreeRef := refSB G.sh G.ann F.wq.sh 0 p

/-- the number over the whole file of the tree in which a position stands -/
def numOf (p : OPos G.sh) : Option ℕ := F.trees.findIdx? fun r => decide (r = F.refOf p)

end FileW

end TypedOracleCompiler.Joined
