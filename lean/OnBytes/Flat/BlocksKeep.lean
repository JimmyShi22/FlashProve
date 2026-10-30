-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/BlocksKeep.lean: the blocks of the other chains whose dry runs state a file's rounds
leave the two flags of a run as they are.

A run of a block has two flags: whether it is dry, and whether intermediate values are kept.
`Blk.Keeps b` (OnBytes/Iop/DrySizes.lean) says that b leaves both as they are. For the links of a
proof's first chain it is shown in OnBytes/Flat/LinksKeeps.lean. Here it is shown of:
 - `Proof.sharedBlock S key`, a shared chain's block, and `Proof.secondBlock S first shared`, a
   second chain's (OnBytes/Proof/Tail.lean);
 - `Proof.firstBlock p links reply`, a proof's first chain's, if the block of the links keeps the
   flags (OnBytes/Proof/File.lean);
 - `linkVerify S first further`, an entry's chain's (OnBytes/Iop/Link.lean).
Each at all arguments. The proofs are by the walk of OnBytes/Flat/LinksKeepsTool.lean (`keeps`): a
theorem on each of the four and on every named routine that its text reaches and that had none, each
behind those of the routines that it calls.

Main theorems: `sharedBlock_keeps`, `secondBlock_keeps`, `firstBlock_keeps`,
`linkVerify_keeps`.

Not claimed: anything on what a block decides, or on what its dry run returns. Nothing on the block
of a key file's one-time chain (`Key.oneTime`, OnBytes/Key/OneTime.lean). For proofs only; no
module of the program imports this file.


-/
import OnBytes.Flat.LinksKeeps
import OnBytes.Proof.File

set_option autoImplicit false

namespace OnBytes.Flat

/-! ## By hand: a routine that calls itself -/

theorem KeepsOf.OnBytes.Psc.hearMany (ns : List Nat) : Over.K (Psc.hearMany ns) := by
  induction ns with
  | nil => unfold _root_.OnBytes.Psc.hearMany; keeps
  | cons n ns ih => unfold _root_.OnBytes.Psc.hearMany; keeps

/-! ## By the walk -/

/-! ### `OnBytes.Proof.sharedBlock`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.requireAllTested :
    Over.K OnBytes.Blk.requireAllTested := by
  keeps

theorem KeepsOf.OnBytes.foldeqColumnsVerify (key : OnBytes.TableKey)
    (S : OnBytes.Params.FoldeqShape) (eqGamma : Array OnBytes.E) (pos : OnBytes.Positions)
    (first : Nat) (u : OnBytes.FoldedRow) (g : Nat) :
    Over.K (OnBytes.foldeqColumnsVerify key S eqGamma pos first u g) := by
  keeps

theorem KeepsOf.OnBytes.foldeqVerify (key : OnBytes.TableKey)
    (S : OnBytes.Params.FoldeqShape) (gamma : List OnBytes.E) (g : Nat)
    (others : Array OnBytes.OracleNotice := #[]) :
    Over.K (OnBytes.foldeqVerify key S gamma g others) := by
  keeps

theorem KeepsOf.OnBytes.linSharedTestsVerify (S : OnBytes.Params.LinShape)
    (x : OnBytes.LinShared) : Over.K (OnBytes.linSharedTestsVerify S x) := by
  keeps

theorem KeepsOf.OnBytes.splitVerify (row : OnBytes.Row) (g1 g2 maskMessage : Nat) :
    Over.K (OnBytes.splitVerify row g1 g2 maskMessage) := by
  keeps

theorem KeepsOf.OnBytes.linSharedVerify (S : OnBytes.Params.LinShape)
    (key : OnBytes.TableKey) : Over.K (OnBytes.linSharedVerify S key) := by
  keeps

theorem KeepsOf.OnBytes.Proof.sharedBlock (S : OnBytes.Params.LinShape)
    (key : OnBytes.TableKey) : Over.K (OnBytes.Proof.sharedBlock S key) := by
  keeps

/-! ### `OnBytes.Proof.secondBlock`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.adoptOracles (sent : Array OnBytes.OracleNotice)
    (given : Array (Nat × Fmt.Src)) : Over.K (OnBytes.Blk.adoptOracles sent given) := by
  keeps

theorem KeepsOf.OnBytes.Blk.sampledElsewhere (mine : Nat) (other : OnBytes.Statement)
    (theirs : Nat) : Over.K (OnBytes.Blk.sampledElsewhere mine other theirs) := by
  keeps

theorem KeepsOf.OnBytes.linAdopt (fromSt : OnBytes.Statement)
    (fromBook : OnBytes.TreeBook) (theirs leafClass : Nat) :
    Over.K (OnBytes.linAdopt fromSt fromBook theirs leafClass) := by
  keeps

theorem KeepsOf.OnBytes.linSecondTestsVerify (S : OnBytes.Params.LinShape)
    (first : OnBytes.LinFirst) (x : OnBytes.LinSecond) :
    Over.K (OnBytes.linSecondTestsVerify S first x) := by
  keeps

theorem KeepsOf.OnBytes.linSecondVerify (S : OnBytes.Params.LinShape)
    (first : OnBytes.LinFirst) (sharedSt : OnBytes.Statement) (sharedBook : OnBytes.TreeBook)
    (shared : OnBytes.LinShared) :
    Over.K (OnBytes.linSecondVerify S first sharedSt sharedBook shared) := by
  keeps

theorem KeepsOf.OnBytes.Proof.secondBlock (S : OnBytes.Params.LinShape)
    (first : OnBytes.LinFirst) (shared : OnBytes.Proof.SharedEnd) :
    Over.K (OnBytes.Proof.secondBlock S first shared) := by
  keeps

/-! ### `OnBytes.Proof.firstBlock`, and what its text reaches -/

theorem KeepsOf.OnBytes.Proof.firstEnd (lin : OnBytes.LinFirst) :
    Over.K (OnBytes.Proof.firstEnd lin) := by
  keeps

theorem KeepsOf.OnBytes.Psc.hearOne (name : String) (kind : Fmt.Kind) (n nz : Nat) :
    Over.K (OnBytes.Psc.hearOne name kind n nz) := by
  keeps

theorem KeepsOf.OnBytes.linFirstRows (S : OnBytes.Params.LinShape)
    (claim : OnBytes.LinClaim) (ids : Array Nat) :
    Over.K (OnBytes.linFirstRows S claim ids) := by
  keeps

theorem KeepsOf.OnBytes.linFirstVerify (S : OnBytes.Params.LinShape)
    (claim : OnBytes.LinClaim) : Over.K (OnBytes.linFirstVerify S claim) := by
  keeps

theorem KeepsOf.OnBytes.takeSlots (o n : Nat) :
    Over.K (OnBytes.takeSlots o n) := by
  keeps

theorem KeepsOf.OnBytes.Psc.hear (x : OnBytes.Psc.Size) :
    Over.K (OnBytes.Psc.hear x) := by
  keeps

theorem KeepsOf.OnBytes.Psc.verify (c : OnBytes.Psc.Claim) (S : OnBytes.Psc.Summand)
    (fresh : List OnBytes.Slot) : Over.K (OnBytes.Psc.verify c S fresh) := by
  keeps

theorem KeepsOf.OnBytes.Batt.verify (kCol : Nat) (rows : List OnBytes.TensorRow)
    (ledger : Nat) : Over.K (OnBytes.Batt.verify kCol rows ledger) := by
  keeps

theorem KeepsOf.OnBytes.memberFirstVerify (S : OnBytes.Params.LinShape)
    (indexMasks : Nat) (pending : List OnBytes.TensorRow) :
    Over.K (OnBytes.memberFirstVerify S indexMasks pending) := by
  keeps

theorem KeepsOf.OnBytes.Proof.firstBlock (p : OnBytes.Params.First)
    (links : OnBytes.Blk OnBytes.Proof.LinksResult) (reply : OnBytes.E)
    (h : Over.K links) :
    Over.K (OnBytes.Proof.firstBlock p links reply) := by
  keeps

/-! ### `OnBytes.linkVerify`, and what its text reaches -/

theorem KeepsOf.OnBytes.groupTarget (g i : Nat) :
    Over.K (OnBytes.groupTarget g i) := by
  keeps

theorem KeepsOf.OnBytes.linkStepsVerify (S : OnBytes.Params.LinkShape)
    (first further : OnBytes.TableKey) :
    Over.K (OnBytes.linkStepsVerify S first further) := by
  keeps

theorem KeepsOf.OnBytes.linkTestVerify (S : OnBytes.Params.LinkShape)
    (x : OnBytes.LinkRun) : Over.K (OnBytes.linkTestVerify S x) := by
  keeps

theorem KeepsOf.OnBytes.linkVerify (S : OnBytes.Params.LinkShape)
    (first further : OnBytes.TableKey) :
    Over.K (OnBytes.linkVerify S first further) := by
  keeps

/-! ## The four blocks -/

/-- A shared chain's block keeps the flags. -/
theorem sharedBlock_keeps (S : Params.LinShape) (key : TableKey) :
    Blk.Keeps (Proof.sharedBlock S key) := KeepsOf.OnBytes.Proof.sharedBlock S key

/-- A second chain's block keeps the flags. -/
theorem secondBlock_keeps (S : Params.LinShape) (first : LinFirst) (shared : Proof.SharedEnd) :
    Blk.Keeps (Proof.secondBlock S first shared) :=
  KeepsOf.OnBytes.Proof.secondBlock S first shared

/-- The block of a proof's first chain keeps the flags, if the block of the links does. -/
theorem firstBlock_keeps (p : Params.First) {links : Blk Proof.LinksResult}
    (h : Blk.Keeps links) (reply : E) : Blk.Keeps (Proof.firstBlock p links reply) :=
  KeepsOf.OnBytes.Proof.firstBlock p links reply h

/-- An entry's chain's block keeps the flags. -/
theorem linkVerify_keeps (S : Params.LinkShape) (first further : TableKey) :
    Blk.Keeps (linkVerify S first further) := KeepsOf.OnBytes.linkVerify S first further

end OnBytes.Flat
