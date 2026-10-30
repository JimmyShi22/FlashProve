-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarX.lean: the honest programs of the compiled scheme, with the hash blocks that each
transcript has received as a further output. Used in the analysis of completeness only. Definitions,
and lemmas that dropping the further output gives the programs of the scheme, and two laws of
`Step.bind`. (Words of this library: lean/GLOSSARY.md.)

With proof-of-work bits the event that a proof string is `none` or a search has failed
(Compile/Batch/CompleteRefDefs.lean: `Ref.badAt`) is no function of what the scheme outputs (why:
the next paragraph). Here programs of Compile/Batch/Prover.lean and Compile/Batch/Star.lean are
written once more, with the same bodies, and a last line that also returns the hash blocks.

Under the hypotheses of `Spec.acceptsHonestBUG` (Compile/Batch/SpecCompleteUG.lean; it is stated for
the prover of Compile/Batch/StarUX.lean), without proof-of-work bits the honest run fails for a
request only if a proof string is `none`, and that can be read off the key and the proofs. With such
bits (Compile/Batch/SpecGrind.lean) it also fails if a search over nonces has failed: if some
proof-of-work bit of the verifier randomness of a transcript is 1. (It is so for `L.grind`, whose
verifier checks the bits: this is by reading. The statements of Compile/Batch/SpecGrind.lean neither
assume nor conclude that V then rejects.) That randomness is made from the hash blocks of the
Fiat-Shamir answers (`rhoOf`), and these are neither in the key nor in a proof.

Of the prover only `PpJ` has a counterpart here: `Pp`, `Ptok` and `P` of Compile/Batch/Star.lean
have none.

  `proveBX`   `proveB`, and for each slot the hash blocks that it has received
  `proveTX`, `proveLkX`, `leavesCX`, `CpX`
      the committer: the hash blocks of Test, and of Link for each copy
  `PpJX`   the prover at a given copy and placement: the hash blocks of each slot
  `CtokX`, `CX`   what `erase` makes of the committer; the same with the ghost names written back
                  (`realQ`), as in Compile/Batch/Star.lean
  `RunX`   what the honest run outputs beside the verification key and the proofs
  `RunX.badT`, `RunX.badL`, `RunX.badB`
      the three events, each stated with `Ref.badAt`: Test; Link for the sampled copy; the slot of
      request number a

Notation: `L`: an `BatchProtocol I X`: the record of protocols (Test, Link, Batch; Iop/Batch.lean); `W`: a
`QueryLayout lam L`, the wire record (Iop/BatchWire.lean); `WP`: a `WireBP L`: the prover's data for the
three protocols, and the enumeration of the encoding randomness (Iop/BatchWireP.lean); `p`: a
`Params` (Compile/Star.lean); `p.sMT`, `p.sFS`: the length of the salt of a leaf, and of the salt of
a chain (Compile/Batch/Verifier.lean); the number of copies is `p.M` + 1; `t`, `Q`, `H`, `wq`, `wp`:
a `Tag`, a `BatchInteractiveOracleProof Y E`, its `BatchHonestProver`, its wire records `ProtocolQueryLayout` and `WirePB`; `xs`: in
`proveBX` a list of slots (`none`: an empty slot) (`proveB`, Compile/Batch/Prover.lean); in `PpJX` a
`List X`: the requests: request number a is in slot σ a (`slotsOfReq`, Compile/Batch/Star.lean);
`fr`, `fl`: maps `ℕ → Bool`: the flags of the requests, and these as flags of the slots
(`slotFlags`, Compile/Batch/Star.lean); fr: for which requests a proof string is made at all (the
head of that file); `σ`, `j`: a permutation of `Fin L.maxBatchSize`: request number a is in slot σ a; the
number of a copy (the head of Compile/Batch/Star.lean; j: `PpJ` there); `XC`, `XP`: the further
output of the committer, of the prover; a search: the nonces 0, 1, .., g.more in this order, one
Fiat-Shamir query each (an attempt), until all proof-of-work bits of the verifier message that the
answer gives are 0 (`fbTG`, Compile/Batch/Prover.lean).

The lemmas `proveB_eq` to `C_eq` are equations between programs; no distribution is used. Nothing
here is run by anybody.
-/
import Compile.Batch.Star
import Compile.Batch.CompleteRefDefs
import Compile.Batch.RealQ
import Compile.EraseKit
import Rom.Bridge

noncomputable section

namespace Rom

variable {S : OSpec} {sp : Split S} {α β γ : Type}

theorem Step.bind_assoc' (c : Step S sp α) (g : α → Step S sp β) (h : β → Step S sp γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (Step.sample n) (funext ih)
  | plain o q k ih => exact congrArg (Step.plain o q) (funext ih)
  | fresh l k ih => exact congrArg (Step.fresh l) (funext ih)
  | marked o t us pt inj k ih => exact congrArg (Step.marked o t us pt inj) (funext fun v => funext fun u => ih v u)
  | reveal ts k ih => exact congrArg (Step.reveal ts) (funext ih)

theorem Step.bind_pure' (c : Step S sp α) : (c.bind fun a => Step.pure a) = c := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (Step.sample n) (funext ih)
  | plain o q k ih => exact congrArg (Step.plain o q) (funext ih)
  | fresh l k ih => exact congrArg (Step.fresh l) (funext ih)
  | marked o t us pt inj k ih => exact congrArg (Step.marked o t us pt inj) (funext fun v => funext fun u => ih v u)
  | reveal ts k ih => exact congrArg (Step.reveal ts) (funext ih)

end Rom

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- `proveB`, and for each slot the hash blocks that it has received. -/
def proveBX (fl : ℕ → Bool) (xs : List (Option Y)) :
    St lam K L (List (Option (OneProtocolProof lam Q)) × List (List (Blk lam K))) :=
  (drawT wp.coin0).bind fun c0 =>
  (eachM (initSlot sFS Q H wp w c0) xs).bind fun zs =>
  (chainT sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape Q.ann
      wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩).bind fun out =>
  (finishAll Q H wq wp trees w fl c0 out.2 0 out.1).bind fun πs =>
    Step.pure (πs, out.1.map fun a => a.blocks)

theorem proveB_eq (fl : ℕ → Bool) (xs : List (Option Y)) :
    proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs =
      (proveBX sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs).bind fun o =>
        Step.pure o.1 := by
  unfold proveB proveBX
  simp only [Step.bind_assoc']
  refine congrArg _
    (funext fun c0 => congrArg _ (funext fun zs => congrArg _ (funext fun out => ?_)))
  exact (Step.bind_pure' _).symm

end Prove

/-! ## The committer and the prover -/

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

def proveTX (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    St lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) × List (List (Blk lam W.K))) :=
  (proveBX p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
      (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [tree] (i, r)
      (fun _ => true) [some ()]).bind fun o =>
  Step.pure (o.1.headD none, o.2)

def proveLkX (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    St lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) × List (List (Blk lam W.K))) :=
  (proveBX p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
      (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [root, tree]
      (i, r₀, r) (fun _ => true) [some ()]).bind fun o =>
  Step.pure (o.1.headD none, o.2)

def leavesCX (i : I) (root : Node lam L) :
    ℕ → St lam W.K L (List (LeafRec lam L) × List (List (List (Blk lam W.K))))
  | 0 => Step.pure ([], [])
  | n + 1 =>
      (nodeP' W WP p i).bind fun nd =>
      (proveLkX W WP p root.tree nd.tree i root.r nd.r).bind fun π =>
      (leavesCX i root n).bind fun rest => Step.pure (⟨nd, π.1⟩ :: rest.1, π.2 :: rest.2)

/-- the committer; further output: the hash blocks of Test, and of Link for each copy -/
def CpX (i : I) :
    St lam W.K L
      ((IVK lam L × IskH lam L) × (List (List (Blk lam W.K)) × List (List (List (Blk lam W.K))))) :=
  (nodeP' W WP p i).bind fun root =>
  (proveTX W WP p root.tree i root.r).bind fun πT =>
  (leavesCX W WP p i root (p.M + 1)).bind fun ls =>
  Step.pure ((⟨root.tree.root, πT.1⟩, ⟨i, root, ls.1⟩), (πT.2, ls.2))

def PpJX (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    St lam W.K L (List (Prf lam L) × List (List (Blk lam W.K))) :=
  match k.leaves[j]? with
  | none => Step.pure (xs.map fun _ => ⟨j, default, none, none⟩, [])
  | some lf =>
      (proveBX p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun o =>
      Step.pure ((List.range xs.length).map fun a =>
          ⟨j, lf.node.tree.root, lf.piL,
            if h : a < L.maxBatchSize then o.1.getD (σ ⟨a, h⟩).val none else none⟩,
        o.2)

theorem proveT_eq (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    proveT W WP p tree i r = (proveTX W WP p tree i r).bind fun o => Step.pure o.1 := by
  unfold proveT proveTX
  rw [proveB_eq]
  simp only [Step.bind_assoc']
  rfl

theorem proveLk_eq (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    proveLk W WP p root tree i r₀ r =
      (proveLkX W WP p root tree i r₀ r).bind fun o => Step.pure o.1 := by
  unfold proveLk proveLkX
  rw [proveB_eq]
  simp only [Step.bind_assoc']
  rfl

theorem leavesC_eq (i : I) (root : Node lam L) :
    ∀ n, leavesC W WP p i root n = (leavesCX W WP p i root n).bind fun o => Step.pure o.1
  | 0 => rfl
  | n + 1 => by
      show (nodeP' W WP p i).bind (fun nd =>
          (proveLk W WP p root.tree nd.tree i root.r nd.r).bind fun π =>
            (leavesC W WP p i root n).bind fun rest => Step.pure (⟨nd, π⟩ :: rest)) =
        ((nodeP' W WP p i).bind fun nd =>
            (proveLkX W WP p root.tree nd.tree i root.r nd.r).bind fun π =>
              (leavesCX W WP p i root n).bind fun rest =>
                Step.pure (⟨nd, π.1⟩ :: rest.1, π.2 :: rest.2)).bind
          fun o => Step.pure o.1
      simp only [proveLk_eq, leavesC_eq i root n, Step.bind_assoc']
      rfl

theorem Cp_eq (i : I) : Cp W WP p i = (CpX W WP p i).bind fun o => Step.pure o.1 := by
  unfold Cp CpX
  simp only [proveT_eq, leavesC_eq, Step.bind_assoc']
  rfl

theorem PpJ_eq (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    PpJ W WP p k fr xs j σ = (PpJX W WP p k fr xs j σ).bind fun o => Step.pure o.1 := by
  unfold PpJ PpJX
  cases k.leaves[j]? with
  | none => rfl
  | some lf =>
      show (proveB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind _ =
        ((proveBX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind _).bind _
      rw [proveB_eq]
      simp only [Step.bind_assoc']
      rfl

/-! ## As oracle algorithms -/

/-- the further output of the committer, of the prover -/
abbrev XC (lam K : ℕ) : Type := List (List (Blk lam K)) × List (List (List (Blk lam K)))
abbrev XP (lam K N : ℕ) : Type := ℕ × Equiv.Perm (Fin N) × List (List (Blk lam K))

def CtokX (i : I) : TypedOracleComputation lam W.K L ((IVK lam L × ISK lam L) × XC lam W.K) :=
  (erase (CpX W WP p i) []).bind fun o => OComp.pure ((o.1.1.1, (o.1.1.2, o.2)), o.1.2)

/-- `CtokX` with the ghost names written back (`realQ`) -/
def CX (i : I) : TypedOracleComputation lam W.K L ((IVK lam L × ISK lam L) × XC lam W.K) := realQ (CtokX W WP p i)

theorem Ctok_eq (i : I) : Ctok W WP p i = (CtokX W WP p i).bind fun o => OComp.pure o.1 := by
  unfold Ctok CtokX
  rw [Cp_eq, erase_bind]
  simp only [OComp.bind_assoc]
  rfl

/-- The committer of the scheme is `CX` with the further output dropped. -/
theorem C_eq (i : I) : C W WP p i = (CX W WP p i).bind fun o => OComp.pure o.1 := by
  unfold C CX
  rw [Ctok_eq, realQ_bind]
  rfl

/-! ## What the honest run (`runAllBUX`, Compile/Batch/StarUX.lean) outputs further, and its three
events -/

/-- what the honest run outputs beside the verification key and the proofs -/
structure RunX (lam K : ℕ) (L : BatchProtocol I X) where
  isk : IskH lam L
  /-- the hash blocks of Test; of Link for each copy -/
  bT : List (List (Blk lam K))
  bL : List (List (List (Blk lam K)))
  /-- the sampled copy, the sampled placement, the hash blocks of each slot of the batch -/
  leaf : ℕ
  perm : Equiv.Perm (Fin L.maxBatchSize)
  bB : List (List (Blk lam K))

variable {W}

/-- Test's proof string is `none`, or one of its searches over nonces has failed -/
def RunX.badT (WP : WireBP L) (z : RunX lam W.K L) : Bool :=
  Ref.badAt (BatchInteractiveOracleProof.ofProto L.offline)
    (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T (z.isk.i, z.isk.root.r) () 0 z.bT

/-- Link's proof string for the sampled copy is `none`, or one of its searches has failed (true also
without such a copy) -/
def RunX.badL (WP : WireBP L) (z : RunX lam W.K L) : Bool :=
  match z.isk.leaves[z.leaf]? with
  | none => true
  | some lf =>
    Ref.badAt (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
      (z.isk.i, z.isk.root.r, lf.node.r) () 0 (z.bL.getD z.leaf [])

/-- the proof string of the slot of request number a, which is x, is `none`, or a search of its
transcript has failed (true also without the sampled copy) -/
def RunX.badB (WP : WireBP L) (z : RunX lam W.K L) (a : Fin L.maxBatchSize) (x : X) : Bool :=
  match z.isk.leaves[z.leaf]? with
  | none => true
  | some lf => Ref.badAt L.onlineBatch L.honestOnlineBatchProver W.B WP.B (z.isk.i, lf.node.r) x (z.perm a).val z.bB

end Compile.Batch
