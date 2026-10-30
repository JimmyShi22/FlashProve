-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarUX.lean: the honest prover that makes no query and builds no tree for an empty
slot, with the hash blocks that each slot has received as a further output. Used in the analysis of
completeness only. Definitions; dropping the further output gives the scheme's programs. (Words of
this library: lean/GLOSSARY.md.)

It is Compile/Batch/StarX.lean for the prover of Compile/Batch/ProverU.lean and
Compile/Batch/StarU.lean, and it goes on to the whole prover and one honest run. The further output
is there because the event that a proof string is `none` or a search has failed (`Ref.badAt`)
depends on hash blocks that are neither in the key nor in a proof. The committer is that of
Compile/Batch/Star.lean, so `CX`, `RunX` and the three events `RunX.badT`, `badL`, `badB` are those
of Compile/Batch/StarX.lean.

  `proveBUX`   `proveBU`, and for each slot the hash blocks that it has received (an empty slot:
               those of the shared rounds alone)
  `PpJUX`   the prover at a given copy and placement: the hash blocks of each slot
  `PtokUX`   what `erase` makes of `PpUX`

Notation: `sMT`, `sFS`: natural numbers: the length of the salt of a leaf, and of the salt of a
chain (Compile/Batch/Verifier.lean); `t`, `Q`, `H`, `wq`, `wp`: a `Tag`, a `BatchInteractiveOracleProof Y E`, its
`BatchHonestProver`, its wire records `ProtocolQueryLayout` and `WirePB`; `xs`: in `proveBUX` a list of slots (`none`: an
empty slot) (`proveB`, Compile/Batch/Prover.lean); in `PpJUX`, `PpUX` a `List X`: the requests:
request number a is in slot σ a (`slotsOfReq`, Compile/Batch/Star.lean); `fr`, `fl`: maps
`ℕ → Bool`: the flags of the requests, and these as flags of the slots (`slotFlags`,
Compile/Batch/Star.lean); fr: for which requests a proof string is made at all (the head of that
file); a search: the nonces 0, 1, .., g.more in this order, one Fiat-Shamir query each (an attempt),
until all proof-of-work bits of the verifier message that the answer gives are 0 (`fbTG`,
Compile/Batch/Prover.lean); `XP lam K N`: `ℕ × Equiv.Perm (Fin N) × List (List (Blk lam K))`: the
further output of the prover: the sampled copy, the sampled placement, the hash blocks of each slot;
the fields of `RunX`: `isk`; `bT`, `bL`: the hash blocks of Test; of Link for each copy; `leaf`,
`perm`, `bB`: the sampled copy, the sampled placement, the hash blocks of each slot of the batch
(both: Compile/Batch/StarX.lean).

The lemmas `proveBU_eq` to `PU_eq` are equations between programs; no distribution is used. Nothing
here is run by anybody.
-/
import Compile.Batch.StarX
import Compile.Batch.StarU

noncomputable section

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

/-- `proveBU`, and for each slot the hash blocks that it has received. -/
def proveBUX (fl : ℕ → Bool) (xs : List (Option Y)) :
    St lam K L (List (Option (OneProtocolProof lam Q)) × List (List (Blk lam K))) :=
  (drawT wp.coin0).bind fun c0 =>
  (eachM (initSlotU sFS Q H wp w c0) xs).bind fun zs =>
  (chainTU sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape Q.ann
      wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩).bind fun out =>
  (finishAll Q H wq wp trees w fl c0 out.2 0 out.1).bind fun πs =>
    Step.pure (πs, out.1.map fun a => a.blocks)

theorem proveBU_eq (fl : ℕ → Bool) (xs : List (Option Y)) :
    proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs =
      (proveBUX sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs).bind fun o =>
        Step.pure o.1 := by
  unfold proveBU proveBUX
  simp only [Step.bind_assoc']
  refine congrArg _
    (funext fun c0 => congrArg _ (funext fun zs => congrArg _ (funext fun out => ?_)))
  exact (Step.bind_pure' _).symm

end Prove

/-! ## The prover -/

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

def PpJUX (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    St lam W.K L (List (Prf lam L) × List (List (Blk lam W.K))) :=
  match k.leaves[j]? with
  | none => Step.pure (xs.map fun _ => ⟨j, default, none, none⟩, [])
  | some lf =>
      (proveBUX p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun o =>
      Step.pure ((List.range xs.length).map fun a =>
          ⟨j, lf.node.tree.root, lf.piL,
            if h : a < L.maxBatchSize then o.1.getD (σ ⟨a, h⟩).val none else none⟩,
        o.2)

/-- the prover; further output: the sampled copy, the sampled placement, the hash blocks of each
slot -/
def PpUX (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) :
    St lam W.K L (List (Prf lam L) × (ℕ × Equiv.Perm (Fin L.maxBatchSize) × List (List (Blk lam W.K)))) :=
  Step.sample p.M fun j =>
    (drawT WP.perm).bind fun σ =>
      (PpJUX W WP p k fr xs j.val σ).bind fun o => Step.pure (o.1, (j.val, σ, o.2))

theorem PpJU_eq (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    PpJU W WP p k fr xs j σ = (PpJUX W WP p k fr xs j σ).bind fun o => Step.pure o.1 := by
  unfold PpJU PpJUX
  cases k.leaves[j]? with
  | none => rfl
  | some lf =>
      show (proveBU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind _ =
        ((proveBUX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).bind _).bind _
      rw [proveBU_eq]
      simp only [Step.bind_assoc']
      rfl

theorem PpU_eq (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) :
    PpU W WP p k fr xs = (PpUX W WP p k fr xs).bind fun o => Step.pure o.1 := by
  unfold PpU PpUX
  refine congrArg (Step.sample p.M) (funext fun j => ?_)
  simp only [PpJU_eq, Step.bind_assoc']
  rfl

/-! ## As oracle algorithms -/

def PtokUX (k : ISK lam L) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (Prf lam L) b × XP lam W.K L.maxBatchSize) :=
  (erase (PpUX W WP p k.1 (fun _ => true) (b.map Prod.fst)) k.2).bind fun o =>
    OComp.pure (fitLen ⟨0, default, none, none⟩ b.length o.1.1, o.1.2)

/-- `PtokUX` with the ghost names written back (`realQ`, Compile/Batch/Oracles.lean: a query to
`fbw t k` becomes the query to `fb t`) -/
def PUX (k : ISK lam L) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (Prf lam L) b × XP lam W.K L.maxBatchSize) :=
  realQ (PtokUX W WP p k b)

theorem PtokU_eq (k : ISK lam L) (b : List (X × Unit)) :
    PtokU W WP p k b = (PtokUX W WP p k b).bind fun o => OComp.pure o.1 := by
  unfold PtokU PtokUX
  rw [PpU_eq, erase_bind]
  simp only [OComp.bind_assoc]
  rfl

/-- The prover `PU` of Compile/Batch/StarU.lean is `PUX` with the further output dropped. -/
theorem PU_eq (k : ISK lam L) (b : List (X × Unit)) :
    PU W WP p k b = (PUX W WP p k b).bind fun o => OComp.pure o.1 := by
  unfold PU PUX
  rw [PtokU_eq, realQ_bind]
  rfl

/-- the committer, then the prover `PUX` on one batch: the verification key and the proofs; and
`RunX` (Compile/Batch/StarX.lean: what the honest run outputs beside the verification key and the
proofs): its field `isk`, then `bT`, `bL` from the further output of `CX`, and `leaf`, `perm`, `bB`
from that of `PUX` -/
def runAllBUX (i : I) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L ((IVK lam L × List (Prf lam L)) × RunX lam W.K L) :=
  (CX W WP p i).bind fun key => (PUX W WP p key.1.2 b).bind fun πs =>
    OComp.pure ((key.1.1, πs.1.val), ⟨key.1.2.1, key.2.1, key.2.2, πs.2.1, πs.2.2.1, πs.2.2.2⟩)

end Compile.Batch
