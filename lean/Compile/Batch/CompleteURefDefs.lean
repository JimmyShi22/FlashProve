-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteURefDefs.lean: the hash work of the honest prover with free empty slots (no
query for an empty slot: `proveBU`, Compile/Batch/ProverU.lean), without tokens (a token is a
position in a store: Compile/Batch/CompleteRefDefs.lean). Definitions, and the rounds of `chainOU`
unfolded (`chainOU_lo`, `chainOU_join`, `chainOU_shr`) (words of this library: lean/GLOSSARY.md).

The counterparts, on strings, of the programs of Compile/Batch/ProverU.lean and
Compile/Batch/StarU.lean, as Compile/Batch/CompleteRefDefs.lean has them for
Compile/Batch/Prover.lean and Compile/Batch/Star.lean. A slot is an `Option`: `none` is an empty
slot, which does nothing.

  `rleavesOU`, `reqRootOU`  the leaves and the root of the request tree: the hash of a slot value;
                            for an empty slot a fresh uniform string (`rleavesTU`, `reqTU`)
  `chainOU`  the rounds (`chainTU`), in the same order; the algorithms of one slot in one round are
             `slotLoO`, `slotJoinO`, `hearO` of Compile/Batch/CompleteRefDefs.lean
  `proveOU`  one execution (`proveBU`): for each slot the hash blocks that it has seen; the empty
             list for an empty slot
  `batOU`, `RBU`  the small experiment: a fresh node (`nodeO`) and one batch on it

What they are for: for every fixed family of oracle functions, the event that the slot of a request
is bad (`Ref.badAt`) in the instrumented honest run has the distribution of `RBU`
(Compile/Batch/CompleteURef.lean; `lawBUG`, Compile/Batch/CompleteURefStarG.lean, under `W.OKG`,
`Fmt`); under lazily sampled oracles and the hypotheses there, the verifier randomness of any one
slot with a request is exactly uniform, except for the proof-of-work bits
(Compile/Batch/CompleteUUnif.lean). Test and Link are made by the committer, which is unchanged:
their small experiments are `Ref.RT` and `Ref.RL`.

Notation: `sMT`, `sFS`: natural numbers: the length of the salt of a leaf, and of the salt of a
chain (Compile/Batch/Verifier.lean); `t`: a `Tag` (Compile/Oracles.lean): test, link or onl; `cms`:
a `List (Dig lam)`: the external roots (`verifyB`, Compile/Batch/Verifier.lean); `embS`, `embP` say
how symbols and plain parts are written into queries (`verifyB`, Compile/Batch/Verifier.lean); `ph`:
a `PhO` (Compile/Batch/CompleteRefDefs.lean): `first`, `loc`, `shr ρ0` or `aft`; `.lo`, `.sh`
(`Kind`, Iop/Batch.lean): a round is called shared (sh) or local (lo) after its verifier message;
`.f4`, `.f5` (`Head`, Compile/Batch/Oracles.lean): (F4): the joining round; (F5): a later shared
round; `blk0 lam K` (Compile/Batch/Prover.lean): a `Blk lam K`: the blocks 0; `gr0` (a field of
`WireRB`, Iop/BatchWire.lean): an `Option (GrW ..)`: has the Fiat-Shamir query of a shared round,
formats (F4) and (F5), a test? none: no; `pl0`: `M0 → P0` (a field of `RAnn`, Iop/Batch.lean); P0,
Pj: the plain strings of m_0 and of m_j.
-/
import Compile.Batch.CompleteRefDefs
import Compile.Batch.StarU

noncomputable section

namespace Compile.Batch.RefU
open Iop Rom Compile.Batch.Ref

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- g on a slot with a request; nothing on an empty slot -/
def optO {σ τ : Type} (g : σ → TypedOracleComputation lam K L τ) : Option σ → TypedOracleComputation lam K L (Option τ)
  | none => OComp.pure none
  | some v => (g v).bind fun v' => OComp.pure (some v')

/-- the leaves of the request tree over the slot values cs; none: an empty slot -/
def rleavesOU : List (Option Bits) → TypedOracleComputation lam K L (List (Dig lam))
  | [] => OComp.pure []
  | some c :: t =>
    (askTypedOracle (L := L) (K := K) OracleName.rleaf c).bind fun d =>
      (rleavesOU t).bind fun r => OComp.pure (d :: r)
  | none :: t => (freshO lam).bind fun u => (rleavesOU t).bind fun r => OComp.pure (digD lam u :: r)

/-- the root of the request tree -/
def reqRootOU (depthReq : ℕ) (cs : List (Option Bits)) : TypedOracleComputation lam K L (Dig lam) :=
  (rleavesOU cs).bind fun ls =>
    (levelsM (rnodeV (L := L) (K := K)) depthReq ls).bind fun lv => OComp.pure (rootOf lv)

/-- the hash blocks that a slot has seen; the empty list for an empty slot -/
def blocksU {s : Shape} (v : Option (VSlot lam K X s)) : List (Blk lam K) :=
  (v.map VSlot.blocks).getD []

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam))

/-- All chains of a batch: for each slot the hash blocks that it has seen. (The four cases, as in
the head of Compile/Batch/Prover.lean: a local round (`.lo`): `optO` of `slotLoO` in each slot; the
joining round (`.sh` in the phase `loc`): `optO` of `slotJoinO` in each slot, the request root, the
query (F4); another shared round (`.sh` in the phase `shr`): the query (F5); a shared round at the
start or after the later local rounds: it has no format: nothing is hashed and the verifier message
is the one of the blocks 0.) -/
def chainOU (depthReq : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → PhO → SStrat s A →
    List (Option (VSlot lam K X s)) → TypedOracleComputation lam K L (List (List (Blk lam K)))
  | [], _, _, _, _, _, _, _, vs => OComp.pure (vs.map blocksU)
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), vs =>
      match a.kind, ph with
      | .lo, ph =>
          (eachO (optO (slotLoO sMT t cms a w (fun p => embS (.inl p))
                  (fun α => embP (.inl (.inr α))) i ph))
              vs).bind fun vs' =>
          chainOU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) vs'
      | .sh, .loc =>
          (eachO (optO
                (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i))
              vs).bind fun vs1 =>
          (reqRootOU depthReq (vs1.map (Option.map fun v => v.c))).bind fun rq =>
          (root0O sMT a w (fun p => embS (.inl p)) m0).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f4 cms (List.ofFn rq), rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 m0)).bind fun ans =>
          chainOU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            (.shr (List.ofFn ans.2)) (k0 (a.kind.shOf (w.chal ans.1)))
            (vs1.map (Option.map (hearO w ans.1)))
      | .sh, .shr ρ0 =>
          (root0O sMT a w (fun p => embS (.inl p)) m0).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f5 ρ0, rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 m0)).bind fun ans =>
          chainOU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            (.shr (List.ofFn ans.2)) (k0 (a.kind.shOf (w.chal ans.1)))
            (vs.map (Option.map (hearO w ans.1)))
      | .sh, ph =>
          chainOU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph
            (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (vs.map (Option.map (hearO w (blk0 lam K))))

section Unfold
variable (dR : ℕ) {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} (w : WireRB lam K r a)
  (W : RoundsQueryLayout lam K s A) (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (σ0 : SStrat (r :: s) (a, A))
  (vs : List (Option (VSlot lam K X (r :: s))))

theorem chainOU_lo (hk : a.kind = .lo) (ph : PhO) :
    chainOU sMT t cms dR (r :: s) (a, A) (w, W) embS embP i ph σ0 vs =
      (eachO
        (optO (slotLoO sMT t cms a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph))
        vs).bind fun vs' =>
          chainOU sMT t cms dR s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              ph.afterLo (σ0.2 (a.kind.shOf (w.chal (blk0 lam K)))) vs' := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

theorem chainOU_join (hk : a.kind = .sh) :
    chainOU sMT t cms dR (r :: s) (a, A) (w, W) embS embP i .loc σ0 vs =
      (eachO (optO (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i))
        vs).bind fun vs1 =>
          (reqRootOU dR (vs1.map (Option.map fun v => v.c))).bind fun rq =>
          (root0O sMT a w (fun p => embS (.inl p)) σ0.1).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f4 cms (List.ofFn rq), rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 σ0.1)).bind fun ans =>
          chainOU sMT t cms dR s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              (.shr (List.ofFn ans.2)) (σ0.2 (a.kind.shOf (w.chal ans.1)))
              (vs1.map (Option.map (hearO w ans.1))) := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

theorem chainOU_shr (hk : a.kind = .sh) (ρ0 : Bits) :
    chainOU sMT t cms dR (r :: s) (a, A) (w, W) embS embP i (.shr ρ0) σ0 vs
      = (root0O sMT a w (fun p => embS (.inl p)) σ0.1).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f5 ρ0, rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 σ0.1)).bind fun ans =>
          chainOU sMT t cms dR s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              (.shr (List.ofFn ans.2)) (σ0.2 (a.kind.shOf (w.chal ans.1)))
              (vs.map (Option.map (hearO w ans.1))) := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

end Unfold

end Rounds

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

/-- One execution of the protocol: for each slot the hash blocks that it has seen. cms are the roots
of the external trees. -/
def proveOU (xs : List (Option Y)) : TypedOracleComputation lam K L (List (List (Blk lam K))) :=
  (drawO wp.coin0).bind fun c0 =>
  (eachO (optO fun x => initO sFS Q H wp xin w c0 (some x)) xs).bind fun vs =>
  chainOU sMT t cms depthReq Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) vs

end Prove

/-! ## The small experiment, and the honest run -/

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- in a batch with the requests xs on a node: is the proof string of request number a, which is x,
`none`, or has a search over nonces of its transcript failed (Ref.badAt; without proof-of-work bits:
`none`) -/
def batOU (xs : List X) (a : Fin L.maxBatchSize) (x : X) (nd : L.EncodingRandomness × Dig lam) : TypedOracleComputation lam W.K L Bool :=
  (drawO WP.perm).bind fun σ =>
  (proveOU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩))
      id some W.depthReq [nd.2] (i, nd.1) (slotsOfReq σ xs)).bind fun bss =>
  OComp.pure (badAt L.onlineBatch L.honestOnlineBatchProver W.B WP.B (i, nd.1) x (σ a).val bss)

/-- a fresh node and one batch on it -/
def RBU (xs : List X) (a : Fin L.maxBatchSize) (x : X) : TypedOracleComputation lam W.K L Bool :=
  (nodeO W WP p i).bind (batOU W WP p i xs a x)

/-- the committer, then the prover with free empty slots on one batch: the verification key and the
proofs -/
def runAllBU (b : List (X × Unit)) : TypedOracleComputation lam W.K L (IVK lam L × List (Prf lam L)) :=
  (C W WP p i).bind fun key => (PU W WP p key.2 b).bind fun πs => OComp.pure (key.1, πs.val)

end Scheme

end Compile.Batch.RefU
