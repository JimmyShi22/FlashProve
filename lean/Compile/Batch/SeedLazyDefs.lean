-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLazyDefs.lean: the lazy prover. Definitions and the statement only. (Words of this
library: lean/GLOSSARY.md.)

`PL`: a prover for the scheme `argP` of Compile/Batch/StarS.lean (isk = (i, seed)) that keeps beside
its key the cache of Compile/Batch/SeedCache.lean (for each copy the root of its tree and the
digests of one level ℓ) and recomputes, of the `Node` of the sampled copy, the randomness of the
encoding and the blocks of 2^ℓ leaves that hold a position that it shows. For each batch:
 (1) a uniform copy j with a fresh coin; the stored pair (root, level) of copy j; if there is none,
     the batch ends without a proof;
 (2) the stored level is hashed up to a root (`hi`); if that root is not the stored one, the batch
     ends without a proof;
 (3) the randomness r of the copy's encoding is derived under the seed (`rD`: the first sample of
     the `Node`), and nothing else of the `Node`;
 (4) a sampled placement (uniform if `WP.perm` has `Enum.OK`, Iop/Wire.lean); all chains of the
     compiled prover `proveBU` of Compile/Batch/ProverU.lean are run, on an empty store, from the
     stored root (`chainsU`: the part of `proveBU` before the proof strings; of the trees over the
     encoded index it needs only the roots); in a round with proof-of-work bits every attempt is a
     query to the Fiat-Shamir oracle of the protocol (Compile/Batch/RealQ.lean: `eraseR`: the ghost
     names written back);
 (5) then, slot by slot, for a slot whose proof string is made: for each position p of the encoded
     index that the slot's verifier reads, the block of 2^ℓ leaves that holds the leaf of p
     (`W.B.ext.leaf p`; it is p under `W.OKG`) is derived again under the seed, on an empty store,
     at the counter at which the committer derived it (`blockD`), and hashed up ℓ levels; if its
     root is not the stored digest number p / 2^ℓ, the batch ends without a proof; the opening of p
     is the salt of its leaf and the path inside the block followed by the path in `hi` (`opL`);
 (6) the proof string of the slot is made with these openings (`finishSlotL`; `finishSlotG`:
     `finishSlot` of Compile/Batch/Prover.lean with the openings in the encoded index given as
     data).

`argPL`: the scheme `argP` with that cache and that prover (Rom/Cache.lean: `withCache`).
`Spec.lazyGr`: if `W.OKG` and ℓ ≤ W.depth, it has the output distributions of `argP`, for all oracle
functions. Proof: Compile/Batch/SeedLazy.lean.

Difference from the implementation that it removes. In argP the prover derives the whole `Node` of
the sampled copy (all 2^depth leaves with their salts, all levels). The implementation keeps one
level of each copy's tree and recomputes only the shown columns.

How to read the definitions.
* A block is derived once for each read position in it, and once more for each slot that reads it:
  nothing is remembered between two openings.
* A slot that is empty, withheld, or for which no proof string is made derives no block.
* "Without a proof": the value `no j b`, a parameter, as in Compile/Batch/SeedCache.lean; `noK` is
  the value that the prover of `argBKE` (Compile/Batch/StarKE.lean) returns where it has no `Node`.
* The implementation, after such a stop, also ends the service that runs batch after batch. Lean's P
  is one call for one batch and has no service, so that has no counterpart here.

Limits. No statement on cost. r is derived whole (as the implementation expands a copy's mask seed).
The symbols of the encoded index at the leaves of a block, and the honest strategy's messages, are
Lean's functions `L.encodeIndex` and `L.honestOnlineBatchProver` of (i, r): how much of them a program must compute is not a
matter of these definitions. Nothing is said on a cache that the committer has not written, beyond
what the definitions show: a missing entry and two comparisons, each of which ends the batch.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedCache
import Compile.Batch.StarS

noncomputable section

open Rom Iop ZKCP

namespace Compile.Batch
namespace Seed

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. The compiled prover in two parts, for any `BatchInteractiveOracleProof` -/

/-- the openings in the external strings, as a proof string holds them -/
abbrev ExtF (lam : ℕ) (E : ExtSpec) : Type := E.Pos → Option (Opening lam E.Sym)

section Prove
variable {K : ℕ} (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

/-- The first part of `proveBU`: the shared coins, the slots at the start, all Fiat-Shamir chains.
cms: the roots of the trees over the external strings. -/
def chainsU (xs : List (Option Y)) :
    St lam K L (H.Coin0 × (List (SlotAcc lam K (Y × H.Coin)) × Acc0)) :=
  (drawT wp.coin0).bind fun c0 =>
  (eachM (initSlotU sFS Q H wp w c0) xs).bind fun zs =>
  (chainTU sMT t cms (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape Q.ann wq.sh embS embP 0
      .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩).bind fun out =>
  Step.pure (c0, out)

/-- The proof string of slot j, the openings in the external strings given: the definition of
`finishSlot`; ext says, for each set of read positions, what the field ext of the proof string
is. -/
def finishSlotG (ext : (E.Pos → Bool) → ExtF lam E) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    St lam K L (Option (OneProtocolProof lam Q)) :=
  let ρ := rhoOf Q.loc.shape Q.ann wq.sh acc.blocks
  let τ := ((H.one.strat w x (c0, cj)).run ρ).1
  let roots := rootToks acc.trees a0.trees
  let path := (a0.req.map fun rq => pathOf rq.levels j).getD []
  let anc := (a0.req.map fun rq => ancOf rq.levels j).getD []
  let pls := putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse τ.plains
  haveI := wp.decW w x ρ
  if ρ ∈ H.one.withheld w x then pure none
  else
    Step.reveal (acc.toks.headD 0 ::
        (roots ++ path ++ (a0.req.map TTree.root).toList ++ anc ++ acc.toks ++
          a0.toks ++ (acc.dead ++ a0.dead))) fun vs =>
    haveI := wq.decO
    haveI := wq.ext.dec
    (opensB Q.loc.shape Q.ann wq.sh τ acc.trees a0.trees
        (fun p => decide (p ∈ Q.loc.reads x ρ pls))).bind fun f =>
    pure (some
      ⟨vs.headD [],
        ((vs.drop 1).take roots.length).map (digD lam),
        pls, f,
        ext (fun p => decide (p ∈ Q.loc.extReads x ρ)),
        digD lam (vs.getD (1 + roots.length + path.length) []),
        j,
        ((vs.drop (1 + roots.length)).take path.length).map (digD lam)⟩)

/-- the proof string of slot j, if it holds a request and fl says that a proof string is made -/
def slotG (ext : (E.Pos → Bool) → ExtF lam E) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0)
    (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) :
    St lam K L (Option (OneProtocolProof lam Q)) :=
  match acc.x with
  | some (x, cj) => if fl j then finishSlotG Q H wq wp w ext c0 a0 j x cj acc else pure none
  | none => pure none

/-- the definition of `finishAll`, with `finishSlotG` -/
def finishAllG (ext : (E.Pos → Bool) → ExtF lam E) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ℕ → List (SlotAcc lam K (Y × H.Coin)) → St lam K L (List (Option (OneProtocolProof lam Q)))
  | _, [] => pure []
  | j, acc :: zs =>
      (slotG Q H wq wp w ext fl c0 a0 j acc).bind fun π =>
      (finishAllG ext fl c0 a0 (j + 1) zs).bind fun r => pure (π :: r)

/-- The openings of the read positions, each made when it is needed. opL q: the salt and the path of
leaf q, or none; none ends everything. The recursion is that of opensExtB. -/
def opensExtL (we : WireE E) (y : E.Str)
    (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))) (isRead : E.Pos → Bool) :
    List E.Pos → TypedOracleComputation lam K L (Option (ExtF lam E))
  | [] => .pure (some fun _ => none)
  | p :: ps => (opensExtL we y opL isRead ps).bind fun of =>
      match of with
      | none => .pure none
      | some f =>
          if isRead p then
            (opL (we.leaf p)).bind fun oo =>
              .pure (oo.map fun o => @Function.update _ _ we.dec f p (some ⟨E.rd y p, o.1, o.2⟩))
          else .pure (some f)

/-- The proof string of slot j, with openings made when they are needed, on the store vs; none: an
opening has failed. A withheld slot makes no opening. -/
def finishSlotL (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))) (c0 : H.Coin0) (a0 : Acc0)
    (j : ℕ) (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    TypedOracleComputation lam K L (Option (Option (OneProtocolProof lam Q) × List Bits)) :=
  let ρ := rhoOf Q.loc.shape Q.ann wq.sh acc.blocks
  haveI := wp.decW w x ρ
  if ρ ∈ H.one.withheld w x then .pure (some (none, vs))
  else
    haveI := wq.ext.dec
    (opensExtL wq.ext (H.ext w) opL
        (fun p => decide (p ∈ Q.loc.extReads x ρ)) wq.ext.all).bind fun og =>
    match og with
    | none => .pure none
    | some gx =>
      (erase (finishSlotG Q H wq wp w (fun _ => gx) c0 a0 j x cj acc) vs).bind fun o =>
        .pure (some o)

/-- the proof string of slot j, if it holds a request and fl says that a proof string is made -/
def slotL (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))) (fl : ℕ → Bool) (c0 : H.Coin0)
    (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    TypedOracleComputation lam K L (Option (Option (OneProtocolProof lam Q) × List Bits)) :=
  match acc.x with
  | some (x, cj) =>
    if fl j then finishSlotL Q H wq wp w opL c0 a0 j x cj acc vs else .pure (some (none, vs))
  | none => .pure (some (none, vs))

/-- the proof strings of all slots from number j on; none: an opening has failed -/
def finishAllL (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))) (fl : ℕ → Bool)
    (c0 : H.Coin0) (a0 : Acc0) :
    ℕ → List (SlotAcc lam K (Y × H.Coin)) → List Bits →
    TypedOracleComputation lam K L (Option (List (Option (OneProtocolProof lam Q)) × List Bits))
  | _, [], vs => .pure (some ([], vs))
  | j, acc :: zs, vs =>
      (slotL Q H wq wp w opL fl c0 a0 j acc vs).bind fun o1 =>
      match o1 with
      | none => .pure none
      | some o =>
        (finishAllL opL fl c0 a0 (j + 1) zs o.2).bind fun o2 =>
          .pure (o2.map fun (r : List (Option (OneProtocolProof lam Q)) × List Bits) => (o.1 :: r.1, r.2))

end Prove

/-! ## Part 2. What is recomputed of a `Node` -/

/-- the string that the salt token of a leaf denotes; the empty string for a leaf without a salt -/
def strOf (vs : List Bits) : Option (Tok × Tok) → Bits
  | some x => vs.getD x.1 []
  | none => []

variable (W : QueryLayout lam L)
  (WP : WireBP L) (p : Params) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- leaf number j of the tree over the encoding of i with the randomness r: a symbol, salted; or
padding (the function in nodeP' of Compile/Batch/Star.lean) -/
def leafFn (i : I) (r : L.EncodingRandomness) (j : ℕ) : Body L × Bool :=
  if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true) else (none, false)

/-- the randomness of the encoding of copy j, derived under the seed: the first sample of the
`Node` -/
def rD (k : I × Fin (σ.sd + 1)) (j : ℕ) : TypedOracleComputation lam W.K L (L.EncodingRandomness × List Bits) :=
  ((erase (drawT (lam := lam) (K := W.K) (L := L) WP.ri) []).blocks bk).derive
    σ k.2 (off W WP p bk.m j)

/-- Block u of 2^ℓ leaves of the tree of copy j, derived under the seed on an empty store: their
digests, the tokens of their salts, the store. The counter: that of the `Node`, the sample for r,
and a salt for each of the min (u 2^ℓ) n salted leaves before the block. -/
def blockD (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (u : ℕ) :
    TypedOracleComputation lam W.K L ((List (Dig lam) × List (Option (Tok × Tok))) × List Bits) :=
  ((erase (leavesE p.sMT ((List.range (2 ^ ℓ)).map fun t => leafFn k.1 r (u * 2 ^ ℓ + t)))
      []).blocks bk).derive
    σ k.2 (off W WP p bk.m j + bk.m WP.ri.n + min (u * 2 ^ ℓ) L.wordLength * bk.m (2 ^ p.sMT - 1))

/-- The salt and the path of leaf q, from its block, the stored level lvl and the levels hi from it
up; none if the root of the block is not the stored digest. -/
def opL (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (lvl : List (Dig lam))
    (hi : List (List (Dig lam))) (q : ℕ) :
    TypedOracleComputation lam W.K L (Option (Bits × List (Dig lam))) :=
  (blockD W WP p bk σ ℓ k j r (q / 2 ^ ℓ)).bind fun a =>
  (levelsM hashTreeNode ℓ a.1.1).bind fun lo =>
  .pure (if lvl[q / 2 ^ ℓ]? = some (rootOf lo) then
      some (strOf a.2 (a.1.2.getD (q % 2 ^ ℓ) none), pathOf lo (q % 2 ^ ℓ) ++ pathOf hi (q / 2 ^ ℓ))
    else none)

/-! ## Part 3. The prover and the scheme -/

/-- what the prover of `argBKE` returns where it has no `Node`: for each request the proof
(j, none) -/
def noK (j : ℕ) (b : List (X × Unit)) : Gen.Slots (PrfK lam L) b :=
  fitLen ⟨0, none⟩ b.length ((b.map Prod.fst).map fun _ => ⟨j, none⟩)

/-- steps 4 to 6: the batch on copy j, once the stored pair st has been read, the levels hi from
the stored level up have been hashed and r has been derived -/
def PLrun (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b)
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : ℕ) (st : Dig lam × List (Dig lam))
    (hi : List (List (Dig lam))) (r : L.EncodingRandomness) :
    TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  .sample WP.perm.n fun z =>
  (eraseR (chainsU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
        (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [st.1] (k.1, r)
        (slotsOfReq (WP.perm.e z) (b.map Prod.fst)))
      []).bind fun o =>
  (finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) (opL W WP p bk σ ℓ k j r st.2 hi)
      (slotFlags (WP.perm.e z) fun _ => true) o.1.1 o.1.2.2 0 o.1.2.1 o.2).bind fun oπ =>
  match oπ with
  | none => .pure (no j b)
  | some πs =>
    .pure (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length (WP.perm.e z) πs.1))

/-- steps 1 (second half) to 6: the batch on copy j -/
def PLat (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) (j : ℕ) :
    TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  match kc.2[j]? with
  | none => .pure (no j b)
  | some st =>
    (levelsM hashTreeNode (W.depth - ℓ) st.2).bind fun hi =>
    if rootOf hi = st.1 then
      (rD W WP p bk σ kc.1 j).bind fun ra => PLrun W WP p bk σ ℓ no kc.1 b j st hi ra.1
    else .pure (no j b)

/-- The lazy prover. -/
def PL (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  .sample p.M fun j => PLat W WP p bk σ ℓ no kc b j.val

/-- The scheme with the proving key (i, seed, for each copy its root and one level of its tree) and
the lazy prover. -/
def argPL (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) :
    Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) ((I × Fin (σ.sd + 1)) × Ca lam) (PrfK lam L) :=
  withCache (argP W WP p bk σ) (cacheOf W WP p bk σ ℓ) (PL W WP p bk σ ℓ no)

end Seed

/-- If `W.OKG` (rounds may have proof-of-work bits) and ℓ ≤ W.depth, the scheme with the lazy prover
has the output distributions of `argP`, for every choice of the oracle functions (the prover: on
every key that the committer of `argPL` can return under them). -/
def Spec.lazyGr : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ)
      (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b),
    W.OKG → ℓ ≤ W.depth → (argP W WP p bk σ).SameRunVia Prod.fst (Seed.argPL W WP p bk σ ℓ no)

end Compile.Batch
