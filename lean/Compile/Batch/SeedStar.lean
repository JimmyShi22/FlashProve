-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedStar.lean: the compiled scheme whose proving key isk is (i, seed). Definitions and
one statement only. (Words of this library: lean/GLOSSARY.md.)

What changes. Only C and P change. C samples one seed and derives all its coins from it through the
auxiliary oracle `OracleName.other` (Rom/SpecDerive.lean); it keeps (i, seed) in place of isk. For each
batch P samples a copy with a fresh coin, derives the `Node` of that copy again (the randomness of
its encoding, its salts, its tree) and nothing else, and runs the batch on it with fresh coins. It
recomputes neither the `Node` of the first encoding nor any proof string of Link.

For which schemes. The transformation is stated for every scheme `argOf WP p F`, `F : Face`:
* its committer is the committer C of Compile/Batch/Star.lean, followed by a function `key` of what
  C returns (what is published);
* its prover samples a copy and then runs a token program `bat` whose arguments are the index i, the
  number of the copy, its `Node` and the batch b. It runs on the whole store of secret strings;
  `TokFree` (below) says that it reads there only what its tokens name;
* its verifier is any oracle algorithm.

The scheme `argB` of Compile/Batch/Star.lean itself is not of this form: its proofs repeat Link's
proof string of the copy, which the prover would have to recompute. `argBKE`, which has the entries
in ivk, is (Compile/Batch/SeedFace.lean: `argBKE_eq`); its programs have the two properties below if
L.maxBatchSize = 2 ^ W.depthReq (Compile/Batch/StepS.lean).

Two properties of `bat` and V are required, which are properties of programs and not of
distributions:
* `Face.TokFree`: `bat` does not look at the numbers of its tokens (`Compile.Seed.Par`,
  Compile/SeedKit.lean): run with the tokens of the `Node` renumbered, on the store with a block of
  consecutive strings removed, it makes the same queries, takes the same samples and returns the
  same result;
* `Face.NoOther`: `bat` and V never query the auxiliary oracle.

An answer of `OracleName.other` has λ bits, and some samples of C have far more outcomes. So every sample of
C is first made from small samples (Rom/Blocks.lean: the parameter bk), and these are derived.

`Spec.seedMainB` (proof: Compile/Batch/SeedMain.lean): if `argOf WP p F` has the three properties
(`IsZKCPArgWith`, ZKCP/Gen.lean: its fields `completeness`, `indexBinding`, `indexPrivacy`) with α,
ε, ζ, in this order, if σ.o = `OracleName.other` and σ.bias bk.w = 0, and if F has the two properties, then
`argSeed` has them (the three) with the same extractor and simulator; completeness error α + b; the
same ε; ζ(t, N) + b + t / (number of seeds). b bounds the bias, along a path of C, of the samples
made from small ones; t bounds the adversary's queries to all oracles.

Limits. Nothing is said about running time or memory: C still builds all M + 2 encodings, trees and
proofs. The derivation is through a random oracle, where the implementation uses a stream cipher
under the seed. P's own coins (the copy, the placement, the coins and salts of the batch) stay fresh
in every call. isk is (i, seed) and nothing else: the implementation also keeps each copy's root and
one level ℓ of its tree, which (i, seed) and the oracles determine (what a prover may keep:
Rom/Cache.lean; that cache: Compile/Batch/SeedCache.lean; the prover that recomputes the randomness
of the encoding and the blocks of 2^ℓ leaves that hold a position that it shows:
Compile/Batch/SeedLazyDefs.lean). Completeness against an adaptive environment: not here. This file
does not define a committer that builds only the first encoding and Test's proof, and proves nothing
on one.

Labels. In Rom/SpecDerive.lean the label of a derived sample is one running counter. The first small
sample of copy j has the number `off` .. j = (samples of the first encoding's `Node` and of Test) +
j · (samples of a copy), which does not depend on the run. Compile/Batch/SeedLabel.lean reads that
counter as (purpose, counter inside the purpose).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.Star
import Compile.Batch.RealQ
import Compile.SeedFix

noncomputable section

open Rom Iop ZKCP
open scoped ENNReal

namespace Compile.Batch
namespace Seed

open Compile.Seed (Par upTree)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## The weighted numbers of uniform samples -/

/-- the phases of Compile/Batch/Prover.lean, without their tokens -/
inductive Ph
  | first
  | loc
  | shr
  | aft

def Ph.afterLo : Ph → Ph
  | .first => .loc
  | .loc => .loc
  | .shr => .aft
  | .aft => .aft

def phOf : PhT → Ph
  | .first => .first
  | .loc => .loc
  | .shr _ => .shr
  | .aft => .aft

/-- the leaves of the tree over a component: 2^d if the component has a tree (Iop/BatchWire.lean:
has0, hasJ), else none -/
def nLv (has : Bool) (d : ℕ) : ℕ := has.toNat * 2 ^ d

/-- the leaves of all trees over prover messages that the chains of n slots build from the phase ph
on; every one of them is salted (the request tree has no salts). A component without a tree has no
leaf. -/
def cChainB {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Ph → ℕ → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (a, A), (w, W), ph, n =>
      match a.kind, ph with
      | .lo, ph => n * nLv w.hasJ w.depthJ + cChainB s A W ph.afterLo n
      | .sh, .loc => n * nLv w.hasJ w.depthJ + nLv w.has0 w.depth0 + cChainB s A W .shr n
      | .sh, .shr => nLv w.has0 w.depth0 + cChainB s A W .shr n
      | .sh, ph => cChainB s A W ph n

/-- the weighted number of uniform samples of one execution of the compiled prover with n slots: the
shared coins; for each slot its coins and the salt of its chain; the salts of all leaves. A sample
with m + 1 outcomes counts μ m. -/
def cProveB (μ : ℕ → ℕ) (sMT sFS : ℕ) {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {Wt : Type} {H : BatchHonestProver Q Wt} (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (n : ℕ) : ℕ :=
  μ wp.coin0.n +
    (n * (μ wp.coin.n + μ (2 ^ sFS - 1)) +
      cChainB Q.loc.shape Q.ann wq.sh .first n * μ (2 ^ sMT - 1))

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (μ : ℕ → ℕ)

/-- the weighted number of samples of a `Node`: the randomness of the encoding, and a salt for each
of its L.wordLength symbols that has a leaf -/
def cNode : ℕ :=
  μ WP.ri.n +
    ((List.range (2 ^ W.depth)).filter fun j => decide (j < L.wordLength)).length * μ (2 ^ p.sMT - 1)

/-- the weighted number of samples of a copy: its `Node` and its run of Link -/
def cLeaf : ℕ := cNode W WP p μ + cProveB μ p.sMT p.sFS W.Lk WP.Lk 1

/-- the weighted number of samples of C before copy j -/
def off (j : ℕ) : ℕ := cNode W WP p μ + cProveB μ p.sMT p.sFS W.T WP.T 1 + j * cLeaf W WP p μ

/-! ## Schemes over the committer of Compile/Batch/Star.lean -/

/-- the tokens of a `Node`, shown through Life2.up -/
def upNode (N₀ δ : ℕ) (nd : Node lam L) : Node lam L := ⟨nd.r, upTree N₀ δ nd.tree⟩

/-- What such a scheme is made of, beside the committer of Compile/Batch/Star.lean. -/
structure Face (W : QueryLayout lam L) (IVK' Pf' : Type) where
  /-- what is published: a function of what C returns, without the store of secret strings -/
  key : IVK lam L → IskH lam L → IVK'
  /-- one batch: given the index, the number of the sampled copy and its `Node` (none: there is no
  such copy) -/
  bat : I → ℕ → Option (Node lam L) → (b : List (X × Unit)) → St lam W.K L (Gen.Slots Pf' b)
  V : IVK' → X → Pf' → TypedOracleComputation lam W.K L Bool

variable {W} {IVK' Pf' : Type} (F : Face W IVK' Pf')

/-- The program of a batch does not look at the numbers of its tokens. -/
def Face.TokFree : Prop :=
  ∀ (N₀ δ : ℕ) (i : I) (j : ℕ) (nd : Node lam L) (b : List (X × Unit)),
    Par N₀ δ Eq (F.bat i j (some (upNode N₀ δ nd)) b) (F.bat i j (some nd) b)

/-- The program of a batch and the verifier never query the auxiliary oracle. -/
structure Face.NoOther : Prop where
  bat : ∀ i j nd b vs, (eraseR (F.bat i j nd b) vs).Avoids OracleName.other
  V : ∀ v x π, (F.V v x π).Avoids OracleName.other

/-- The scheme given by the record F. As in Compile/Batch/Star.lean, C and P are what `erase` makes
of the programs, with every query to a ghost name `fbw t k` turned into the query to `fb t`
(Compile/Batch/RealQ.lean: eraseR = realQ after erase): neither C nor P queries a ghost name. (The
program of a `Node`, nodeP', has no Fiat-Shamir query, so `erase` gives it no query to a ghost
name.) -/
def argOf : Gen.Arg (spec lam W.K L) I X Unit IVK' (ISK lam L) Pf' where
  C := fun i => (C W WP p i).bind fun o => .pure (F.key o.1 o.2.1, o.2)
  P := fun k b =>
    .sample p.M fun j =>
      (eraseR (F.bat k.1.i j.val (k.1.leaves[j.val]?.map LeafRec.node) b) k.2).bind
        fun o => .pure o.1
  V := F.V

variable (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- its committer with every sample made from small ones -/
def Cb (i : I) : TypedOracleComputation lam W.K L (IVK' × ISK lam L) := ((argOf WP p F).C i).blocks bk

/-- the scheme with that committer -/
def argBk : Gen.Arg (spec lam W.K L) I X Unit IVK' (ISK lam L) Pf' :=
  withC (argOf WP p F) (Cb WP p F bk)

/-- The prover with the seed: a uniform copy j with a fresh coin; the `Node` of copy j, derived
again under the seed, on an empty store; the batch on that `Node`, with fresh
coins. -/
def PS (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (Gen.Slots Pf' b) :=
  .sample p.M fun j =>
  (((erase (nodeP' W WP p k.1) []).blocks bk).derive σ k.2 (off W WP p bk.m j.val)).bind fun a =>
  (eraseR (F.bat k.1 j.val (some a.1) b) a.2).bind fun o => .pure o.1

/-- The scheme given by F with the proving key (i, seed). -/
def argSeed : Gen.Arg (spec lam W.K L) I X Unit IVK' (I × Fin (σ.sd + 1)) Pf' :=
  derivedWith (argBk WP p F bk) σ (PS WP p F bk σ)

end Seed

/-! ## The statement -/

/-- Under the hypotheses below on σ, bk, b and F: the scheme with isk = (i, seed) has the three
properties of `argOf` (`Gen.IsZKCPArgWith`: `completeness` with α, `indexBinding` with ε,
`indexPrivacy` with ζ), with the same extractor and simulator, with b added to α and b + t / (number
of seeds) to ζ. -/
def Spec.seedMainB : Prop :=
  ∀ (I X PP : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (IVK' Pf' : Type) (F : Seed.Face W IVK' Pf') (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))
      (R : Gen.RelPair I X Unit PP) (B : ℕ) (E : Gen.Extractor (spec lam W.K L) I X Unit IVK' Pf')
      (Sim : Gen.Simulator (spec lam W.K L) PP IVK' X Pf') (α b : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    σ.o = OracleName.other → σ.bias bk.w = 0 → (∀ i, (C W WP p i).pathBiasB bk ≤ b) →
    F.TokFree → F.NoOther → Gen.IsZKCPArgWith R (Seed.argOf WP p F) B E Sim α ε ζ →
    Gen.IsZKCPArgWith R (Seed.argSeed WP p F bk σ) B E Sim (α + b) ε
      (fun t N => ζ t N + b + (t : ℝ≥0∞) / (σ.sd + 1 : ℕ))

end Compile.Batch
