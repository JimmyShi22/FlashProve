-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarO.lean: the compiled scheme with pruned Merkle paths in keys and proofs.

The file has definitions and one statement. Keys and proofs of the compiled scheme hold proof
strings: the non-interactive proofs of the protocols Test, Link and Batch (a slot is one
request's part of Batch; words of this library: lean/GLOSSARY.md). In
Compile/Batch/Star.lean the key holds Test's proof string, and a proof holds Link's proof string and
a slot's. In Compile/Batch/StarK.lean the key also lists the entry (cm', Link's proof string) of
each of the M + 1 copies (second encodings of the index, each under its own root cm'; M is
`Params.M`), and a proof is the number of a copy with a slot's proof string. The verifier `verifyOneProtocol`
(Compile/Batch/Verifier.lean), in a tree that the wire record marks as pruned (`pr0`, `prJ`, `pr`),
reads of the Merkle paths of the opened positions only the sibling digests that it cannot compute
itself. Pruning (`pruneO`, Compile/Batch/Pruned.lean) replaces these paths by one list of the
digests that are read.

  `prunedK W p A`         A scheme `A` with the keys and proofs of Compile/Batch/StarK.lean: its
                          committer and prover followed by pruning, with the verifier `VKO`. The
                          proving key does not change.
  `fillIVKK`, `fillPrfK`  Maps back to full paths, used only in the analysis.

`Spec.pruneKeepsKGr` is proved in Compile/Batch/MainO.lean. Let the wire record `W` (tree depths,
leaf numbers, flags, limits, and how hash blocks give challenges) be well-formed (`W.OKG`,
Iop/BatchWire.lean; rounds may have proof-of-work bits). Then whatever bounds, extractor and
simulator a scheme `A` with the verifier `VK` has in the definition of ZKCP/Gen.lean, the pruned
scheme has the same bounds, with the extractor read through the maps back and the simulator followed
by pruning. (`VK` is the verifier of Compile/Batch/StarK.lean, the pruned scheme is
`prunedK W p A`.) It is stated for any such `A`, so that one statement covers the forms of the
scheme that differ only in committer and prover. That any such `A` has such bounds is not shown in
this file.

Notation: `R`: a `Gen.RelPair I X Unit PP`: two indexed relations R_yes ⊆ R_no with the public
parameters pp(i) (ZKCP/Gen.lean); `B`: a natural number: in `ValidBatch R B i b`, a batch of at most
B pairs (ZKCP/Gen.lean); `E`, `Sim`: a `Gen.Extractor`, a `Gen.Simulator` (ZKCP/Gen.lean); α, ε, ζ:
arguments of `IsZKCPArgWith` (ZKCP/Gen.lean): α stands in its field `completeness`, ε in
`indexBinding`, ζ in `indexPrivacy`; in ζ(t, N), t bounds the queries of `Vt ivk`, N counts batches
(`PrivacyFor`, ZKCP/Gen.lean); ε(tC, tP): in `HasIndexBindingWith`, tC and tP bound the queries of
`Ct` and of every `Pt st` (ZKCP/Gen.lean).

Limits: nothing is said about sizes (Compile/Batch/SizeO.lean). This statement carries over only
the bounds of that definition (`IsZKCPArgWith`, ZKCP/Gen.lean): not refined completeness
(`HasRefinedCompletenessError`, ZKCP/Gen.lean), nor any further property of the scheme with full
paths.
-/
import Compile.Batch.Pruned
import Compile.Batch.StarK
import Compile.Batch.Spec
import Compile.GenLe

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenLe
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## Keys and proofs -/

structure IVKO (lam : ℕ) (L : BatchProtocol I X) where
  cm : Dig lam
  piT : Option (BPrfO lam (BatchInteractiveOracleProof.ofProto L.offline))

structure PrfO (lam : ℕ) (L : BatchProtocol I X) where
  leaf : ℕ
  cm : Dig lam
  piL : Option (BPrfO lam (BatchInteractiveOracleProof.ofProto L.link))
  piB : Option (BPrfO lam L.onlineBatch)

abbrev LinksO (lam : ℕ) (L : BatchProtocol I X) : Type :=
  List (Dig lam × Option (BPrfO lam (BatchInteractiveOracleProof.ofProto L.link)))
abbrev IVKKO (lam : ℕ) (L : BatchProtocol I X) : Type := IVKO lam L × LinksO lam L

structure PrfKO (lam : ℕ) (L : BatchProtocol I X) where
  leaf : ℕ
  piB : Option (BPrfO lam L.onlineBatch)

variable (W : QueryLayout lam L)

def pruneIVK (v : IVK lam L) : IVKO lam L := ⟨v.cm, v.piT.map (pruneO W.T)⟩
def prunePrf (π : Prf lam L) : PrfO lam L :=
  ⟨π.leaf, π.cm, π.piL.map (pruneO W.Lk), π.piB.map (pruneO W.B)⟩
def pruneIVKK (v : IVKK lam L) : IVKKO lam L :=
  (pruneIVK W v.1, v.2.map fun e => (e.1, e.2.map (pruneO W.Lk)))
def prunePrfK (π : PrfK lam L) : PrfKO lam L := ⟨π.leaf, π.piB.map (pruneO W.B)⟩

def fillIVK (v : IVKO lam L) : IVK lam L := ⟨v.cm, v.piT.map (fillO W.T)⟩
def fillPrf (π : PrfO lam L) : Prf lam L :=
  ⟨π.leaf, π.cm, π.piL.map (fillO W.Lk), π.piB.map (fillO W.B)⟩
def fillIVKK (v : IVKKO lam L) : IVKK lam L :=
  (fillIVK W v.1, v.2.map fun e => (e.1, e.2.map (fillO W.Lk)))
def fillPrfK (π : PrfKO lam L) : PrfK lam L := ⟨π.leaf, π.piB.map (fillO W.B)⟩

/-! ## The verifiers -/

variable (p : Params)

/-- The verifier for pruned keys and proofs: `V` of Compile/Batch/Star.lean with the three verifiers
for pruned proof strings. -/
def VO (v : IVKO lam L) (x : X) (π : PrfO lam L) : TypedOracleComputation lam W.K L Bool :=
  match v.piT, π.piL, π.piB with
  | some πT, some πL, some πB =>
      if π.leaf ≤ p.M then do
        let a ← vTO W p.sMT p.sFS v.cm πT
        let b ← vLO W p.sMT p.sFS v.cm π.cm πL
        let c ← vBO W p.sMT p.sFS π.cm x πB
        pure (a && b && c)
      else pure false
  | _, _, _ => pure false

/-- The proof (number of a copy, the slot's proof string) with the entry of that number from the
key, as `reK ∘ liftK` of Compile/Batch/StarK.lean. -/
def reKO (ℓ : LinksO lam L) (π : PrfKO lam L) : PrfO lam L :=
  match ℓ[π.leaf]? with
  | some e => ⟨0, e.1, e.2, π.piB⟩
  | none => ⟨0, default, none, π.piB⟩

/-- The verifier for pruned keys that list the entries, and pruned proofs. -/
def VKO (v : IVKKO lam L) (x : X) (π : PrfKO lam L) : TypedOracleComputation lam W.K L Bool := VO W p v.1 x (reKO v.2 π)

/-- The verifier of Compile/Batch/StarK.lean, under a name: `(argBK W WP p).V = VK W p` by
definition. -/
def VK (v : IVKK lam L) (x : X) (π : PrfK lam L) : TypedOracleComputation lam W.K L Bool :=
  V W p v.1 x (reK v.2 (liftK π))

/-! ## The schemes -/

/-- A scheme with keys and proofs of Compile/Batch/StarK.lean, pruned. -/
def prunedK {ISK : Type} (A : Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) ISK (PrfK lam L)) :
    Gen.Arg (spec lam W.K L) I X Unit (IVKKO lam L) ISK (PrfKO lam L) :=
  mapArg A (pruneIVKK W) (prunePrfK W) (VKO W p)

variable (WP : WireBP L)

/-- The compiled scheme with the entries in the verification key and pruned Merkle paths. -/
def argBKO : Gen.Arg (spec lam W.K L) I X Unit (IVKKO lam L) (ISK lam L) (PrfKO lam L) :=
  prunedK W p (argBK W WP p)

/-! ## The statement -/


/-- For a well-formed wire record, whose rounds may have proof-of-work bits (`W.OKG`), and a scheme
whose verifier is `VK`: pruning keeps `Gen.IsZKCPArgWith`, with the same bounds. -/
def Spec.pruneKeepsKGr : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p : Params), W.OKG →
  ∀ (ISK PP : Type) (A : Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) ISK (PrfK lam L)),
    A.V = VK W p →
  ∀ (R : Gen.RelPair I X Unit PP) (B : ℕ)
      (E : Gen.Extractor (spec lam W.K L) I X Unit (IVKK lam L) (PrfK lam L))
      (Sim : Gen.Simulator (spec lam W.K L) PP (IVKK lam L) X (PrfK lam L))
      (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    Gen.IsZKCPArgWith R A B E Sim α ε ζ →
    Gen.IsZKCPArgWith R (prunedK W p A) B (pullEK (fillIVKK W) (fillPrfK W) E)
      (pushSimK (pruneIVKK W) (prunePrfK W) Sim) α ε ζ



end Compile.Batch
