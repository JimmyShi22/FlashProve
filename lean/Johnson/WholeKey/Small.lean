-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Small.lean: two small equations on the scheme with the whole key published
(Johnson/WholeKey/Defs.lean), and what follows from the first by one call: INDEX BINDING of that
scheme, from the library's theorem at the whole key.

General theorems with their proofs. This file states no goal of the release.

  verifyW_eq_VCA   the verifier of Defs.lean, which re-packs key and proof and calls the compiled
      verifier at the key (root, out-of-domain sample) (verifyAtKeyRoot), IS the compiled verifier at the whole
      key (verifyAtFullKey, Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean), as programs, at every key, instance and proof.
      Why it holds: verifyAtKeyRoot is by definition verifyAtFullKey at a key whose list holds the one entry that the proof
      brings, and at the place 0. Where the whole key's list has no entry at the proof's place, verifyAtFullKey
      says no; the re-packing then lays an entry without a link proof, to which verifyAtFullKey says no as well.
  tabO_is_committerAtFixedCoins  the committer's program for a table (tabO), followed by (root, honest
      out-of-domain sample) and (index, randomness, salts), IS the library's committer behind its
      coins (committerAtFixedCoins, Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean), as programs: the same queries in the
      same order. tabO also keeps the tree's levels.
  argW_binding     index binding of argW, for every committer and every prover, with the library's
      extractor at the whole key, at the library's bound: VCA_binding_at
      (Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean), under that theorem's premises, called once. An
      adversarial committer here puts what is made once into the key and not into the proof.

Limits. Nothing on hiding or completeness. argW_binding reads the verifier alone: it holds at every
honest side, an idle one too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params)

/-- **The verifier is the compiled verifier at the whole key.** -/
theorem verifyW_eq_VCA (k : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    verifyW W S cA r₀ p k x π = verifyAtFullKey W S cA r₀ p k x π := by
  obtain ⟨cm, rcd, piT, links⟩ := k
  obtain ⟨leaf, copy, piB⟩ := π
  show verifyAtFullKey W S cA r₀ p ⟨cm, rcd, piT, [(links[leaf]?).getD (cm, rcd, none)]⟩ x ⟨0, copy, piB⟩ =
    verifyAtFullKey W S cA r₀ p ⟨cm, rcd, piT, links⟩ x ⟨leaf, copy, piB⟩
  unfold verifyAtFullKey
  cases hl : links[leaf]? with
  | none => cases piT <;> cases piB <;> simp
  | some l => simp

theorem verifyW_eq : verifyW W S cA r₀ p = verifyAtFullKey W S cA r₀ p :=
  funext fun k => funext fun x => funext fun π => verifyW_eq_VCA W S cA r₀ p k x π

/-- **The committer's program for a table is the library's committer behind its coins**, which
forgets the levels. -/
theorem tabO_is_committerAtFixedCoins (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    ((tabO W S b₀ i r s).bind fun t =>
      OComp.pure ((⟨t.tree.root, L.recOf i t.r t.seed⟩ : KeyRoot lam L), (i, r, s))) =
      committerAtFixedCoins W S b₀ i r s := by
  unfold tabO committerAtFixedCoins committerTreeKeptByProver committerTreeRoot treeO seedsO
  rw [committerLeafHashes_eq]
  simp only [OComp.bind_assoc, OComp.bind]
  rfl

/-- **Index binding of the scheme with the whole key published**, at every honest side: the
library's theorem at the whole key, called once. -/
theorem argW_binding (h : HonestSide lam L Bd aT aL) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hbB : Err.Below εB εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent) (hW : OKA W cA) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      (argW W S cA r₀ p h) (extractorC0 W) (soundnessBoundOverTypedOracles W εs) :=
  VCA_binding_at W S cA r₀ p Ryes Rno wit eR εT εL εB εs sub hS hSd hbT hbL hbB hlT hlL hlB hcT hcL
    hco hW (argW W S cA r₀ p h) (verifyW_eq W S cA r₀ p)

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.verifyW_eq_VCA
#print axioms OnBytes.WholeKey.tabO_is_committerAtFixedCoins
#print axioms OnBytes.WholeKey.argW_binding
