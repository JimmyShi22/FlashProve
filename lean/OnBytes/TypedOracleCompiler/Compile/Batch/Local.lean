-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Local.lean: a second form of Compile/Batch/Local.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

Comments apart, every declaration of this file has the text of Compile/Batch/Local.lean; what it
means changes with the definitions that it names.

The rest of this head is the head of Compile/Batch/Local.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Local.lean: for a query encoding (`m : OracleCoding (typedOracleFamily lam K L) lam`, Rom/Family.lean) in
which the Merkle oracles have one hash block (`m.blocks OracleName.leaf = 1` and the like), what is
extracted from a trace depends only on its entries at one-block oracles (`single m tr`,
Rom/Family.lean) (words of this library: lean/GLOSSARY.md).

The step to one hash function (Rom/Family.lean) requires an extractor to read only such entries
(`Rom.LocalTo`). Here: the string under a root of an encoded index (`extEnc_single`), a leaf of a
tree over oracles (`extLeaf_single`) and a slot value of a request tree (`extReq_single`) are the
same for a trace and for its one-block entries.
`localTo_of_extEnc` concludes `LocalTo` for every extractor whose first part is a function of
`extEnc` and whose second part reads no trace.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Events
import Rom.Family

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

namespace Local

/-- Entries that a view does not see can be left out. -/
theorem firstPre_filter {E Q D : Type} [DecidableEq D] (view : E → Option (Q × D)) (p : E → Bool)
    (h : ∀ e, p e = false → view e = none) (c : D) :
    ∀ tr : List E, Merkle.firstPre view (tr.filter p) c = Merkle.firstPre view tr c
  | [] => rfl
  | e :: tr => by
      have ih := firstPre_filter view p h c tr
      unfold Merkle.firstPre at ih ⊢
      cases hp : p e
      · have hn : Merkle.hit view c e = none := by
          unfold Merkle.hit
          rw [h e hp]
          rfl
        rw [List.filter_cons_of_neg (by simp [hp]), List.findSome?_cons, hn]
        exact ih
      · rw [List.filter_cons_of_pos hp, List.findSome?_cons, List.findSome?_cons, ih]

theorem preimage_filter {E D Y : Type} [DecidableEq D] {Ev : Merkle.Events E D}
    (V : Merkle.OraclePair Ev Y) (p : E → Bool) (hl : ∀ e, p e = false → V.leaf e = none)
    (hn : ∀ e, p e = false → V.node e = none) (tr : List E) :
    ∀ {t : Merkle.Shape} (q : t.Pos) (c : D), V.preimage (tr.filter p) q c = V.preimage tr q c
  | _, .here, c => firstPre_filter V.leaf p hl c tr
  | _, .left q, c => by
      simp only [Merkle.OraclePair.preimage,
        firstPre_filter V.node p hn c tr, preimage_filter V p hl hn tr q]
  | _, .right q, c => by
      simp only [Merkle.OraclePair.preimage,
        firstPre_filter V.node p hn c tr, preimage_filter V p hl hn tr q]

end Local

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem extLeaf_single (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extLeaf (single m tr) d c j = extLeaf tr d c j := by
  unfold extLeaf single
  refine Local.preimage_filter (pairM lam K L) _ ?_ ?_ tr _ c
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | (simp [hl] at ho)
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | (simp [hn] at ho)

theorem extReq_single (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : m.blocks OracleName.rleaf = 1)
    (hn : m.blocks OracleName.rnode = 1) (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extReq (single m tr) d c j = extReq tr d c j := by
  unfold extReq single
  refine Local.preimage_filter (pairR lam K L) _ ?_ ?_ tr _ c
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | (simp [hl] at ho)
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | (simp [hn] at ho)

/-- If leaf and node have one hash block: the string under a root of an encoded index is read from
one-block entries. -/
theorem extEnc_single (W : QueryLayout lam L) (m : OracleCoding (typedOracleFamily lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Tc W) (cm : Dig lam) :
    extEnc W (single m tr) cm = extEnc W tr cm := by
  simp only [extEnc, extLeaf_single m hl hn]

/-- If leaf and node have one hash block: an extractor that decodes what the trace determines under
a root in ivk (`hEi`), and whose second part reads no trace (`hEw`), satisfies `LocalTo`. -/
theorem localTo_of_extEnc (W : QueryLayout lam L) (m : OracleCoding (typedOracleFamily lam W.K L) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) {Wt IVK Pf : Type}
    (E : ZKCP.Gen.Extractor (typedOracleFamily lam W.K L) I X Wt IVK Pf) (cm : IVK → Dig lam)
    (f : IVK → (Fin L.wordLength → L.Symbol) → Option I) (hEi : ∀ v tr, E.Ei v tr = f v (extEnc W tr (cm v)))
    (hEw : ∀ v tr x π tr' tr₁ tr₁', E.Ew v tr x π tr' = E.Ew v tr₁ x π tr₁') : LocalTo E m :=
  ⟨fun v tr => by rw [hEi, hEi, extEnc_single W m hl hn], fun v tr x π tr' => hEw v tr x π tr' _ _⟩

end TypedOracleCompiler.Compile.Batch
