-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/StrictClause.lean: the third clause of OnBytes/TypedOracleCompiler/Slice/PlainClause.lean for the
sibling's compiled verifier with the strict format. The plain half of
a file of this project that is not in this library said again over the sibling's types.

OnBytes/TypedOracleCompiler/Slice/PlainClause.lean speaks of the sibling's `verifyB`, which takes one whole path for
each opening and does not test the format of the string. The verifier of the compiled scheme is
`verifyOneProtocol`: it tests the strict format (among other things the lengths sMT, sFS of the salts) and,
where the wiring's flags say so, walks up a tree once over a pruned set of paths. By the sibling's
`runsIn_verifyB_of_strict`, what the strict verifier accepts, `verifyB` accepts with other paths,
within the same trace, if the wiring is lawful. The other string has the same symbols and salts in
its openings, so a reading keeps its external openings if it keeps the first string's
(`keeps_withPaths`).

Main definition: `Written.verifierS`.
Main theorems: `keeps_withPaths`, `plainBad_langS`.

Not claimed. Nothing beyond that file's third clause but the other verifier, and for the named set
alone: no form with "there is" is stated for the strict verifier. What that file's head says is not
claimed is not claimed here either. The strict format's tests are used for nothing: that R keeps the
string's external openings stays a hypothesis. By the sibling's own page its definitions of the
strict format tree by tree are pinned by no theorem. The batch's half stands in
OnBytes/TypedOracleCompiler/Slice/BatchClause.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.PlainClause
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestSound

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A string with other paths in its openings has the same symbols and salts there: a reading that
keeps the external openings of the one keeps those of the other. -/
theorem keeps_withPaths {embE : L.Symbol → L.Bd} (R : Reading L embE) {Y : Type}
    {Q : BatchInteractiveOracleProof Y (oneExternalString L.wordLength L.Symbol)}
    (π : OneProtocolProof lam Q) (P1 : OPos Q.loc.shape → List (Dig lam))
    (P2 : (oneExternalString L.wordLength L.Symbol).Pos → List (Dig lam))
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt) :
    ∀ p op, (π.withPaths P1 P2).ext p = some op → R.keeps p op.sym op.salt := by
  intro p op h
  have h' : (π.ext p).map (fun o => (⟨o.sym, o.salt, P2 p⟩ : Opening lam L.Symbol)) = some op := h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact hk p o ho

/-- The compiled verifier of a written protocol with the strict format: the sibling's `verifyOneProtocol`. -/
noncomputable def Written.verifierS {W : QueryLayout lam L} (Z : Written W) (sMT sFS : ℕ) (cm : Dig lam)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto Z.P)) : TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Z.t (BatchInteractiveOracleProof.ofProto Z.P) Z.wq Z.embS Z.embP (fun _ => none)
    W.embE (W.dReq Z.t) [cm] () π

/-- `plainBad_lang` for the verifier with the strict format. -/
theorem plainBad_langS {W : QueryLayout lam L} (Z : Written W) (R : Reading L W.embE)
    (ε : Err Z.P.shape)
    (Lg : Unit → (oneExternalString L.wordLength L.Symbol).Str → Prop) (hs : Z.P.Sound Lg ε) (hl : Z.P.IsLocal) (hZ : Z.OK)
    (sMT sFS : ℕ) (tr : Tc W) (cm : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto Z.P))
    (hB : ¬ plainBad Z R ε tr) (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (Z.verifierS sMT sFS cm π) true) : Lg () (R.at W tr cm) := by
  obtain ⟨P1, P2, h⟩ := runsIn_verifyB_of_strict hZ.wire hrun
  exact plainBad_lang Z R ε Lg hs hl hZ tr cm (π.withPaths P1 P2) hB
    (keeps_withPaths R π P1 P2 hk) h

end TypedOracleCompiler.Slice
