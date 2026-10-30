-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TwoLink.lean: the entry's arm of the compiled verifier, at the inputs of
Johnson/Flat/TwoSizes.lean, is sound against every maker.

One theorem at each size: `linkA_pr` (Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean) at `innerCompilerInputFromDryRunAtFullSize T` |
`innerCompilerInputFromDryRunAtSmallSize T`'s own object, marks, wire, record's wire and code of the answers. Of its seven
premises all are met here: the link's soundness (under the theorem on codes), its verifier's
locality, the marks' coherence, the code of the answers (one to one; one length), the seed's law,
that every round's error is at most 2^-128, and the laws of the entry's wire (`OKLA T.W`:
`linkWireLawsFromDryRunAtFullSize`, `linkWireLawsFromDryRunAtSmallSize`: at the written wiring of Johnson/Flat/WireAt.lean).

Limits: those of Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean and Johnson/Flat/TwoSizes.lean; and: T.W is
the written wiring: that programs are wired so is stated by no theorem. The key file's and the proof
file's protocols are not read by the statement but through the types of the wire and the oracles.
That the typed queries are the strings that a program hashes is not said here: the oracles are the
typed ones, not one hash function. `LinkHolds` says nothing where the first table decodes to
nothing. The theorem takes all of T, so also a coding and an extractor that it never reads: the
coding's type holds laws, and where no T is the theorem says nothing. `tVL T.W` is at a request tree
of one leaf: our choice.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TwoSizes
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPr

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The full-size files -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {G : FilesParameters X RecFull}
  {P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- What the entry's arm asks of the wires holds at the written wiring: under no hypothesis. -/
theorem linkWireLawsFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : OKLA T.W :=
  have h := wiresFullAt A E G P T.salt
  ⟨h.2.2.1, h.1.B.ext, h.1.prjE_emb, h.1.prjL_emb, h.1.extDepth.2.1, h.1.extL⟩

set_option maxRecDepth 20000 in
/-- Under the theorem on codes (a hypothesis of the theorem: Lean's list of axioms does not show
it): the entry's arm of the compiled verifier at this size is sound against every maker: it accepts
two roots, two records and a proof string, and what it promises of them fails on the trace, with
probability at most n · 2^-128 + 2 (n + 1)² / 2^256, n = 5 (t + tVL), where t bounds the maker's
queries. -/
theorem linkPrFull (hA : BCHKS46At GF GE) (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (p : Params)
    (M : TypedOracleComputation 256 T.W.K (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) T.Bd
                            (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL)
      (OutLA 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL))
    (t : ℕ) (hq : M.QueryBound t) :
    Rom.Pr (joinedLA T.W T.letters.Sd T.letters.cA p M).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ LinkHolds T.W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
      (((t + tVL T.W) * (1 + 4) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        2 * (((t + tVL T.W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  have ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtFullSize_entrySound A (relationsAndEncodingOfClaims A E) G hA
  linkA_pr (εL := ε) hs
    (byConstructionFull T).entryLocal (byConstructionFull T).entryCoherent (linkWireLawsFromDryRunAtFullSize T)
    ⟨(withContentFull hA T).answersCode, (byConstructionFull T).answersLength⟩
    (withContentFull hA T).seedLaw
    (by
      show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
        (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsFull)) ε) _
      rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
      exact hb) p M t hq

end

/-! ## The small files -/

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {G : FilesParameters X RecSmall}
  {P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- What the entry's arm asks of the wires holds at the written wiring: under no hypothesis. -/
theorem linkWireLawsFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : OKLA T.W :=
  have h := wiresSmallAt A E G P T.salt
  ⟨h.2.2.1, h.1.B.ext, h.1.prjE_emb, h.1.prjL_emb, h.1.extDepth.2.1, h.1.extL⟩

set_option maxRecDepth 20000 in
/-- Under the theorem on codes (a hypothesis of the theorem: Lean's list of axioms does not show
it): the entry's arm of the compiled verifier at this size is sound against every maker: it accepts
two roots, two records and a proof string, and what it promises of them fails on the trace, with
probability at most n · 2^-128 + 2 (n + 1)² / 2^256, n = 5 (t + tVL), where t bounds the maker's
queries. -/
theorem linkPrSmall (hA : BCHKS46At GF GE) (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (p : Params)
    (M : TypedOracleComputation 256 T.W.K (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) T.Bd
                            (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL)
      (OutLA 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL))
    (t : ℕ) (hq : M.QueryBound t) :
    Rom.Pr (joinedLA T.W T.letters.Sd T.letters.cA p M).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ LinkHolds T.W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
      (((t + tVL T.W) * (1 + 4) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        2 * (((t + tVL T.W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  have ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtSmallSize_entrySound A (relationsAndEncodingOfClaims A E) G hA
  linkA_pr (εL := ε) hs
    (byConstructionSmall T).entryLocal (byConstructionSmall T).entryCoherent (linkWireLawsFromDryRunAtSmallSize T)
    ⟨(withContentSmall hA T).answersCode, (byConstructionSmall T).answersLength⟩
    (withContentSmall hA T).seedLaw
    (by
      show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
        (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsSmall)) ε) _
      rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
      exact hb) p M t hq

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.linkPrFull
#print axioms VerifiableInference.OnPublicFiles.linkPrSmall
