-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/ProofSevenReM.lean: the seven fields of `ProofPlainSevenAtF`
(Johnson/Flat/Dec/ProofPlainLeft.lean) carried FROM ONE LETTER M' TO ANOTHER LETTER M.

Why. M stands in two of the seven fields, once each way: `glues` has to give it, `tie` has to spend
it. So from the seven at M' and "M' gives M" SIX fields carry over to M, and the seventh does not:
`tie` at M is a premise of its own.
  `ProofPlainSevenAtF.reM`: the seven at M'; M' a c → M a c at all a, c; `tie` at M, in the field's
  own words: then the seven at M.
Use. Who has proved the seven at an M of its own, and that its M gives the chosen one (`meansSome`,
Johnson/Goal/Meaning/TieAtSome.lean), gets the seven at the chosen one with `tie_of_some` in the
last place.
Limits. A joining: it pays nothing. The old `tie` at M' is not used. "M' gives M" is asked at ALL a
and c, with no promise in front: who has it only under the first chain's first promise, its steps or
L₁ (what `glues`' first implication has in hand) cannot use the lemma as it lies. No soundness
follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.ProofPlainLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

/-- **From one M to another: six fields carry over; `tie` is owed anew.** -/
theorem ProofPlainSevenAtF.reM {X XiP : Type} {F : FileDescription XiP} {instP : X × RecFull → XiP}
    {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DP : WholeD} {rP : RecFull}
    {depthReq : ℕ} {early : X → X} {W : Type}
    {c₁ : Block F.S₁ F.Cl} {k₁ : List (Block F.S₁ F.Cl)} {c₂ : Block F.S₂ F.Cl}
    {k₂ : List (Block F.S₂ F.Cl)} {c₃ : Block F.S₃ F.Cl} {k₃ : List (Block F.S₃ F.Cl)}
    {e₁ e₂ e₃} {dW wEnd : W} {Pl M' L₁ L₂ w₀ kS₂}
    (H : ProofPlainSevenAtF F instP A E DP rP depthReq early c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd Pl
      M' L₁ L₂ w₀ kS₂)
    (M : (X × RecFull) × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
      (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (hM : ∀ a c, M' a c → M a c)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (τ : Tr (chainsOf (ckP .two)
                     (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh)
        (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃) (z : (EAll (DP.at frS.P.T.a) (allOf (DP.at
            frS.P.T.a))).Str),
        F.okStart (instP (x, rec)) = true →
        silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
            ByteArray.empty).msgF τ).2 ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀
            rP) ByteArray.empty).msgJ τ).2 ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP)
            (join₀ rP) ByteArray.empty).msg3 τ).2 = true →
        F.fin (instP (x, rec)) s₁ s₂ s₃ = true →
        (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
            (restCap e₂) (restCap e₃) dW wEnd)).in₁ (instP (early x, rec)), (y, fun _ => [])) →
          M ((early x, rec), y) ((F.pub (instP (x, rec)), s₁), z)) →
        (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none ∨
          ∃ i, (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = some i ∧ (lettersAt A (relationsAndEncodingOfClaims A
                                    E)).conf.Rno i x w₀) :
    ProofPlainSevenAtF F instP A E DP rP depthReq early c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd Pl M L₁
      L₂ w₀ kS₂ where
  leads₁ := H.leads₁
  leads₂ := H.leads₂
  leads₃ := H.leads₃
  glues := ⟨fun x y b ho hs => ⟨(H.glues.g₁ x y b ho hs).1,
      fun hl => hM _ _ ((H.glues.g₁ x y b ho hs).2 hl)⟩, H.glues.g₂, H.glues.g₃⟩
  pubEarly := H.pubEarly
  one := H.one
  tie := tie

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.ProofPlainSevenAtF.reM
