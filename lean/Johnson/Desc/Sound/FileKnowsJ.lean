-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FileKnowsJ.lean: the rule of composition across the three chains FOR A BATCH of
requests that share the second chain: one statement, `FileKnowsJ`, and its proof.

`Links.KnowsJ` (OnBytes/TypedOracleCompiler/Joined/MidLinks.lean) is what the top theorem for a proof file
(`proofSound_top_links`, Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean) asks of the three chains' data: each
chain a link with keys (`LinkJ`, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean), and the two hand-overs. Here it is
reached at the value of Johnson/Desc/Sound/FileRule.lean:
  `l₁`, `l₃`: from the first and the third clause of `FileKnows`' proof (`file_know₁`,
    `file_know₃`), by the library's `LinkJ.ofLocal`: the first and the third chain's rounds are each
    request's own; nothing is asked here of the second chain's blocks or of `Glue₂`;
  `l₂`: A PREMISE HERE: the clause on the shared chain (stated at this value in
    Johnson/Desc/Sound/SharedSeam.lean, over the rule of Johnson/Desc/Sound/SharedRule.lean);
  `hands₁`, `hands₂`: free (FileRule.lean says why).

Limits: those of FileRule.lean. The keys k₁, k₂ are parameters. The premise before the last is a law
on the first key: what the first chain hands on has a key that is a function F₁ of the stored table
alone: so for requests with one stored table it is one key. The top theorem asks the list record by
record (`Links.comap`): not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileKnowsProof
import OnBytes.TypedOracleCompiler.Joined.MidLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.TypedOracleCompiler.Joined (Links LinkJ)
open _root_.CompileK.Joined (allKind_const)

/-- **The rule of composition across the three chains, for a batch.** N: the number of requests. -/
def FileKnowsJ : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (N : ℕ) (k₁ : X₁ × (EAll D all).Str → κ₁)
    (k₂ : X₂ × (EAll D all).Str → κ₂) (F₁ : (oneExternalString (2 ^ D.a) SgX).Str → κ₁),
    T.Fits → EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁) → EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃) →
    T.Glue₁ Q → T.Ends Q →
    (∀ a τ b, ((T.row tF tJ t3 okF okJ ok3).links
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.out a τ = some b → k₁ b = F₁ a.2) →
    LinkJ ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₂
      (chainsOf C D tF tJ t3).A₂ N k₁ k₂ (fun _ => True) (T.mid₁ Q) (T.mid₂ Q)
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).e₂ (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₂ →
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).KnowsJ N k₁ k₂

theorem fileKnowsJ : FileKnowsJ := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N k₁ k₂ F₁ hf
    g₁ g₃ hg₁ he hk l₂
  exact ⟨LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (file_know₁ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₁ hg₁) F₁ hk, l₂,
    LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (file_know₃ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₃ he) (fun _ => ()) (fun _ _ _ _ => rfl),
    fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

end VerifiableInference.Desc.Sound
