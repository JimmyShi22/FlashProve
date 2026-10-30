-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FileBatch.lean: the rule of composition across a proof file's three chains, for a
batch of N requests, from premises on the blocks alone. A SHEET OF STATEMENTS: two propositions
written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

What is said. The top theorem for a proof file (`proofSound_top_links`,
Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean) asks of the three chains the list `Links.KnowsJ`
(OnBytes/TypedOracleCompiler/Joined/MidLinks.lean). `FileKnowsJ` (Johnson/Desc/Sound/FileKnowsJ.lean) gives that
list at the library's row of the three folds, with the shared chain's clause l₂ as a premise. Here
that premise is paid by Johnson/Desc/Sound/SharedSeam.lean. `FileKnowsJOfKeyed`: from `EachGood` at
the first and the third chain and `Keyed` at the shared chain. `FileKnowsJOfGood`: from `EachGood`
at the first and the third chain and, at the shared chain, a law for one request for each block
(`EachGoodIn`) with `EachRels`, `EachKeeps` and a test on the data.

Limits. (1) Those of FileRule.lean, SharedRule.lean, GoodIn.lean and SharedSeam.lean. (2) THE LAW ON
THE FIRST KEY IS A PREMISE: what the first chain hands on has a key that is a function F₁ of the
stored table alone. In `FileKnowsJOfGood` the key is the shared chain's own first record with the
stored table: so that record must be the same for all instances. Where it hangs on a part of the
instance that all requests of a batch share (the key file's record), the statement is to be read at
the type Y of the instances WITH THAT PART FIXED: the top theorem asks the list record by record.
(3) Nothing bounds the errors.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- **Across the three chains, for a batch: the shared chain's blocks are links with keys.** -/
def FileKnowsJOfKeyed : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ : Type)
    (tF : TF) (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places D all S₁ S₂ S₃ W) (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂) (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
    (N : ℕ) (kA kZ : BKey (frameAt D all D.key₂ T.ft₂) S₂) (k₁ : X₁ × (EAll D all).Str → κ₁)
    (k₂ : X₂ × (EAll D all).Str → κ₂) (F₁ : (oneExternalString (2 ^ D.a) SgX).Str → κ₁),
    T.Fits → EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁) → Keyed N Q.on₂ Q.R₂ 0 T.p₂ T.l₂ kA kZ →
    EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃) → T.Glued Q →
    (∀ a τ b, ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.out a
      τ = some b → k₁ b = F₁ a.2) →
    (∃ g : κ₁ → kA.1, ∀ a, kA.2 (T.in₂ a.1, a.2) = g (k₁ a)) →
    (∃ G : κ₁ → kZ.1 → κ₂, ∀ a b, k₂ (T.out₂ a.1 b.1, b.2) = G (k₁ a) (kZ.2 b)) →
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).KnowsJ N k₁ k₂

/-- **Across the three chains, for a batch, from a law for one request for each block.** The letters
are those of `SeamOfGood`. -/
def FileKnowsJOfGood : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₀ S₃ X₁ X₂ Cl W TF TJ T3 : Type)
    (tF : TF) (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places D all S₁ S₂ S₃ W) (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂) (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
    (N : ℕ) (get : S₂ → S₀) (set : S₂ → S₀ → S₂) (Ra : ℕ → S₂ × (EAll D all).Str → W → Prop)
    (Rc : S₂ × (EAll D all).Str → W → Prop)
    (F₁ : (oneExternalString (2 ^ D.a) SgX).Str → S₀ × (oneExternalString (2 ^ D.a) SgX).Str),
    T.Fits → EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁) → EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃) →
    T.Glued Q → (Q.R₂ = fun i a w => Ra i a w ∧ Rc a w) →
    EachGoodIn Q.on₂ Ra 0 (T.p₂ :: T.l₂) →
    EachRels Q.on₂ Ra (actsOf get D.t₁ T.p₂ T.l₂) 0 (T.p₂ :: T.l₂) →
    EachKeeps Q.on₂ Rc 0 (T.p₂ :: T.l₂) → (∀ t s, get (set t s) = s) →
    (∀ t s s', set (set t s) s' = set t s') →
    (∀ q ∈ T.p₂ :: T.l₂, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
    (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) →
    (∀ a τ b, ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.out a
      τ = some b → (get (T.in₂ b.1), b.2.1) = F₁ a.2) →
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).KnowsJ N
      (fun a : X₁ × (EAll D all).Str => (get (T.in₂ a.1), a.2.1)) (fun _ => ())


end VerifiableInference.Desc.Sound
