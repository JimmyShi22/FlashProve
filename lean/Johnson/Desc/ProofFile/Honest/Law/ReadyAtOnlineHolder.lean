-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyAtOnlineHolder.lean: two more kinds of form beside
Honest/Law/ReadyAtOnlineForms.lean. No definition; four theorems.

  `kindPays_first_at_own_description`, `kindPays_shared_at_own_description`,
  `kindPays_second_at_own_description`   a kind that pays at every return at the base filling, at that
                              return's own description, pays at the online return at its own: no
                              list is fixed in advance
  `ready_one_at_laid`         **the type of the field `ready₁` of `PlainAt` at the letters of whoever
                              holds them**: it asks `LaidAt` at those letters, as the field's holder
                              has it, and the two tests on the public files, and no head

Limits.
  * Nothing here pays a kind. What is paid by the payments is that `chainSteps` returns at the members:
    nothing here says that a part plays, or that a verifier accepts.
  * `ready_one_at_laid` asks one served pair; that some pair is served is not shown here.
  * That the maker returns is a premise (hA).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyAtOnlineForms
import Johnson.Desc.ProofFile.Honest.AtPureBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm (TraceWhereServed)
open VerifiableInference.Desc (KindName Chain)

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files} {κ : KindName}

/-- **A kind that pays at every return at the base filling, at that return's own description, pays at
the online return at its own: first chain.** -/
theorem kindPays_first_at_own_description (hA : onlineMaker files = .ok returned)
    (hbase : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        KindPays A₀.B 0 A₀.F.first.blocksInOrder A₀.H.first κ) :
    KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first κ :=
  kindPays_first_of_base_return hA fun A₀ h₀ => by
    obtain ⟨-, -, eF, -⟩ := atPure_book_same h₀ hA
    rw [← eF]
    exact hbase A₀ h₀

/-- **The same at the shared chain.** -/
theorem kindPays_shared_at_own_description (hA : onlineMaker files = .ok returned)
    (hbase : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        KindPays A₀.B 1 A₀.F.shared.blocksInOrder A₀.H.shared κ) :
    KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared κ :=
  kindPays_shared_of_base_return hA fun A₀ h₀ => by
    obtain ⟨-, -, eF, -⟩ := atPure_book_same h₀ hA
    rw [← eF]
    exact hbase A₀ h₀

/-- **The same at the second chain.** -/
theorem kindPays_second_at_own_description (hA : onlineMaker files = .ok returned)
    (hbase : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        KindPays A₀.B 2 A₀.F.second.blocksInOrder A₀.H.second κ) :
    KindPays returned.B 2 returned.F.second.blocksInOrder returned.H.second κ :=
  kindPays_second_of_base_return hA fun A₀ h₀ => by
    obtain ⟨-, -, eF, -⟩ := atPure_book_same h₀ hA
    rw [← eF]
    exact hbase A₀ h₀

end

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {returned : OnlineReturn Z}

/-- **The type of the field `ready₁` of `PlainAt` at the letters of whoever holds them.** Conditional on
`LaidAt` at these letters, on the two tests on the public files, on the return, on the sixteen
payments, on G's three lists being the return's, on `TraceWhereServed` and on one served pair. -/
theorem ready_one_at_laid (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (laid : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned)
    {G : ProofFile.Honest.Sides (descZ Zp Np cF) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness OnBytes.TableKey Cells Unit Unit}
    (e1 : (provG Z Zp Np cF returned.B G returned.H).first = returned.H.first)
    (e2 : (provG Z Zp Np cF returned.B G returned.H).shared = returned.H.shared)
    (e3 : (provG Z Zp Np cF returned.B G returned.H).second = returned.H.second)
    {Served : FullSizeMatrix → LPFD.Full.XF → Prop} (hT : TraceWhereServed Served returned) {M : FullSizeMatrix}
    {request : LPFD.Full.XF} (hS : Served M request) :
    ∃ w₀ rc x k R,
      ready (descZ Zp Np cF) returned.B (provG Z Zp Np cF returned.B G returned.H) w₀ rc x k =
        .ok R := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨_, _, _, _, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  have Dt := readyDebts_online h hA Pm
  rw [(atPure_at_laid laid hA).2] at Dt
  have rc : (protocolAtFiles Z).EncodingRandomness := Classical.choice (protocolAtFiles Z).encodingRandomnessIsNonempty
  have seed : (protocolAtFiles Z).OutOfDomainSeed := Classical.choice (protocolAtFiles Z).outOfDomainSeedIsNonempty
  obtain ⟨hi, ht⟩ := hT M request ((protocolAtFiles Z).recOf M rc seed) hS
  obtain ⟨R, hR⟩ := ready_of_sides (readyDebts_same_sides Dt e1 e2 e3 rfl rfl) hi ht rc default
  exact ⟨M, rc, _, default, R, hR⟩

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.kindPays_first_at_own_description
#print axioms ProofFile.Honest.Term.kindPays_shared_at_own_description
#print axioms ProofFile.Honest.Term.kindPays_second_at_own_description
#print axioms ProofFile.Honest.Term.ready_one_at_laid
