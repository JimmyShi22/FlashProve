-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/GoodInProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/GoodIn.lean.

Limits: those of Johnson/Desc/Sound/GoodIn.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn
import OnBytes.Maker.TreesLaws
import OnBytes.Maker.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

theorem goodOfGoodIn : GoodOfGoodIn := by
  intro S Cl W C F p on on' R R' h
  refine ⟨⟨pointsT C p.ds⟩, stageIOR_isLocal C p.stage p.run, fun a ha => ?_⟩
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b w hb hw
  obtain ⟨ho, hk⟩ := hτ b hb
  exact hk w (hw.elim id fun n => absurd ho n)

theorem goodInOfCarry : GoodInOfCarry := by
  intro S Cl W C F p on on' R R' hc hk a ha
  refine Doomed.mono _ _ ?_ (hk a ha)
  intro τ hτ b hb
  exact ⟨hc a τ b ha hb, fun w hw => hτ b w hb hw⟩

theorem goodInOfBadFam : GoodInOfBadFam := by
  intro S Cl W C F p on on' R R' bad hW h2 h3 a ha
  exact Iop.doomed_of_clean _ _ (bad a) _ (hW a ha)
    fun τ hτ b hb => ⟨h2 a τ b ha hτ hb, fun w hw => h3 a τ b w ha hτ hb hw⟩

theorem goodInBeside : GoodInBeside := by
  intro S Cl W C F p on on' R R' Rc h hc a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  obtain ⟨ho, hk⟩ := hτ b hb
  exact ⟨ho, fun w hw => ⟨hk w hw.1, hc a τ b w ha hb ho hw.2⟩⟩

end VerifiableInference.Desc.Sound
