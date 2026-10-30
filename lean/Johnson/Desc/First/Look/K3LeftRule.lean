-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LeftRule.lean: four statements of Johnson/Top/H/K3LeftStatement.lean and
Johnson/Desc/First/Look/K3LeftRuleStatement.lean, proved: a promise can grow (GoodInPromise); the
promise K3LeftOn stands at every later record (K3LeftOnStays) and follows from the sharp one
(K3LeftOnOfAt); the relation behind the block goes back over a later step (CBehindBack). Theorems
with their proofs.

Limits. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LeftRuleStatement
import Johnson.Top.H.K3LeftLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **A promise can grow**: the prover has lost towards a property that holds the promise; a
sentence that every yes leaves can be laid into that property. -/
theorem goodInPromise : GoodInPromise := fun S Cl W Fr p on on' Q R R' h hQ a ha =>
  Iop.Doomed.mono _ _
    (fun τ hτ b hb => ⟨⟨(hτ b hb).1, hQ a τ b ha hb⟩, (hτ b hb).2⟩) (h a ha)

/-- **The promise stands at every later record.** -/
theorem k3LeftOnStays : K3LeftOnStays := by
  rintro S fork heard h lm first Q s t Fs Ft hh fs ft hL hS ⟨F, F', G, g, rs, q, n, L, hg, hG, l, -⟩
  obtain rfl : G = Fs := Option.some.inj (hG.symm.trans fs)
  exact ⟨F, F', Ft, g, rs, q, n, L, hh.trans hg, ft, l.trans hL, hS⟩

/-- The sharp promise gives the other. -/
theorem k3LeftOnOfAt : K3LeftOnOfAt := by
  rintro S fork heard h lm first Q s ⟨F, F', g, rs, q, n, L, hg, hF⟩
  exact ⟨F, F', F', g, rs, q, n, L, hg, hF, _root_.Fo.Later.refl _, L.padLeft.fit⟩

/-- **The relation behind the block goes back over a later step.** -/
theorem cBehindBack : CBehindBack := by
  rintro S W Fr r lm first mk pl st wt fork heard Pin a b w w' Fa Fb hh fa fb hL hst hw hP
    ⟨hp, g, F', f1, f2, k, kr⟩
  obtain rfl : F' = Fb := Option.some.inj (f1.symm.trans fb)
  have e1 : cMs r wt w' = cMs r wt w := by
    unfold cMs
    rw [hw]
  have e2 : cMu r wt w' = cMu r wt w := by
    unfold cMu
    rw [e1]
  have e3 : cNu r mk pl wt w' = cNu r mk pl wt w := by
    funext q
    unfold cNu
    rw [e2]
  refine ⟨hP hp, g, Fa, fa, hh.symm.trans f2, ?_, ?_⟩
  · rw [← hst, e2, e3]
    exact k3OutBack _ Reading.gl _ _ _ _ _ g Fa F' hL k
  · rw [← hst, e1]
    exact k3OutRiderBack r lm first _ _ g Fa F' hL kr

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.goodInPromise
#print axioms VerifiableInference.OnPublicFiles.k3LeftOnStays
#print axioms VerifiableInference.OnPublicFiles.k3LeftOnOfAt
#print axioms VerifiableInference.OnPublicFiles.cBehindBack
