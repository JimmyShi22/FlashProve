-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsOfCongr.lean: the sentence «the digits are in their tables»
(DigitsOf, Johnson/Desc/First/K8/DigitsOf.lean: the approximate range proof's files' own): WHAT IT
READS, AS TWO LEMMAS: of its table of cells, and of the approximate range proof's parameters. Light:
over that file alone. NO SOUNDNESS IS CLAIMED.

Main names.
  digitsOf_cells: two tables that agree AT THE CELLS THAT THE SENTENCE READS (the array tl.ix.ZZ,
    row u < tl.tau, the columns (tl.zzCol μ b 0).getD 0 + i for μ < tl.NM, i < (tl.mats.getD μ
    {}).m, b < 2) say the same.
  digitsOf_six: two values of the parameters that agree in NM, tau, mats, ix.ZZ, mz, off say the
    same: the sentence reads no other field (zzCol reads NM, mats, mz, off; of sizeOf it reads lo
    and hi, two constants).
OBJECT. The definition DigitsOf.
USER. digitsAt_mgAll (Johnson/Desc/Sound/MgAt/K3DigitsAt.lean).
LETTERS. tl, ts, A, A'.
IS IT EMPTY? At A' := A, ts := tl the premises hold.


Compiled with the whole library.
Limits. One direction each. The approximate range proof's authors have a lemma on the parameters of
their own (K8.digitsOf_congr, K8/LawItemsAt.lean: both directions, under wideOf tl = wideOf tl',
which asks funClosed and funs besides): digitsOf_six asks six fields alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K8.DigitsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (DigitsOf)

/-- **The sentence reads its table at these cells alone.** -/
theorem digitsOf_cells (tl : HTailF2) (A A' : ℕ → ℕ → ℕ → Cb.Gl.E)
    (h : ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      A tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i) = A' tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) :
    DigitsOf tl A → DigitsOf tl A' := by
  intro H μ hμ u hu i hi
  obtain ⟨h0, h1⟩ := H μ hμ u hu i hi
  rw [h μ hμ u hu i hi 0 (by omega)] at h0
  rw [h μ hμ u hu i hi 1 (by omega)] at h1
  exact ⟨h0, h1⟩

/-- **It reads six fields of the parameters alone.** -/
theorem digitsOf_six (tl ts : HTailF2) (hNM : ts.NM = tl.NM) (hTau : ts.tau = tl.tau)
    (hM : ts.mats = tl.mats) (hZ : ts.ix.ZZ = tl.ix.ZZ) (hmz : ts.mz = tl.mz)
    (hoff : ts.off = tl.off) (A : ℕ → ℕ → ℕ → Cb.Gl.E) : DigitsOf tl A → DigitsOf ts A := by
  intro H μ hμ u hu i hi
  have hc : ∀ b j, ts.zzCol μ b j = tl.zzCol μ b j := by
    intro b j
    unfold HTailF2.zzCol
    rw [hNM, hM, hmz, hoff]
  rw [hNM] at hμ
  rw [hTau] at hu
  rw [hM] at hi
  have K := H μ hμ u hu i hi
  rw [hZ, hc 0 0, hc 1 0]
  exact K

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digitsOf_cells
#print axioms VerifiableInference.OnPublicFiles.digitsOf_six
