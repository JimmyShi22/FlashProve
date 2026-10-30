-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SharedOpensOfData.lean: the shared chain opens no tree of the first chain, at the
data of every description. Theorems, by the makers' own test.

Why. The rule for N slots behind one key (Johnson/Desc/Sound/FoldSlots.lean, FileBatch.lean,
SharedSeam.lean) takes as a premise: every number of a tree that a round of the data's second list
opens is at least t₁, the number of trees that the first chain sends. Given that `FileDescription.data`
says yes, it needs neither an evaluation nor a further test in a verifier's text: `FileDescription.data`
asks the makers' tests (`okAt`), and the second clause of `Three.Whole.fits`
(OnBytes/Three/Data.lean) says that the first two chains name their own trees alone.

Main names.
  `fits_own₂`: that clause at the second chain: every opening there is named as the chain's own.
  `opens_rdsFromL`: where the numbers in a round's data come from.
  `sharedOpens_of_okAt`: the premise at the data of three lists of written rounds at which `okAt`
    says yes.
  `sharedOpens_of_data`: the premise at D, from `F.data file = .ok D` alone.

Limits. A fact on numbers of trees; nothing on soundness. That `F.data file` says yes is a premise
here, and is itself owed wherever this premise is. The file does not say that the shared chain opens
any tree (at the written lists it does: `sharedOpens_some_proofFull`, in the file named above).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesDataProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open OnBytes.Three (rootsIn rdsFromL rdOf wholeNo)

/-- The second clause of the makers' test, at the second chain: every opening is of a tree that the
chain sends itself. -/
theorem fits_own₂ {R₁ R₂ R₃ : Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ r ∈ R₂, ∀ o ∈ r.1.opens, ∃ n, Three.named 1 o.2 = some (1, n) := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, c2⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [List.all_eq_true] at c2
  intro r hr o ho
  have h2 := c2 (1, R₂) (by simp) r hr o ho
  cases hn : Three.named 1 o.2 with
  | none =>
    have h3 : (match Three.named 1 o.2 with
      | none => false
      | some y => ((1 : ℕ) == 2 || y.1 == 1) && decide (y.1 ≤ 1)) = true := h2
    rw [hn] at h3
    cases h3
  | some y =>
    have h3 : (match Three.named 1 o.2 with
      | none => false
      | some y => ((1 : ℕ) == 2 || y.1 == 1) && decide (y.1 ≤ 1)) = true := h2
    rw [hn] at h3
    have h4 : (((1 : ℕ) == 2 || y.1 == 1) && decide (y.1 ≤ 1)) = true := h3
    obtain ⟨y1, y2⟩ := y
    have h5 : y1 = 1 := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h4
      omega
    subst h5
    exact ⟨y2, rfl⟩

/-- A number in a round's data is the number over the file of a tree that one of the round's
openings names. -/
theorem opens_rdsFromL (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ) (R : Rounds)
    (d : Three.RDL) (hd : d ∈ rdsFromL all t₁ t₂ here base first R) (j : ℕ) (hj : j ∈ d.opens) :
    ∃ r ∈ R, ∃ o ∈ r.1.opens, ∃ x, Three.named here o.2 = some x ∧ wholeNo t₁ t₂ x = j := by
  unfold rdsFromL at hd
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hd
  obtain ⟨r, n, hr, rfl⟩ := zipWith_get _ _ _ _ _ hk
  obtain ⟨u, hu, e⟩ := List.mem_filterMap.1 hj
  obtain ⟨y, hy, e'⟩ := Option.map_eq_some_iff.1 e
  exact ⟨r, List.mem_of_getElem? hr, u, hu, y, hy, e'⟩

/-- **Where the makers' tests say yes, the shared chain opens no tree of the first chain.** -/
theorem sharedOpens_of_okAt {a : ℕ} {R₁ R₂ R₃ : Rounds} (hok : okAt a (some (R₁, R₂, R₃)) = true) :
    ∀ d ∈ (dataOf a R₁ R₂ R₃).ds₂, ∀ j ∈ d.opens, (dataOf a R₁ R₂ R₃).t₁ ≤ j := by
  have P := okAt_parts (R := (R₁, R₂, R₃)) hok
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := P.fits
  have hcn : countsFit a (Three.Whole.of R₁ R₂ R₃) = true := P.counts
  unfold countsFit at hcn
  simp only [Bool.and_eq_true, beq_iff_eq] at hcn
  have t₁ : (dataOf a R₁ R₂ R₃).t₁ = rootsIn R₁ := hcn.1
  intro d hd j hj
  rw [t₁]
  have hd₁ : d ∈ (Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf := hd
  obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd₁
  have hj' : j ∈ d'.opens := hj
  obtain ⟨r, hr, o, ho, x, hx, rfl⟩ :=
    opens_rdsFromL _ (rootsIn R₁) (rootsIn R₂) 1 (rootsIn R₁) 0 R₂ d' hd' j hj'
  obtain ⟨n, hn⟩ := fits_own₂ hf r hr o ho
  rw [hn] at hx
  obtain rfl := Option.some.inj hx
  exact Nat.le_add_right _ _

/-- **At the data of every description the shared chain opens no tree of the first chain.** -/
theorem sharedOpens_of_data {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j := by
  obtain ⟨⟨R₁, R₂, R₃⟩, -, hok, rfl⟩ := data_ok F file D h
  exact sharedOpens_of_okAt hok

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.sharedOpens_of_okAt
#print axioms VerifiableInference.Desc.Sound.sharedOpens_of_data
