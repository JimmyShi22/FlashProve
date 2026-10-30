-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaCaps.lean: the upper bound of E2E/ZetaGeneral.lean on the error term
`OnBytes.WholeKey.zetaW`, for arbitrary search limits.

Summary. With all search limits 0 each proof-of-work search has one try. `zetaW` counts every
further try, up to the search limit, at an oracle name of its own (`osW`, `laterNames`,
Johnson/WholeKey/Zeta.lean), so the bound grows with the limits. The parameters are arbitrary and
the premises are on numbers alone.

Main results.
  `zetaW_le_caps`: `zetaW … t n ≤ (t A + (9 + CT + CL + CB) A (2 (M + 2) + A)) / 2 ^ b` with
    A := `boundA M n`, if the search limits are at most CT, CL, CB · the six errors of simulators
    and aborts and the error of the OOD seeds are 0 · there are no more sessions than one copy
    serves · a leaf's salt, a Fiat-Shamir query's salt and a digest each have at least b secret bits
    · the ten numbers of the wiring are as in `mW_le`. A does not grow with the search limits; the
    bound is linear in them.

Terms: E2E/HidingTerms.lean.

Limits.
- No bound on `zetaW` says that the searches succeed. That for given search limits a proof is
  produced, except with small probability, is a statement about the prover's run, and it is not
  proved here (at the verifier's parameters: E2E/StringsAtInput.lean). In the words of
  Johnson/WholeKey/Zeta.lean: "No term for a search that runs out: that is a value of the key or of
  a proof, which the simulator is built to make with the real law."
- A bound on a written expression. What that expression bounds, and under which premises, is stated
  in Johnson/WholeKey/Statement.lean and Johnson/WholeKey/Main.lean.
- An upper bound, not proved to be tight: at a further try's name the count is bounded by all
  rounds, not by the rounds with a test.

Definitions and helper lemmas.
  `maxCap_le`, `nLater_le`, `later_card`: the greatest search limit of a round with a test is at
    most a bound on all limits; the rounds whose search may make a given further try are at most the
    rounds; k further tries have at most k names.
  `later_mem`: a name among those of the further tries is the name of a further try at that tag.
  `osW_mem`, `osW_card`: a counted oracle name is one of the nine or the name of a further try; with
    limits of at most CT, CL, CB there are at most 9 + CT + CL + CB.


-/
import E2E.ZetaGeneral

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open OnBytes.WholeKey OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

section
variable {lam K : ℕ}

theorem maxCap_le {cap : ℕ → ℕ} {C : ℕ} (h : ∀ i, cap i ≤ C) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), maxCap s A W cap i ≤ C
  | [], _, _, _ => Nat.zero_le _
  | _ :: s, (a, A), (w, W), i => by
    show max (if roundHasTest a w = true then cap i else 0) (maxCap s A W cap (i + 1)) ≤ C
    refine max_le ?_ (maxCap_le h s A W (i + 1))
    split
    · exact h i
    · exact Nat.zero_le _

theorem nLater_le (cap : ℕ → ℕ) (j : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), nLater s A W cap i j ≤ s.length
  | [], _, _, _ => Nat.le_refl _
  | _ :: s, (a, A), (w, W), i => by
    show (if roundHasTest a w = true ∧ j + 1 ≤ cap i then 1 else 0) + nLater s A W cap (i + 1) j ≤
      s.length + 1
    have ih := nLater_le cap j s A W (i + 1)
    split <;> omega

end

theorem later_card (t : Tag) (k : ℕ) : (laterNames t k).card ≤ k := by
  unfold laterNames
  exact le_trans Finset.card_image_le (le_of_eq (Finset.card_range k))

theorem later_mem {t : Tag} {k : ℕ} {o : ON₂} (h : o ∈ laterNames t k) : ∃ j, o = .fbw t j := by
  unfold laterNames at h
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
  exact ⟨j, rfl⟩

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (p : Params) (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (u : NumsW)

/-- A counted oracle name is one of the nine, or the name of a further try. -/
theorem osW_mem {o : ON₂} (h : o ∈ osW W a) : o ∈ nine ∨ ∃ t j, o = .fbw t j := by
  unfold osW at h
  simp only [Finset.mem_union] at h
  rcases h with ((h | h) | h) | h
  · exact .inl h
  · exact .inr ⟨_, later_mem h⟩
  · exact .inr ⟨_, later_mem h⟩
  · exact .inr ⟨_, later_mem h⟩

theorem osW_card {CT CL CB : ℕ} (hT : ∀ i, a.capT i ≤ CT) (hL : ∀ i, a.capL i ≤ CL)
    (hB : ∀ i, a.capB i ≤ CB) : (osW W a).card ≤ 9 + CT + CL + CB := by
  unfold osW
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add (le_trans (Finset.card_union_le _ _) (Nat.add_le_add nine_card ?_)) ?_)) ?_)
  · exact le_trans (later_card _ _) (maxCap_le hT _ _ _ _)
  · exact le_trans (later_card _ _) (maxCap_le hL _ _ _ _)
  · exact le_trans (later_card _ _) (maxCap_le hB _ _ _ _)

/-- **The error for arbitrary search limits, from bounds on numbers.** -/
theorem zetaW_le_caps (t n b CT CL CB : ℕ) (hT : ∀ i, a.capT i ≤ CT) (hL : ∀ i, a.capL i ≤ CL)
    (hB : ∀ i, a.capB i ≤ CB)
    (hz : u.zT = 0 ∧ u.zL = 0 ∧ u.zO = 0 ∧ u.hT = 0 ∧ u.hL = 0 ∧ u.hO = 0 ∧ u.δ = 0)
    (hn : n ≤ u.s1) (hb1 : b ≤ c.ℓ) (hb2 : b ≤ p.sFS) (hb3 : b ≤ lam) (hd : W.depth = 32)
    (l1 : runLeaves L.offline.shape aT (wTC W).sh ≤ 2 ^ 37)
    (l2 : runLeaves L.link.shape aL (wLC W).sh ≤ 2 ^ 25)
    (l3 : runLeaves L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ≤ 2 ^ 39)
    (r1 : L.offline.shape.length ≤ 2 ^ 20) (r2 : L.link.shape.length ≤ 2 ^ 20)
    (r3 : L.onlineBatch.loc.shape.length ≤ 2 ^ 20) (q1 : W.depthReqT ≤ 2 ^ 20) (q2 : W.depthReqL ≤ 2 ^ 20)
    (q3 : W.depthReq ≤ 2 ^ 20) :
    zetaW W S p a c u t n ≤
      ((t * boundA a.M n +
        (9 + CT + CL + CB) * (boundA a.M n * (2 * (a.M + 2) + boundA a.M n)) : ℕ) : ℝ≥0∞) /
        2 ^ b := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  obtain ⟨-, -, -, -, -, -, c7, c8, c9⟩ :=
    counts_le a.M n _ _ _ _ _ _ _ _ _ l1 l2 l3 r1 r2 r3 q1 q2 q3
  have h9 := mW_le W a n hd l1 l2 l3 r1 r2 r3 q1 q2 q3
  have hm : ∀ o ∈ osW W a, mW W a n o ≤ boundA a.M n := by
    intro o ho
    rcases osW_mem W a ho with h | ⟨t', j, rfl⟩
    · exact h9 o h
    · cases t' with
      | test => exact le_trans (nLater_le _ _ _ _ _ _) c7
      | link => exact le_trans (Nat.mul_le_mul_left _ (nLater_le _ _ _ _ _ _)) c8
      | onl => exact le_trans (Nat.mul_le_mul_left _ (nLater_le _ _ _ _ _ _)) c9
  have he : ∀ o ∈ osW W a, eW W S a n o ≤ 2 * (a.M + 2) := by
    intro o ho
    rcases osW_mem W a ho with h | ⟨t', j, rfl⟩
    · simp only [nine, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Nat.zero_le _
        | (show (if _ then 2 * (a.M + 2) else 0) ≤ _
           split
           · exact Nat.le_refl _
           · exact Nat.zero_le _)
    · exact Nat.zero_le _
  have hbits : ∀ o ∈ osW W a, b ≤ bitsW (lam := lam) p c o := by
    intro o ho
    rcases osW_mem W a ho with h | ⟨t', j, rfl⟩
    · simp only [nine, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact hb1
        | exact hb3
        | exact le_min hb2 hb3
    · exact le_min hb2 hb3
  unfold zetaW
  rw [pOver_zero _ _ _ hn, z1, z2, z3, z4, z5, z6, z7]
  simp only [mul_zero, add_zero, zero_add]
  exact costTotal_le_of _ _ _ _ t (boundA a.M n) (2 * (a.M + 2)) b (9 + CT + CL + CB) hm he hbits
    (osW_card W a hT hL hB)

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.osW_card
#print axioms AtPublicFiles.ZetaAt.zetaW_le_caps
#print axioms AtPublicFiles.ZetaAt.maxCap_le
#print axioms AtPublicFiles.ZetaAt.nLater_le
#print axioms AtPublicFiles.ZetaAt.later_card
#print axioms AtPublicFiles.ZetaAt.later_mem
#print axioms AtPublicFiles.ZetaAt.osW_mem
