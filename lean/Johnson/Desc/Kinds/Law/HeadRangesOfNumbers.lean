-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadRangesOfNumbers.lean: THE GEOMETRY OF THE OUTPUT HEAD'S CELLS: the places
at which the library's own map lays the features that the head's relation names lie inside the four
ranges of SmallH (Law/HeadCellsMeet.lean: InRanges): at the full size's numerals.

Main name (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  inRanges_of_numbers: InRanges h L b, from the structures of numerals NumH h L and BorderH b
      (Johnson/Road/HeadPlace.lean) and four equations on K6's files' own sizes: d = 5120, T =
      1024, JV = 202048, NR + 21 ≤ 120.

  inRanges_in_scope: InRanges AT ALL PUBLIC FILES IN THE GOALS' SCOPE: no premise beside the scope's
      three.

  inSizes_in_scope: the four ranges lie inside the sizes of the approximate range proof at segment
      24, at all public files in the goals' scope (public_mats,
      OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean: the list of matrices is matsH's).

How. Each place is a quotient and a remainder of the feature's number by numerals: linear
arithmetic.
Every letter under "there is": none.
What it does not say. The full size alone. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadCellsMeet
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Norm (d T)

/-- **The geometry, at the full size's numerals.** -/
theorem inRanges_of_numbers [Sizes] {h : OnBytes.Model.Head.Shape} {L : OnBytes.Model.Head.HL}
    {b : OnBytes.Model.Head.Border} (N : OnBytes.Road.Hd.NumH h L) (Bd : OnBytes.Road.Hd.BorderH b)
    (hd : d = 5120) (hT : T = 1024) (hJ : JV = 202048) (hR : NR + 21 ≤ 120) :
    InRanges h L b := by
  refine ⟨fun f t hf ht => Or.inl ?_, fun f t hf ht => Or.inr (Or.inl ?_),
    fun f t hf ht => Or.inr (Or.inr (Or.inl ?_)), fun f t hf ht => Or.inr (Or.inr (Or.inr ?_))⟩
  · show 0 + f / (L.m / h.T) / L.k < h.NHf ∧ f % (L.m / h.T) * h.T + t < L.m ∧
      f / (L.m / h.T) % L.k < L.k
    rw [N.fc, N.k, N.NHf, N.T, N.m]
    rw [hd, hJ] at hf
    rw [hT] at ht
    omega
  · show h.NHf + f / (L.mD / h.T) / L.kD = h.NHf ∧ f % (L.mD / h.T) * h.T + t < L.mD ∧
      f / (L.mD / h.T) % L.kD < L.kD
    rw [N.fcD, N.kD, N.T, N.mD]
    rw [hd] at hf
    rw [hT] at ht
    omega
  · show h.NHf + 1 + f / (L.mR / h.T) / L.kR = h.NHf + 1 ∧ f % (L.mR / h.T) * h.T + t < L.mR ∧
      f / (L.mR / h.T) % L.kR < L.kR
    rw [N.fcR, N.kR, N.T, N.mR]
    rw [hT] at ht
    omega
  · show h.NHf + 3 + b.cell (f / h.d) (f % h.d) / (b.mxb / h.T) / b.kxb = h.NHf + 3 ∧
      b.cell (f / h.d) (f % h.d) % (b.mxb / h.T) * h.T + t < b.mxb ∧
      b.cell (f / h.d) (f % h.d) / (b.mxb / h.T) % b.kxb < b.kxb
    rw [Bd.cell, N.T, Bd.fc, Bd.kxb, Bd.mxb, N.d]
    unfold Inst.Model.Head.fX
    rw [hd] at hf
    rw [hT] at ht
    omega

/-- **THE GEOMETRY HOLDS AT ALL PUBLIC FILES IN THE GOALS' SCOPE.** -/
theorem inRanges_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (w : Nat) :
    @InRanges (parOf X.hS w).sizes X.hS X.HLy (OnBytes.Model.Verify.borderOf X.y) := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have R := InScope.k06Ref_in_scope hZ hR h
  exact @inRanges_of_numbers (parOf X.hS w).sizes _ _ _
    (OnBytes.Road.Hd.numH_of_layout B.full B.head)
    (OnBytes.Road.Hd.borderH_of_layout B.lay B.switches B.sized B.sized2) R.d R.T R.JV (by decide)

/-- **THE FOUR RANGES LIE INSIDE THE PLAN'S SIZES, AT ALL PUBLIC FILES IN THE GOALS' SCOPE.** -/
theorem inSizes_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (a r c : Nat) (hin : InFour X.hS X.HLy (OnBytes.Model.Verify.borderOf X.y) a r c) :
    a < (Meaning.sizesOf X 24).NM ∧ c < (Meaning.sizesOf X 24).k a ∧
      r < (Meaning.sizesOf X 24).m a := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have hN4 : X.hS.NHf = 4 := B.full.NHf
  obtain ⟨stream, _, hm, hNM⟩ := _root_.Fo.Pub.public_mats h
  have e : Meaning.tlAt X 24 = X.H.tl := by
    unfold Meaning.tlAt
    simp
  show a < (Meaning.tlAt X 24).NM ∧ c < ((Meaning.tlAt X 24).mats.getD a {}).k ∧
    r < ((Meaning.tlAt X 24).mats.getD a {}).m
  rw [e, hNM, hm]
  unfold OnBytes.Model.Head.matsH
  rw [hN4]
  unfold InFour at hin
  rw [hN4] at hin
  rcases hin with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · interval_cases a <;> simp [List.range, List.range.loop, List.zipIdx] <;> exact ⟨h3, h2⟩
  · subst h1
    simp [List.range, List.range.loop, List.zipIdx]
    exact ⟨h3, h2⟩
  · subst h1
    simp [List.range, List.range.loop, List.zipIdx]
    exact ⟨h3, h2⟩
  · subst h1
    simp [List.range, List.range.loop, List.zipIdx]
    exact ⟨h3, h2⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.inRanges_of_numbers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.inRanges_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.inSizes_in_scope
