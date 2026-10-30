-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkDigAt.lean: THE CLAUSE okDig OF THE PROMISE Ok (`DigStatic` at the
fixed structure and the snapshot's ledger: RestStatic.lean) AT A STATE, FROM THREE FACTS: by the
road of OkJoin.lean. A definition and theorems.
  `gD tl`: the nine planned readings of the structure that `DigStatic` reads: the lookup's public
    numbers, the arrays' numbers, the number of rows of cells, the number of combinations, the two
    calls, the number of matrices, the symbols' arrays, the number of blocks. `gD_blank`: none is
    one of the fourteen written fields. `g9_of_gD`: they give OkJoin.lean's seven.
  `dig_congr`: **two structures with the same nine readings and two ledgers whose arrays have the
    same looks have `DigStatic` together.**
  `okDig_at`: **okDig's body at `fixed9 φ s`** where the structure's nine readings are tlP's (h1),
    the snapshot's arrays have FP's looks (h2), and `DigStatic tlD tlP FP` (H).
Limits. h1 and h2 are shown of no state here, H of no plan. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RestStatic
import Johnson.Desc.First.Link.Law.OkJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.DgP
open _root_.Fo (CoefOK allPieces Frame PieceOK)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.TailClaims.Law (blank)

/-- **What `DigStatic` reads of the approximate range proof's structure.** -/
def gD (tl : HTailF2) :
    Forest.Shape × T2Map × ℕ × ℕ × CallZ × CallZ × ℕ × Array ℕ × ℕ :=
  (tl.f9, tl.ix, tl.mz, tl.tau, tl.z1, tl.z2, tl.NM, tl.gtTree, tl.blocks.size)

/-- It reads none of the fourteen written fields. -/
theorem gD_blank (u tl : HTailF2) : gD (blank u tl) = gD tl := rfl

section
variable {tl tl' : HTailF2}

theorem gD_parts (h : gD tl = gD tl') :
    tl.f9 = tl'.f9 ∧ tl.ix = tl'.ix ∧ tl.mz = tl'.mz ∧ tl.tau = tl'.tau ∧ tl.z1 = tl'.z1 ∧
      tl.z2 = tl'.z2 ∧ tl.NM = tl'.NM ∧ tl.gtTree = tl'.gtTree ∧
      tl.blocks.size = tl'.blocks.size := by
  unfold gD at h
  simp only [Prod.mk.injEq] at h
  exact h

/-- The nine give the seven of OkJoin.lean. -/
theorem g9_of_gD (h : gD tl = gD tl') : g9 tl = g9 tl' := by
  obtain ⟨_, e2, _, e4, e5, e6, e7, e8, e9⟩ := gD_parts h
  unfold g9
  rw [e2, e4, e5, e6, e7, e8, e9]

theorem zOf_of_gD (h : gD tl = gD tl') (q : ℕ) : tl.zOf q = tl'.zOf q := by
  obtain ⟨_, _, _, _, e5, e6, _⟩ := gD_parts h
  unfold HTailF2.zOf
  rw [e5, e6]

theorem piecesL_of_gD (h : gD tl = gD tl') (q : ℕ) : piecesL tl q = piecesL tl' q := by
  unfold piecesL
  rw [zOf_of_gD h]

theorem allPieces_of_gD (h : gD tl = gD tl') : allPieces tl = allPieces tl' := by
  unfold allPieces
  rw [zOf_of_gD h, zOf_of_gD h]

/-- **`DigStatic` HANGS ON THE NINE READINGS AND THE LOOKS ALONE.** -/
theorem dig_congr {tlD : HTailF2} (hg : gD tl = gD tl') {F F' : Fork}
    (hl : F.trees.toList.map look = F'.trees.toList.map look) (H : DigStatic tlD tl' F') :
    DigStatic tlD tl F := by
  obtain ⟨e1, e2, e3, e4, e5, e6, _, _, _⟩ := gD_parts hg
  have fr : Frame F' F := frame_of_looks (looks_array hl)
  refine ⟨⟨e1.trans H.same.f9, e2.trans H.same.ix, e3.trans H.same.mz, e4.trans H.same.tau,
      e5.trans H.same.z1, e6.trans H.same.z2⟩, fun q hq => ?_, fun q hq p hp => ?_, fun q hq => ?_,
    coefOK_congr (g9_of_gD hg) (coefOK_frame fr H.coef), fun a ha => ?_⟩
  · rw [zOf_of_gD hg]
    exact H.small q hq
  · rw [piecesL_of_gD hg] at hp
    have k := H.pieces q hq p hp
    rw [zOf_of_gD hg]
    exact ⟨by rw [e2]; exact k.tree, by rw [e3]; exact k.c0, k.le, k.pw, k.rp, k.b, k.bn, k.dvd,
      k.fit⟩
  · rw [piecesL_of_gD hg]
    exact H.apart q hq
  · rw [allPieces_of_gD hg] at ha
    rw [(fr.2 a.2.tree).1]
    exact H.inside a ha

end

/-- **THE CLAUSE okDig AT WHAT IS FIXED AT A STATE**: where the structure's nine readings are the
plan's, the snapshot's arrays have the plan's looks, and the plan has `DigStatic`. -/
theorem okDig_at {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
    (u : HTailF2) (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (s : S)
    (tlD tlP : HTailF2) (FP : Fork) (h1 : ∀ tl, s.tl? = some tl → gD tl = gD tlP)
    (h2 : ∀ p, atS.get? s = some p →
      (pubOf p).F.trees.toList.map look = FP.trees.toList.map look)
    (H : DigStatic tlD tlP FP) :
    ∀ tlb v, (π (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v →
      DigStatic tlD tlb v.F := by
  intro tlb v e1 e2
  have e1' : s.tl?.map (blank u) = some tlb := (congrArg Prod.fst (hπ s)).symm.trans e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 e1'
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (show (atS.get? s).map pubOf = some v from e2)
  exact dig_congr ((gD_blank u tl).trans (h1 tl htl)) (h2 p hp) H

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.g9_of_gD
#print axioms VerifiableInference.Desc.LinkJoin.dig_congr
#print axioms VerifiableInference.Desc.LinkJoin.okDig_at
