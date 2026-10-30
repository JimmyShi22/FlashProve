-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SizesBack.lean: THE LEDGER's SIZES, PULLED BACK OVER THE MERGE's ACCEPTING STEP: WHERE THE LEDGER BEHIND HAS ITS SIZES, SO HAS THE ONE IN FRONT. Theorems on
the texts.

Why. Several clauses of a link's Ok are had by stepping back along «reached» to a sub-protocol's accept, whose law asks that the ledger IN FRONT has its sizes (`Sized`). The
table's promise says that at the border at which it is held, which lies BEHIND. The library's `Later` carries the sizes forward alone. But `Fork.hide` writes by set!, and
taking slots moves «next»: so a text that turns the ledger by these two alone turns no array's length. SHOWN HERE OF THE MERGE; of no other text of the stretch.

What is said.
  `SameSizes F G`: the number of slots and the three arrays' lengths are the same. `SameSizes.back`: so `Sized G → Sized F`; `.fwd`; `.trans`.
  `hide_sizes`, `hideRun_sizes`: **a successful `Fork.hide`, and a successful run of them, NO PREMISE ON THE SIZES.**
  `merge_sizes`: at `headMergeDecide`'s yes: both states stand at the head, open, and `SameSizes` of their ledgers.
  `merge_pulls`: **so: a ledger is open behind and has its sizes ⊢ a ledger is open in front and has its sizes.**

Limits. The merge alone: the like at the lookups' decision is the lookup's files' to show. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.LedgerBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (decide_inv mergeHear_inv merge_ledger)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- The number of slots and the three arrays' lengths are the same. -/
def SameSizes (F G : Fork) : Prop :=
  G.ns = F.ns ∧ G.vp.size = F.vp.size ∧ G.mf.size = F.mf.size ∧ G.gotF.size = F.gotF.size

theorem SameSizes.refl (F : Fork) : SameSizes F F := ⟨rfl, rfl, rfl, rfl⟩

theorem SameSizes.trans {F G H : Fork} (h : SameSizes F G) (k : SameSizes G H) : SameSizes F H :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.trans h.2.2.2⟩

/-- **The sizes, pulled back.** -/
theorem SameSizes.back {F G : Fork} (h : SameSizes F G) (hG : Sized G) : Sized F := by
  obtain ⟨a, b, c, d⟩ := h
  obtain ⟨x, y, z⟩ := hG
  exact ⟨by omega, by omega, by omega⟩

theorem SameSizes.fwd {F G : Fork} (h : SameSizes F G) (hF : Sized F) : Sized G := by
  obtain ⟨a, b, c, d⟩ := h
  obtain ⟨x, y, z⟩ := hF
  exact ⟨by omega, by omega, by omega⟩

/-- A successful hiding turns no length. -/
theorem hide_sizes {F G : Fork} {j : ℕ} {y f : E} (h : F.hide j y f = some G) :
    SameSizes F G := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, by simp, by simp, by simp⟩
  · cases h

theorem hideList_sizes (f : E) : ∀ (l : List E) (x x' : ℕ × Fork),
    l.foldlM (Fork.hideStep f) x = some x' → SameSizes x.2 x'.2
  | [], x, x', h => by
    have e : x = x' := by simpa using h
    rw [e]
    exact SameSizes.refl _
  | y :: l, x, x', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨x₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨j, G⟩ := x
    obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.1 (show (G.hide j y f).map _ = some x₁ from h1)
    exact (hide_sizes hH).trans (hideList_sizes f l _ x' h2)

/-- **A successful run of hidings turns no length.** -/
theorem hideRun_sizes {F G : Fork} {first : ℕ} {v : Array E} {f : E}
    (h : F.hideRun first v f = some G) : SameSizes F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideList_sizes f v.toList (first, F) x hx
  · cases h

/-- **THE MERGE's ACCEPTING STEP TURNS NO LENGTH.** -/
theorem merge_sizes (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ a.opened = true ∧ a'.opened = true ∧
      SameSizes a.F a'.F := by
  obtain ⟨a, a', ha, ha', ho, ho', -⟩ := merge_ledger P h
  obtain ⟨a₁, a₁', tp, G, claim, x, wo, e1, e1', _, _, _, _, hm, hF, _⟩ := decide_inv h
  obtain ⟨_, _, _, _, _, v, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsF, hhide, _⟩ :=
    mergeHear_inv hm
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (First.Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (First.Here.head.inj e1').symm
  refine ⟨a₁, a₁', ha, ha', ho, ho', ?_⟩
  have k := hideRun_sizes hhide
  rw [hF]
  exact ⟨k.1, k.2.1, k.2.2.1, k.2.2.2⟩

/-- **THE SIZES, PULLED BACK OVER THE MERGE.** -/
theorem merge_pulls (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ G, s.fork? = some G ∧ Sized G := by
  obtain ⟨a, a', ha, ha', ho, ho', hz⟩ := merge_sizes P h
  obtain ⟨G', hG', hS⟩ := hB
  have e : a'.F = G' := by simpa [S.fork?, ha', ho'] using hG'
  exact ⟨a.F, by simp [S.fork?, ha, ho], hz.back (e ▸ hS)⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.SameSizes.back
#print axioms VerifiableInference.Desc.LinkJoin.hide_sizes
#print axioms VerifiableInference.Desc.LinkJoin.hideList_sizes
#print axioms VerifiableInference.Desc.LinkJoin.hideRun_sizes
#print axioms VerifiableInference.Desc.LinkJoin.merge_sizes
#print axioms VerifiableInference.Desc.LinkJoin.merge_pulls
