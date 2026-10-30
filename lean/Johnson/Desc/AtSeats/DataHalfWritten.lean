-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/DataHalfWritten.lean (it imports
Johnson/Desc/AtSeats/ToldHalves.lean): THE DATA's HALF OF
THE FIELD told, AT THE THREE WRITTEN LISTS OF ROUNDS, AT EVERY PLACE OF THE FIRST CHAIN's LIST OF
ROUNDS' DATA: of the two rounds that stand at i₀, tree number n has the depth and the width of
laidFull[base + n], base the trees that the rounds in front send.

  zip_at           a round's data at place i is rdOf … r sent, sent the trees of the data in front:
                   by sentBefore_eq (Johnson/G/WholeTwin.lean), at any lists of rounds.
  dataHalf_of      THE HALF, AT ANY THREE LISTS OF ROUNDS, from a sentence on one round's data (H)
                   and "the data's trees are 83 at most". No list is unfolded.
  dataHalf_written  at the written lists: H is trees_of_round (ShapeAtWritten.lean).

PREMISES LEFT: ht : 83 ≤ rootsIn dryProofFull.1 · hT: the first chain's data send 83 trees at most
(both were compiled in other files; not shown here).
What is not claimed. That the rounds of a file in scope are the written lists. The declared half.
Nothing on soundness.

-/
import Johnson.Desc.AtSeats.ToldHalves
import Johnson.G.WholeTwin
import Johnson.G.TestsFlat
import OnBytes.Maker.WholeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Three OnBytes.Maker Johnson.G
open OnBytes.Params (Rounds)

theorem rdOf_trees_length (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (r : Fmt.Round × List Fmt.Stored) (sent : Nat) :
    (rdOf all t₁ t₂ here base first r sent).trees.length = r.1.items.countP (· == .root) := by
  simp [rdOf]

/-- A round's data at place i. -/
theorem zip_at (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat) :
    ∀ (R : Rounds) (a i : Nat) (x : RDL),
      (List.zipWith (rdOf all t₁ t₂ here base first) R (sentFrom a R))[i]? = some x →
      ∃ r, x = rdOf all t₁ t₂ here base first r (a +
        (((List.zipWith (rdOf all t₁ t₂ here base first) R (sentFrom a R)).take i).map
          (·.trees.length)).sum)
  | [], a, i, x, h => by simp [sentFrom] at h
  | r :: R, a, 0, x, h => by
    simp only [sentFrom, List.zipWith_cons_cons, List.getElem?_cons_zero,
      Option.some.injEq] at h
    exact ⟨r, by simp [h]⟩
  | r :: R, a, i + 1, x, h => by
    simp only [sentFrom, List.zipWith_cons_cons, List.getElem?_cons_succ] at h
    obtain ⟨r', e⟩ := zip_at all t₁ t₂ here base first R _ i x h
    refine ⟨r', ?_⟩
    rw [e]
    simp only [sentFrom, List.zipWith_cons_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
      rdOf_trees_length, Nat.add_assoc]

theorem sum_take_le (l : List Nat) (j : Nat) : (l.take j).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop j l, List.sum_append]
  exact Nat.le_add_right _ _

/-- One tree of one round's data of the list. -/
theorem tree_at (R₁ R₂ R₃ : Rounds)
    (H : ∀ r sent i sh, (rdOf (Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) 0 0 0 r
      sent).trees[i]? = some sh → sent + i < 83 → laidFull[sent + i]? = some (sh.a, sh.W))
    (hT : (((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf).map (·.trees.length)).sum ≤ 83)
    (i : Nat) (d : RDT) (hd : ((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf)[i]? = some d)
    (k : Nat) (sh : Fmt.Shape) (hk : d.trees[k]? = some sh) :
    laidFull[((((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf).take i).map (·.trees.length)).sum + k]? =
      some (sh.a, sh.W) := by
  set ds := (Whole.of R₁ R₂ R₃).stretch₁.map rdtOf with hds
  -- the bound
  have hlt : k < d.trees.length := (List.getElem?_eq_some_iff.1 hk).1
  have hi : i < ds.length := (List.getElem?_eq_some_iff.1 hd).1
  have hstep : ((ds.take (i + 1)).map (·.trees.length)).sum =
      ((ds.take i).map (·.trees.length)).sum + d.trees.length := by
    rw [List.take_succ, hd]
    simp
  have hle : ((ds.take (i + 1)).map (·.trees.length)).sum ≤ 83 := by
    rw [List.map_take]
    exact Nat.le_trans (sum_take_le _ _) hT
  have hb : ((ds.take i).map (·.trees.length)).sum + k < 83 := by omega
  -- the round's data
  obtain ⟨x, hx, rfl⟩ : ∃ x, (Whole.of R₁ R₂ R₃).stretch₁[i]? = some x ∧ rdtOf x = d := by
    rw [hds, List.getElem?_map] at hd
    exact Option.map_eq_some_iff.1 hd
  have hL : (Whole.of R₁ R₂ R₃).ds₁ = List.zipWith
      (rdOf (Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) 0 0 0) R₁ (sentFrom 0 R₁) :=
    rdsFromL_eq _ _ _ _ _ _ R₁
  have hi' : i < (Whole.of R₁ R₂ R₃).stretch₁.length := by
    rw [hds, List.length_map] at hi
    exact hi
  have hx' : (Whole.of R₁ R₂ R₃).ds₁[i]? = some x := by
    unfold Whole.stretch₁ at hx
    rw [List.dropLast_eq_take, List.getElem?_take] at hx
    split at hx
    · exact hx
    · cases hx
  have htk : (ds.take i).map (·.trees.length) =
      ((Whole.of R₁ R₂ R₃).ds₁.take i).map (·.trees.length) := by
    rw [hds, ← List.map_take, List.map_map]
    unfold Whole.stretch₁ at hi' ⊢
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left]
    · rfl
    · rw [List.length_dropLast] at hi'
      omega
  rw [hL] at hx'
  obtain ⟨r, e⟩ := zip_at _ _ _ _ _ _ R₁ 0 i x hx'
  rw [← hL, Nat.zero_add, ← htk] at e
  rw [e] at hk
  exact H r _ k sh hk hb

/-- **THE HALF, at any three lists of rounds.** -/
theorem dataHalf_of (R₁ R₂ R₃ : Rounds)
    (H : ∀ r sent i sh, (rdOf (Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) 0 0 0 r
      sent).trees[i]? = some sh → sent + i < 83 → laidFull[sent + i]? = some (sh.a, sh.W))
    (hT : (((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf).map (·.trees.length)).sum ≤ 83) (i₀ : Nat) :
    DataHalf ((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf) i₀
      ((((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf).take i₀).map (·.trees.length)).sum := by
  intro d₁ d₂ e n sh h
  set ds := (Whole.of R₁ R₂ R₃).stretch₁.map rdtOf with hds
  have g : ∀ j : Nat, ((ds.drop i₀).take 2)[j]? = ([d₁, d₂] : List RDT)[j]? := fun j => by rw [e]
  have h1 : ds[i₀]? = some d₁ := by
    have := g 0
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop] at this
    simpa using this
  have h2 : ds[i₀ + 1]? = some d₂ := by
    have := g 1
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop] at this
    simpa using this
  rw [treeSh_flat] at h
  have h' : (d₁.trees ++ d₂.trees)[n]? = some sh := by simpa using h
  by_cases c : n < d₁.trees.length
  · rw [List.getElem?_append_left c] at h'
    exact tree_at R₁ R₂ R₃ H hT i₀ d₁ h1 n sh h'
  · rw [List.getElem?_append_right (Nat.le_of_not_lt c)] at h'
    have k := tree_at R₁ R₂ R₃ H hT (i₀ + 1) d₂ h2 _ sh h'
    have hstep : ((ds.take (i₀ + 1)).map (·.trees.length)).sum =
        ((ds.take i₀).map (·.trees.length)).sum + d₁.trees.length := by
      rw [List.take_succ, h1]
      simp
    rw [← hds, hstep] at k
    have ee : ((ds.take i₀).map (·.trees.length)).sum + d₁.trees.length +
        (n - d₁.trees.length) = ((ds.take i₀).map (·.trees.length)).sum + n := by omega
    rw [ee] at k
    exact k

/-- **At the written lists.** -/
theorem dataHalf_written (ht : 83 ≤ rootsIn dryProofFull.1)
    (hT : (((Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).stretch₁.map rdtOf).map
      (·.trees.length)).sum ≤ 83) (i₀ : Nat) :
    DataHalf ((Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).stretch₁.map rdtOf) i₀
      ((((Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).stretch₁.map rdtOf).take
        i₀).map (·.trees.length)).sum :=
  dataHalf_of _ _ _ (fun r sent i sh h hi => trees_of_round _ _ ht r sent i sh h hi) hT i₀

end HashBuild
