-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PlanAtData.lean: three fields of PlanAt (Johnson/Desc/K1/Law/NewAtSending.lean:
"the plan's side of a sending"): tree, listed and part: as lemmas general in the place: at ANY
sending of the first chain whose two rounds d₁ d₂ are the written data's own. Statements with their
proofs; each conclusion is the field's own text, to the letter. A law file; no running text imports
it.
  data_roots: each round of the first chain's data sends as many trees as its entry counts roots,
      where the written rounds' items do (hRoots: the conclusion of fits_roots)
  mem_of_stretch: the first of two rounds cut out of a list is in the list
  laid_of_own, trees_len: under the kind's own test on its parameters the trees can be laid; the
      place's list of trees is as long as the layout's
  tree_at_data: the field tree: (layOf P).tree.getD j 0 < d₁.trees.length, where d₁ is the data's
      round at the place and bears the sending's entry
  listed_of_tiled, listed_at_cut: the field listed: where the chain's sub-protocols fit the data
      (ChainFit: the premise of tiledOfFit), every piece q of the maker's cut has
      ListedAt F q.base q.ds
  cnt_lt: a message is counted among the earlier ones of its tree
  part_of_laid, part_of_own: the field part: no two messages of a place have one seat: TRUE BY THE
      MAKE OF THE LAYOUT, wherever one is made: a message's part is the number of earlier messages
      in its tree (layTrees_fits)

What is not claimed. ChainFit at the proof file's first chain and the frame's list of all trees: no
payer is named here. The fields told, mems, seats, fits. Nothing on soundness.

-/
import Johnson.Desc.Sound.TilesCutProofs
import Johnson.Desc.Book.BookFits
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.Port6
import OnBytes.Maker.ReadData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker OnBytes.Flat
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Book (LayFits layTrees_fits cnt)
open _root_.Run.PQ (CK)

/-! ## tree -/

/-- **Each round of the first chain's data sends as many trees as its entry counts roots.** -/
theorem data_roots (a : ℕ) (R₁ R₂ R₃ : Rounds)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots) :
    ∀ d ∈ (dataOf a R₁ R₂ R₃).ds₁, d.trees.length = d.entry.roots := by
  intro d hd
  have e : (dataOf a R₁ R₂ R₃).ds₁.map (fun d : RDT => (d.trees.length, d.entry.roots)) =
      (R₁.map fun r => (r.1.items.countP (· == .root), r.1.entry.roots)).dropLast := by
    show (((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast).map rdtOf).map _ = _
    rw [List.map_map, List.map_dropLast]
    exact congrArg List.dropLast (rdsFromL_map _ _ _ _ _ _
      ((fun d : RDT => (d.trees.length, d.entry.roots)) ∘ rdtOf)
      (fun r => (r.1.items.countP (· == Fmt.Item.root), r.1.entry.roots))
      (fun _ _ => by simp [rdtOf, Three.rdOf]) R₁)
  have hm : (d.trees.length, d.entry.roots) ∈
      (R₁.map fun r => (r.1.items.countP (· == .root), r.1.entry.roots)).dropLast := by
    rw [← e]
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  obtain ⟨r, hr, er⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hm)
  have e1 : r.1.items.countP (· == .root) = d.trees.length := congrArg Prod.fst er
  have e2 : r.1.entry.roots = d.entry.roots := congrArg Prod.snd er
  rw [← e1, ← e2]
  exact hRoots r hr

theorem mem_of_stretch {α : Type} {l : List α} {n : ℕ} {x y : α}
    (h : (l.drop n).take 2 = [x, y]) : x ∈ l := by
  have h1 : x ∈ (l.drop n).take 2 := by rw [h]; exact List.mem_cons_self
  exact List.mem_of_mem_drop (List.mem_of_mem_take h1)

theorem laid_of_own {P : Par} (hB : planOkOwn P = true) :
    layTrees P.codes P.sent = some (layOf P) := by
  unfold planOkOwn at hB
  have h1 := (Bool.and_eq_true_iff.1 hB).1
  unfold planOk at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1.2
  rw [Own.treesCan_eq] at h2
  obtain ⟨lay, hl⟩ := Option.isSome_iff_exists.1 h2
  unfold layOf
  rw [hl]
  rfl

theorem trees_len {P : Par} (hB : planOkOwn P = true) :
    P.trees.length = (layOf P).shapes.size := by
  unfold Par.trees
  rw [Own.treesMade_eq, laid_of_own hB]
  simp

/-- **The field tree**, at the data's own round. -/
theorem tree_at_data (a : ℕ) (R₁ R₂ R₃ : Rounds)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots) (n : ℕ) (d₁ d₂ : RDT)
    (hd : ((dataOf a R₁ R₂ R₃).ds₁.drop n).take 2 = [d₁, d₂]) (P : Par)
    (he : d₁.entry = seedEntry P) (hB : planOkOwn P = true) :
    ∀ j : Fin (shapesOf P).length, (layOf P).tree.getD j.val 0 < d₁.trees.length := by
  intro j
  rw [data_roots a R₁ R₂ R₃ hRoots d₁ (mem_of_stretch hd), he]
  show _ < P.trees.length
  rw [trees_len hB]
  have hj : j.val < P.sent.size := by
    have := j.isLt
    simpa [shapesOf] using this
  exact (layTrees_fits (laid_of_own hB) j.val hj).1

/-! ## listed -/

section
variable {C : CK} {F : Frame} {S Cl W : Type}

theorem listed_of_tiled : ∀ (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)), Tiled p l →
    ∀ q ∈ p :: l, q.Listed
  | p, [], h, q, hq => by
    obtain rfl := List.mem_singleton.1 hq
    exact h.2
  | p, p' :: l, h, q, hq => by
    obtain ⟨_, h2, _, _, h5⟩ := (tiled_cons p p' l).1 h
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact h2
    · exact listed_of_tiled p' l h5 q hq'

/-- **The field listed**, at every piece of the maker's cut. -/
theorem listed_at_cut (rest : (i : ℕ) → (ds : List RDT) → Sound.Rest C F S W ds)
    (putBack : List Fmt.RoundView) (dep : ℕ → Option ℕ) (l : List (Block S Cl)) (b : Block S Cl)
    (i base : ℕ) (ds : List RDT) (hFit : ChainFit F dep base b l ds putBack)
    (q : Piece C F S Cl W)
    (hq : q ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2) :
    ListedAt F q.base q.ds :=
  q.listedAt (listed_of_tiled _ _ (tiledOfFit C F S Cl W rest putBack dep l b i base ds hFit) q hq)

end

/-! ## part -/

theorem cnt_mono (tree : Array Nat) (τ : Nat) : ∀ {i k : Nat}, i ≤ k → cnt tree τ i ≤ cnt tree τ k
  | i, 0, h => by
    obtain rfl : i = 0 := Nat.le_zero.1 h
    exact Nat.le_refl _
  | i, k + 1, h => by
    rcases Nat.lt_or_ge i (k + 1) with h1 | h1
    · exact Nat.le_trans (cnt_mono tree τ (Nat.le_of_lt_succ h1)) (Nat.le_add_right _ _)
    · obtain rfl : i = k + 1 := Nat.le_antisymm h h1
      exact Nat.le_refl _

/-- A message is counted among the earlier ones of its tree. -/
theorem cnt_lt (tree : Array Nat) {i' i : Nat} (h : i' < i) :
    cnt tree (tree.getD i' 0) i' < cnt tree (tree.getD i' 0) i := by
  have h1 : cnt tree (tree.getD i' 0) (i' + 1) = cnt tree (tree.getD i' 0) i' + 1 := by
    show cnt tree (tree.getD i' 0) i' + (if tree.getD i' 0 = tree.getD i' 0 then 1 else 0) = _
    rw [if_pos rfl]
  have h2 := cnt_mono tree (tree.getD i' 0) (show i' + 1 ≤ i from h)
  omega

/-- **No two messages of one layout have one seat.** -/
theorem part_of_laid {n : Nat} {L : TreeLay} (h : LayFits n L) (i i' : ℕ) (hi : i < n)
    (hi' : i' < i) :
    (L.tree.getD i' 0, L.part.getD i' 0) ≠ (L.tree.getD i 0, L.part.getD i 0) := by
  intro e
  have e1 : L.tree.getD i' 0 = L.tree.getD i 0 := congrArg Prod.fst e
  have e2 : L.part.getD i' 0 = L.part.getD i 0 := congrArg Prod.snd e
  rw [(h i hi).2, (h i' (Nat.lt_trans hi' hi)).2, ← e1] at e2
  exact Nat.ne_of_lt (cnt_lt L.tree hi') e2

/-- **The field part**, under the kind's own test on its parameters. -/
theorem part_of_own {P : Par} (hB : planOkOwn P = true) :
    ∀ i i' : ℕ, i < P.sent.size → i' < i →
      ((layOf P).tree.getD i' 0, (layOf P).part.getD i' 0) ≠
        ((layOf P).tree.getD i 0, (layOf P).part.getD i 0) :=
  fun i i' hi hi' => part_of_laid (layTrees_fits (laid_of_own hB)) i i' hi hi'

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.data_roots
#print axioms VerifiableInference.Desc.K1.trees_len
#print axioms VerifiableInference.Desc.K1.tree_at_data
#print axioms VerifiableInference.Desc.K1.listed_of_tiled
#print axioms VerifiableInference.Desc.K1.listed_at_cut
#print axioms VerifiableInference.Desc.K1.part_of_laid
#print axioms VerifiableInference.Desc.K1.part_of_own
