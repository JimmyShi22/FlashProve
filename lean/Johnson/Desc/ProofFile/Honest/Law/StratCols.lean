-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratCols.lean: a chain's opened columns, as the library's slot
computes them from wants (`wantsDecl`, Johnson/Desc/BlockSlot.lean; `viewOf`,
OnBytes/Maker/Whole.lean), compared with the columns that the functions of Honest/Frame.lean fill
from reads. No prover is named.

  `filterMap_some`, `flat_eq`   on lists
  `fillCols_nil_ok`   with no stored run to fall back on, every read has its words, and the columns
                      are the reads' own
  `wants_cols`       if a look-up of columns by wants agrees with the look-ups `stored` and `tree`
                      wherever these return a value, and the keys agree, then the wants, filled by
                      that look-up, are the columns that `fillCols` returns
  `opened_fits`       what the tests on the plan say of an opening: the tree's declared length and
                      width are those of the oracle message that its sender declares

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Fmt.Rules6Laws
import Johnson.Desc.BlockSlot
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (Want)

variable {Xi : Type}

theorem filterMap_some {α β : Type} (f : α → Option β) (g : α → β) : ∀ l : List α,
    (∀ a ∈ l, f a = some (g a)) → l.filterMap f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons_some (h a List.mem_cons_self), List.map_cons,
      filterMap_some f g l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem flat_eq {σ α β γ : Type} (L : σ → List Nat) (fw : σ → Nat → α) (fr : σ → Nat → β)
    (g : α → Option γ) (h : β → γ) : ∀ l : List σ,
    (∀ s ∈ l, ∀ x ∈ L s, g (fw s x) = some (h (fr s x))) →
    (l.flatMap fun s => (L s).map (fw s)).filterMap g = (l.flatMap fun s => (L s).map (fr s)).map h
  | [], _ => rfl
  | s :: l, H => by
    rw [List.flatMap_cons, List.flatMap_cons, List.filterMap_append, List.map_append,
      flat_eq L fw fr g h l fun s' hs' => H s' (List.mem_cons_of_mem _ hs'), List.filterMap_map,
      List.map_map]
    exact congrArg (· ++ _) (filterMap_some _ _ _ fun x hx => H s List.mem_cons_self x hx)

theorem fillCols_nil_ok : ∀ (q : List Read) (c : List OpenedColumn), fillCols q [] = .ok c →
    c = q.map (fun r => (r.key, r.pos, r.words.getD [])) ∧ ∀ r ∈ q, r.words.isSome = true
  | [], c, h => by
    simp only [fillCols] at h
    cases h
    exact ⟨rfl, fun r hr => by cases hr⟩
  | r :: q, c, h => by
    cases hw : r.words with
    | none => simp [fillCols, hw] at h
    | some u =>
      simp only [fillCols, hw, List.tail_nil] at h
      split at h
      · cases h
      obtain ⟨l, hl, rfl⟩ := exMap_ok h
      obtain ⟨e, ha⟩ := fillCols_nil_ok q l hl
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, hw, e]
        rfl
      · intro r' hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · rw [hw]
          rfl
        · exact ha r' hr'

/-- **The slot's columns are those of `fillCols`.** `num`, `key`: a tree's number through the whole
file and its key, as the slot has them. `col`: the slot's look-up of a column. `lay`: how the slot
turns a want and its column into a view's column. -/
theorem wants_cols (num : Fmt.TreeSource → Nat) (key : Nat → Nat) (col : Want → Option (List UInt64))
    (lay : Want → List UInt64 → OpenedColumn)
    (hl₁ : ∀ item x u, lay (.table item x) u = (Fmt.storedKey item, x, u))
    (hl₂ : ∀ j x u, lay (.tree j x) u = (key j, x, u))
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (l : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (c : List OpenedColumn),
    (∀ r ∈ l, ∀ o ∈ r.opens, key (num o.2) = o.1.tree - ft) →
    (∀ r ∈ l, ∀ s ∈ r.stored, ∀ x u, x < 2 ^ s.sh.a → stored s.item x = some u →
      col (.table s.item x) = some u) →
    (∀ r ∈ l, ∀ o ∈ r.opens, ∀ x pt, x < 2 ^ o.1.a → tree o.2 = some pt →
      col (.tree (num o.2) x) = some (pt.2.col x)) →
    fillCols (readsOf chain ft stored tree l Rs) [] = .ok c →
    ((wantsDecl num l Rs).filterMap fun w => (col w).map (lay w)) = c := by
  intro l Rs c hk hs ht hc
  obtain ⟨rfl, hall⟩ := fillCols_nil_ok _ _ hc
  clear hc
  induction l generalizing Rs with
  | nil => simp [wantsDecl, readsOf]
  | cons d l ih =>
    cases Rs with
    | nil => simp [wantsDecl, readsOf]
    | cons R Rs =>
      have hall' : ∀ r ∈ (d.stored.flatMap fun s =>
            (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
              (⟨Fmt.storedKey s.item, x, some s.item, none, none, stored s.item x, s.sh.W⟩ :
                Read)) ++
          (d.opens.flatMap fun o =>
            (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
              (⟨o.1.tree - ft, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
                (tree o.2).map (·.2.col x), o.1.W⟩ : Read)) ++
          readsOf chain ft stored tree l Rs, r.words.isSome = true := hall
      have ihh := ih Rs (fun r hr => hk r (List.mem_cons_of_mem _ hr))
        (fun r hr => hs r (List.mem_cons_of_mem _ hr))
        (fun r hr => ht r (List.mem_cons_of_mem _ hr))
        (fun r hr => hall' r (List.mem_append_right _ hr))
      simp only [wantsDecl, readsOf, List.filterMap_append, List.map_append, ihh]
      congr 1
      congr 1
      · refine flat_eq _ _ _ _ _ d.stored fun s hs' x hx => ?_
        have hx' : x < 2 ^ s.sh.a := by
          obtain ⟨z, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        have hsome := hall' _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.2 ⟨s, hs', List.mem_map.2 ⟨x, hx, rfl⟩⟩)))
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hsome
        have hu' : stored s.item x = some u := hu
        show (col (.table s.item x)).map (lay (.table s.item x)) =
          some (Fmt.storedKey s.item, x, (stored s.item x).getD [])
        rw [hs d List.mem_cons_self s hs' x u hx' hu', hu']
        exact congrArg some (hl₁ _ _ _)
      · refine flat_eq _ _ _ _ _ d.opens fun o ho x hx => ?_
        have hx' : x < 2 ^ o.1.a := by
          obtain ⟨z, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        have hsome := hall' _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨o, ho, List.mem_map.2 ⟨x, hx, rfl⟩⟩)))
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hsome
        have hu' : (tree o.2).map (·.2.col x) = some u := hu
        obtain ⟨pt, hpt, rfl⟩ := Option.map_eq_some_iff.1 hu'
        show (col (.tree (num o.2) x)).map (lay (.tree (num o.2) x)) =
          some (o.1.tree - ft, x, ((tree o.2).map (·.2.col x)).getD [])
        rw [ht d List.mem_cons_self o ho x pt hx' hpt, hpt, ← hk d List.mem_cons_self o ho]
        exact congrArg some (hl₂ _ _ _)

/-- **What the tests on the plan say of an opening.** `i`: the chain of the round that opens,
from 0. The tree's sender and number are those of `srcOf`. -/
theorem opened_fits {F : FileDescription Xi} (hp : F.planOk = true) {i : Nat} {l : List Fmt.DeclaredRound}
    (hi : (l, i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)]) {r : Fmt.DeclaredRound}
    (hr : r ∈ l) {o : Fmt.Shape × Fmt.TreeSource} (ho : o ∈ r.opens) {j : Nat} {L : List (Nat × Nat)}
    (hj : (L, j) ∈ [(sentOf F.first.blocksInOrder, 0), (sentOf F.shared.blocksInOrder, 1), (sentOf F.second.blocksInOrder, 2)])
    (hsrc : (srcOf i o.2).1 = j) : L[(srcOf i o.2).2]? = some (o.1.a, o.1.W) := by
  have h0 := ((F.planOk_ok).1 hp).opened
  have h1 := List.all_eq_true.1 h0 (L, j) hj
  simp only [Bool.and_eq_true] at h1
  have h2 := List.all_eq_true.1 h1.1 ((srcOf i o.2).2, o.1.a, o.1.W) (by
    unfold openedOwn
    refine List.mem_flatMap.2 ⟨(l, i), hi, List.mem_filterMap.2 ⟨o, List.mem_flatMap.2 ⟨r, hr, ho⟩,
      ?_⟩⟩
    cases ho2 : o.2 with
    | own n =>
      rw [ho2] at hsrc
      have hij : i = j := hsrc
      simp [srcOf, hij]
    | taken ch k =>
      rw [ho2] at hsrc
      have hcj : ch = j := hsrc
      simp [srcOf, hcj])
  exact beq_iff_eq.1 h2

end ProofFile.Honest

#print axioms ProofFile.Honest.filterMap_some
#print axioms ProofFile.Honest.flat_eq
#print axioms ProofFile.Honest.fillCols_nil_ok
#print axioms ProofFile.Honest.wants_cols
#print axioms ProofFile.Honest.opened_fits
