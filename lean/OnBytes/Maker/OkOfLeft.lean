-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfLeft.lean: the clause l₂ of the makers' test `rowFitAt` (`RowFit`,
OnBytes/Maker/RowFit.lean) follows from `Three.Whole.fits` by the one table of trees alone; and the
makers' tests on three lists of rounds (`okAt`, OnBytes/Maker/Files.lean) from eight parts of them
(`LeftOf5`), at the record of a reading and at the values of the program's two readers.

The clause (`RowLeft`, OnBytes/Maker/OkOfRow.lean): a tree of an earlier chain that the third
chain opens stands in the list of trees left behind the second chain, at the depth that the data
give it. Both sides are read off one table: the list of trees left keeps the number and the depth
of each tree that a later chain opens; the data's depth is that of the n-th of the rounds' trees
laid in a row, which is what the table's rows hold.

Main names:
  `zipIdx_fst`, `mem_zipIdx_of_mem`, `find_zipIdx`: on numbered lists.
  `treeShT_flat`, `treesOfChain_shapes`, `treesOfChain_opened`, `flat_dropLast`: the shapes of a
    chain's trees; a chain's rows of the table.
  `left_find`: a tree is found in the list of trees left under its number. `third_opened`: an
    opening of the third chain's data stands in the list of all openings.
  `rowLeft_of_fits`: the clause.
  `LeftOf5`: what is left: eight fields. `okAt_of_read5`: the whole test from the record of a
    reading.
  `okAt_key`, `okAt_proof`: the same from a value of the program's reader of a key file or of a
    proof file, at `dryKey` and `dryProof` as OnBytes/Maker/Files.lean defines them, at every key
    that is alike to the reading's.

Limits: `LeftOf5` is a premise, shown of no lists: at most two roots a message; the clause on the
table of trees (sent no later than opened; one shape); the clause on the labels' numbers; the two
seals (kind, no item, no work); no other sealed round; `storedFit`; two rounds in the first chain.
Each is a part of `okAt` itself. At a proof file the block is the call's own, with two premises on
it (hb, pl₁): that the dry run of another request's block states the same list is not shown here.
`okAt` is one of three tests; the two others, `shapesFit` and `sealBare`, follow from it
(OnBytes/Maker/OkOfShapes.lean). A statement on a file
may ask further tests of the data; nothing is said on these here. Nothing on soundness.
-/
import OnBytes.Maker.OkOfFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK OnBytes.Tie.Pv.Keeps.Plain
open OnBytes.Three (rootsIn treesOfChain)
open OnBytes.Params (Rounds)

/-! ### Lists -/

theorem zipIdx_fst {α : Type} : ∀ (l : List α) (k : ℕ), (l.zipIdx k).map Prod.fst = l
  | [], _ => rfl
  | x :: l, k => by rw [List.zipIdx_cons, List.map_cons, zipIdx_fst l (k + 1)]

theorem mem_zipIdx_of_mem {α : Type} : ∀ (l : List α) (k : ℕ) (x : α), x ∈ l →
    ∃ i, (x, i) ∈ l.zipIdx k
  | [], _, _, h => by cases h
  | y :: l, k, x, h => by
    rw [List.zipIdx_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨k, List.mem_cons_self ..⟩
    · obtain ⟨i, hi⟩ := mem_zipIdx_of_mem l (k + 1) x h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

/-- The first member of a numbered list that passes Q and has the number k + j is the member at the
place j, if that passes Q. -/
theorem find_zipIdx {α : Type} (Q : α × ℕ → Bool) : ∀ (l : List α) (k j : ℕ) (x : α),
    l[j]? = some x → Q (x, k + j) = true →
    (l.zipIdx k).find? (fun t => Q t && t.2 == k + j) = some (x, k + j)
  | [], _, _, _, h, _ => by cases h
  | y :: l, k, 0, x, h, hq => by
    have e : y = x := Option.some.inj h
    rw [List.zipIdx_cons, List.find?_cons, e]
    have : (Q (x, k) && (x, k).2 == k + 0) = true := by
      rw [Nat.add_zero] at hq ⊢
      simp [hq]
    rw [this]
    rfl
  | y :: l, k, j + 1, x, h, hq => by
    have h' : l[j]? = some x := h
    rw [List.zipIdx_cons, List.find?_cons]
    have : (Q (y, k) && (y, k).2 == k + (j + 1)) = false := by
      have : ((y, k).2 == k + (j + 1)) = false := by
        show (k == k + (j + 1)) = false
        rw [beq_eq_false_iff_ne]
        omega
      rw [this, Bool.and_false]
    rw [this]
    have e : k + (j + 1) = (k + 1) + j := by omega
    rw [e] at hq ⊢
    exact find_zipIdx Q l (k + 1) j x h' hq

/-! ### The shapes of a chain's trees -/

/-- How the shape of a chain's tree number n unfolds at a first round. -/
theorem treeShT_step (d : RDT) (ds : List RDT) (n : ℕ) : treeShT (d :: ds) n =
    if n < d.trees.length then d.trees[n]? else treeShT ds (n - d.trees.length) := rfl

/-- The shape of a chain's tree number n is the n-th of the rounds' trees laid in a row. -/
theorem treeShT_flat : ∀ (ds : List RDT) (n : ℕ), treeShT ds n = (ds.flatMap (·.trees))[n]?
  | [], _ => rfl
  | d :: ds, n => by
    rw [treeShT_step, List.flatMap_cons]
    split
    · rename_i h
      rw [List.getElem?_append_left h]
    · rename_i h
      rw [List.getElem?_append_right (Nat.le_of_not_lt h), treeShT_flat ds]

theorem rows_shapes : ∀ (ds : List Three.RDL) (k : ℕ),
    (((ds.zipIdx k).flatMap fun d => d.1.trees.zipIdx.map fun s => (d.2, s.2, s.1)).map
      fun x => x.2.2) = ds.flatMap (·.trees)
  | [], _ => rfl
  | d :: ds, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append, rows_shapes ds (k + 1),
      List.flatMap_cons, List.map_map]
    exact congrArg (· ++ _) (zipIdx_fst d.trees 0)

/-- The shapes in a chain's rows of the table are the rounds' trees laid in a row. -/
theorem treesOfChain_shapes (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (here base : ℕ)
    (ds : List Three.RDL) :
    (treesOfChain all here base ds).map (·.shape) = ds.flatMap (·.trees) := by
  unfold treesOfChain
  rw [List.map_map, ← rows_shapes ds 0]
  have e : ∀ l : List (ℕ × ℕ × Fmt.Shape), l.zipIdx.map
      ((fun t : Three.Tree => t.shape) ∘ fun x : (ℕ × ℕ × Fmt.Shape) × ℕ =>
        (⟨here, x.1.1, x.1.2.1, x.1.2.2, (all.filter (·.1 == base + x.2)).map (·.2.2)⟩ :
          Three.Tree)) = l.map fun x => x.2.2 := fun l => by
    conv_rhs => rw [← zipIdx_fst l 0, List.map_map]
    rfl
  exact e _

/-- Where the n-th row of a chain's trees is opened. -/
theorem treesOfChain_opened (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (here base : ℕ)
    (ds : List Three.RDL) (n : ℕ) (t : Three.Tree)
    (h : (treesOfChain all here base ds)[n]? = some t) :
    t.openedAt = (all.filter (·.1 == base + n)).map (·.2.2) := by
  unfold treesOfChain at h
  rw [List.getElem?_map] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [List.getElem?_zipIdx] at hx
  obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 hx
  show (all.filter (·.1 == base + (0 + n))).map (·.2.2) = _
  rw [Nat.zero_add]

/-! ### The list of trees left -/

/-- A tree of the table that a chain up to c has sent and a chain behind c opens is found in the
list of trees left behind c under its number, at its shape's depth. -/
theorem left_find (W : Three.Whole) (c j : ℕ) (t : Three.Tree) (h : W.table[j]? = some t)
    (hc : t.chain ≤ c) (ho : ∃ o ∈ t.openedAt, c < o.1) :
    ((leftAfter W c).find? (·.no == j)).map (·.a) = some t.shape.a := by
  have hq : (fun t : Three.Tree × ℕ => decide (t.1.chain ≤ c) &&
      t.1.openedAt.any fun o => decide (c < o.1)) (t, 0 + j) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact ⟨hc, ho⟩
  have k := find_zipIdx (fun t : Three.Tree × ℕ => decide (t.1.chain ≤ c) &&
      t.1.openedAt.any fun o => decide (c < o.1)) W.table 0 j t h hq
  rw [Nat.zero_add] at k
  unfold leftAfter
  rw [List.find?_map, List.find?_filter]
  have e : (fun a : Three.Tree × ℕ => decide ((decide (a.1.chain ≤ c) &&
      a.1.openedAt.any fun o => decide (c < o.1)) = true ∧
      ((fun x : LeftT => x.no == j) ∘ fun t : Three.Tree × ℕ => (⟨t.2, t.1.shape.a⟩ : LeftT)) a =
        true)) = fun t : Three.Tree × ℕ => (decide (t.1.chain ≤ c) &&
      t.1.openedAt.any fun o => decide (c < o.1)) && t.2 == j := by
    funext x
    rw [Bool.decide_and, Bool.decide_eq_true, Bool.decide_eq_true]
    rfl
  rw [e, k]
  rfl

/-- The trees of the data's first list, laid in a row, are the first of the trees of the rounds'
data laid in a row. -/
theorem flat_dropLast (l : List Three.RDL) (j : ℕ)
    (h : j < ((l.dropLast.map rdtOf).map (·.trees.length)).sum) :
    ((l.dropLast.map rdtOf).flatMap (·.trees))[j]? = (l.flatMap (·.trees))[j]? := by
  obtain ⟨u, hu⟩ := List.dropLast_prefix l
  have e : (l.dropLast.map rdtOf).flatMap (·.trees) = l.dropLast.flatMap (·.trees) := by
    rw [List.flatMap_map]
    rfl
  have hl : (l.dropLast.flatMap (·.trees)).length =
      ((l.dropLast.map rdtOf).map (·.trees.length)).sum := by
    rw [List.length_flatMap, List.map_map]
    rfl
  conv_rhs => rw [← hu, List.flatMap_append]
  rw [e, List.getElem?_append_left (by rw [hl]; exact h)]

/-- An opening of the third chain's data stands in the list of all openings, under the chain 2. -/
theorem third_opened (a : ℕ) (R₁ R₂ R₃ : Rounds) :
    ∀ d ∈ (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃, ∀ j ∈ d.opens,
      ∃ s i, (j, s, 2, i) ∈ (Three.Whole.of R₁ R₂ R₃).opens := by
  intro d hd j hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
  have hx' : x ∈ Three.rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) 2
      (rootsIn R₁ + rootsIn R₂) (Three.first₃ (rootsIn R₁)) R₃ := hx
  unfold Three.rdsFromL at hx'
  obtain ⟨r, hr, k, rfl⟩ := mem_zipWith'' _ _ _ _ hx'
  obtain ⟨u, hu, e⟩ := List.mem_filterMap.1 hj
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨i, hi⟩ := mem_zipIdx_of_mem R₃ 0 r hr
  refine ⟨u.1, i, ?_⟩
  have h3 : (Three.wholeNo (rootsIn R₁) (rootsIn R₂) y, u.1, 2, i) ∈
      Three.opensOf (rootsIn R₁) (rootsIn R₂) 2 R₃ := by
    unfold Three.opensOf
    refine List.mem_flatMap.2 ⟨(r, i), hi, List.mem_filterMap.2 ⟨u, hu, ?_⟩⟩
    show (Three.named 2 u.2).map _ = _
    rw [hy]
    rfl
  exact List.mem_append_right _ (List.mem_append_right _ h3)

/-- **The clause of `RowFit` on the third chain's openings of earlier chains' trees**, from
`Three.Whole.fits`, by the table alone. -/
theorem rowLeft_of_fits (a : ℕ) {R₁ R₂ R₃ : Rounds} {n : ℕ}
    (hf : Three.Whole.fits R₁ R₂ R₃ n = true) :
    RowLeft (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) (leftAfter (Three.Whole.of R₁ R₂ R₃) 1) := by
  have hc := countsFit_of_fits a hf
  unfold countsFit at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  have t₁ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₁ = rootsIn R₁ := hc.1
  have t₂ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₂ = rootsIn R₂ := hc.2
  have lA : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
      (Three.Whole.of R₁ R₂ R₃).ds₁).length = rootsIn R₁ := trees_count _ _ _ _ _ _ _ _ R₁
  have lB : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
      (Three.Whole.of R₁ R₂ R₃).ds₂).length = rootsIn R₂ := trees_count _ _ _ _ _ _ _ _ R₂
  have tab : (Three.Whole.of R₁ R₂ R₃).table =
      treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0 (Three.Whole.of R₁ R₂ R₃).ds₁ ++
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁) (Three.Whole.of R₁ R₂ R₃).ds₂ ++
      treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
        (Three.Whole.of R₁ R₂ R₃).ds₃) := rfl
  intro d hd j hj hlt
  obtain ⟨s, i, hall⟩ := third_opened a R₁ R₂ R₃ d hd j hj
  rw [t₁, t₂] at hlt
  unfold WholeD.depth
  rw [t₁, t₂]
  by_cases h1 : j < rootsIn R₁
  · rw [if_pos h1]
    have hj' : j < (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
        (Three.Whole.of R₁ R₂ R₃).ds₁).length := by rw [lA]; exact h1
    have g := List.getElem?_eq_getElem hj'
    have ht : (Three.Whole.of R₁ R₂ R₃).table[j]? = some ((treesOfChain
        (Three.Whole.of R₁ R₂ R₃).opens 0 0 (Three.Whole.of R₁ R₂ R₃).ds₁)[j]) := by
      rw [tab, List.getElem?_append_left hj', g]
    rw [left_find _ 1 j _ ht
      (by rw [treesOfChain_chain _ _ _ _ _ (List.getElem_mem hj')]; exact Nat.zero_le _)
      ⟨(2, i), by
        rw [treesOfChain_opened _ _ _ _ j _ g]
        exact List.mem_map.2 ⟨(j, s, 2, i), List.mem_filter.2 ⟨hall, by simp⟩, rfl⟩, by
        show 1 < 2
        omega⟩]
    rw [treeShT_flat]
    have fd := flat_dropLast (Three.Whole.of R₁ R₂ R₃).ds₁ j (by
      have : ((((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf).map (·.trees.length)).sum) =
          rootsIn R₁ := t₁
      rw [this]
      exact h1)
    have fd' : ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁.flatMap (·.trees))[j]? =
        ((Three.Whole.of R₁ R₂ R₃).ds₁.flatMap (·.trees))[j]? := fd
    rw [fd', ← treesOfChain_shapes (Three.Whole.of R₁ R₂ R₃).opens 0 0, List.getElem?_map, g]
    rfl
  · rw [if_neg h1, if_pos (by omega)]
    have hj' : j - rootsIn R₁ < (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
        (Three.Whole.of R₁ R₂ R₃).ds₂).length := by rw [lB]; omega
    have g := List.getElem?_eq_getElem hj'
    have ht : (Three.Whole.of R₁ R₂ R₃).table[j]? = some ((treesOfChain
        (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁) (Three.Whole.of R₁ R₂ R₃).ds₂)[j -
          rootsIn R₁]) := by
      rw [tab, List.getElem?_append_right (by rw [lA]; omega), lA,
        List.getElem?_append_left hj', g]
    rw [left_find _ 1 j _ ht
      (by rw [treesOfChain_chain _ _ _ _ _ (List.getElem_mem hj')])
      ⟨(2, i), by
        rw [treesOfChain_opened _ _ _ _ (j - rootsIn R₁) _ g]
        refine List.mem_map.2 ⟨(j, s, 2, i), List.mem_filter.2 ⟨hall, ?_⟩, rfl⟩
        show (j == rootsIn R₁ + (j - rootsIn R₁)) = true
        rw [beq_iff_eq]
        omega, by
        show 1 < 2
        omega⟩]
    rw [treeShT_flat]
    have e2 : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂.flatMap (·.trees) =
        (Three.Whole.of R₁ R₂ R₃).ds₂.flatMap (·.trees) := by
      show ((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf).flatMap (·.trees) = _
      rw [List.flatMap_map]
      rfl
    rw [e2, ← treesOfChain_shapes (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁),
      List.getElem?_map, g]
    rfl

/-! ### The whole test, from eight parts of it -/

/-- What of the makers' tests is not shown here to follow from a reading: eight parts of `okAt`;
`rowFitAt` is not among them. -/
structure LeftOf5 (a : ℕ) (R₁ R₂ R₃ : Rounds) : Prop where
  /-- no message has more than two roots: the format has no such bound -/
  few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ 2
  c3 : fits3 R₁ R₂ R₃ = true
  c4 : fits4 R₁ R₂ R₃ = true
  seal₁ : SealAt R₁
  seal₂ : SealAt R₂
  c6 : fits6 R₁ R₂ R₃ = true
  stored : storedFit a (Three.Whole.of R₁ R₂ R₃) = true
  /-- the first chain has a round beside its last -/
  two : 2 ≤ R₁.length

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

variable (a : ℕ)

/-- **The makers' tests pass at the lists of a file that was read, if `LeftOf5` holds of them.**
`rowFitAt` is no premise: `rowLeft_of_fits` with OnBytes/Maker/OkOfRow.lean pays it. -/
theorem okAt_of_read5
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁) (pl₁ : PlainRounds R₁)
    (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (L : LeftOf5 a R₁ R₂ R₃) :
    okAt a (some (R₁, R₂, R₃)) = true :=
  okAt_of_read4 a T hS₁ o₁ pl₁ b₁ R₃ hd
    ⟨L.few, L.c3, L.c4, L.seal₁, L.seal₂, L.c6, L.stored, L.two,
      rowLeft_of_fits a (fits_of_read T hS₁ o₁ b₁ R₃ hd L.few L.c3 L.c4 L.seal₁ L.seal₂ L.c6)⟩

end Read

variable (a : ℕ)

/-- **A key file.** Where the program's reader has returned r, the makers' tests pass at the dry
runs' lists at every key that is alike to r's, if what is left holds. -/
theorem okAt_key (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r) (key₀ : TableKey)
    (hk : KeyAlike key₀ r.key) (R : Rounds × Rounds × Rounds) (hR : dryKey k key₀ = some R)
    (L : LeftOf5 a R.1 R.2.1 R.2.2) : okAt a (dryKey k key₀) = true := by
  rw [dryKey_keyAlike hk k] at hR ⊢
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  have hR' : ((Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime)).bind
      (Three.dry3 (Key.tailPublic k noTable) r.key) = some R := hR
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own k.oneTime T.first_dry
  rw [hR]
  exact okAt_of_read5 a T hS₁' o₁ (plain_oneTime _ _ _ _ T.first_dry) b₁ R₃ hd L

/-- **A proof file**, at the call's own block, which carries the relation "alike" where no given
source is met and whose rounds note no opening with the mark "stored". -/
theorem okAt_proof (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
    (h : (readProof c table copy request words block file).fromStart = .ok r)
    (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block) (key₀ : TableKey)
    (hk : KeyAlike key₀ r.key) (R : Rounds × Rounds × Rounds)
    (hR : dryProof c key₀ block = some R) (pl₁ : PlainRounds R.1)
    (L : LeftOf5 a R.1 R.2.1 R.2.2) : okAt a (dryProof c key₀ block) = true := by
  rw [dryProof_keyAlike hk c block] at hR ⊢
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  have hR' : (block.dryRun (firstStart c.first)).bind
      (Three.dry3 (tailPublic c noTable) r.key) = some R := hR
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  rw [hR]
  exact okAt_of_read5 a T hS₁' o₁ pl₁ b₁ R₃ hd L

end OnBytes.Maker

#print axioms OnBytes.Maker.rowLeft_of_fits
#print axioms OnBytes.Maker.okAt_of_read5
#print axioms OnBytes.Maker.okAt_key
#print axioms OnBytes.Maker.okAt_proof
