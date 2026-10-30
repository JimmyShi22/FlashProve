-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WalksAt.lean: the paths of all checks of one tree, in the typing of a whole file, are
read off one table of vertices.

OnBytes/TypedOracleCompiler/Joined/WalkTable.lean shows that the walk of a forest says yes if its checks are read
off one consistent table of vertices V (`FromTable`: leaf, path, meets, root; `walk_of_table`). At
the typing of a whole file each forest is one tree of a stretch (OnBytes/Maker/ForestsAt.lean), and
the path of each opening is read out of the record of vertices of an opening of the file
(OnBytes/Maker/TablesRow.lean). A tree may be opened more than once in a file. Here the table of a
tree is made of the records of all its openings in a row, and the condition on the paths is shown
under one hypothesis: two openings of one tree hold one value at each vertex (`OneTable`).

  `recOf W r j`       the records of vertices of all openings of the tree j in the file, in a row.
  `OneTable W r j`    the hypothesis: two openings of the tree j hold one value at each vertex below
                      the top, and at the top's first place.
  `seenAt_append`, `seenAt_flat`, `seenAt_rec`
                      what one opening's record holds at such a vertex, the row holds there.
  `mapM_mono`, `pathFrom_mono`
                      a whole path that is read out of a record is read out of each record that
                      holds at least the same.
  `isTree_path`       **`FromTable`'s condition on the paths**, for a forest that is the tree number
                      n of a stretch, at V := `vertexOf` of the tree's depth and `recOf`.
  `isTree_walk`       so the walk of that forest says yes under g, given the other three conditions
                      at that V.

`OneTable` is not shown here (OnBytes/Maker/ReadWalks.lean has it for two openings with one root,
below the root). The other premises: `TabsRow`, `TabsHold`: both follow
where the tables return a value; the test `shapesFit`.

Not claimed. The conditions leaf, meets and root. Nothing on soundness.


-/
import OnBytes.Maker.ForestsAt
import OnBytes.Maker.TypingAt
import OnBytes.Maker.ReadNodes

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-- The records of vertices of all openings of the tree j in the file, in a row. -/
def recOf (W : Three.Whole) (r : Proof.TailRead) (j : ℕ) : List (ℕ × ℕ × ByteArray) :=
  ((ownRowsW W r).filter (·.1 == j)).flatMap (·.2.2.2.seen)

theorem mem_recOf {W : Three.Whole} {r : Proof.TailRead} {j : ℕ} {z : Opened}
    (hz : (j, z) ∈ ownRowsW W r) {u : ℕ × ℕ × ByteArray} (hu : u ∈ z.2.2.seen) :
    u ∈ recOf W r j :=
  List.mem_flatMap.2 ⟨(j, z), List.mem_filter.2 ⟨hz, beq_self_eq_true j⟩, hu⟩

/-- **A hypothesis on a file as read**: two openings of the tree j hold one value at each vertex
below the top, and at the top's first place. -/
def OneTable (W : Three.Whole) (r : Proof.TailRead) (j : ℕ) : Prop :=
  ∀ z z', (j, z) ∈ ownRowsW W r → (j, z') ∈ ownRowsW W r → ∀ d p v v', (d ≠ 0 ∨ p = 0) →
    seenAt z.2.2.seen d p = some v → seenAt z'.2.2.seen d p = some v' → v = v'

theorem seenAt_append (s s' : List (ℕ × ℕ × ByteArray)) (d p : ℕ) :
    seenAt (s ++ s') d p = (seenAt s d p).or (seenAt s' d p) := by
  unfold seenAt
  rw [List.find?_append]
  cases s.find? fun v => v.1 == d && v.2.1 == p <;> rfl

/-- The look-up in records in a row, where all that hold the vertex hold one value. -/
theorem seenAt_flat {α : Type} (f : α → List (ℕ × ℕ × ByteArray)) (d p : ℕ) (v : ByteArray) :
    ∀ l : List α, (∃ z ∈ l, seenAt (f z) d p = some v) →
      (∀ z ∈ l, ∀ v', seenAt (f z) d p = some v' → v' = v) →
      seenAt (l.flatMap f) d p = some v
  | [], ⟨_, hz, _⟩, _ => by cases hz
  | z0 :: l, ⟨z, hz, hv⟩, H => by
    rw [List.flatMap_cons, seenAt_append]
    cases e : seenAt (f z0) d p with
    | some v0 => rw [H z0 List.mem_cons_self v0 e]; rfl
    | none =>
      rcases List.mem_cons.1 hz with rfl | hz'
      · rw [e] at hv; cases hv
      · exact seenAt_flat f d p v l ⟨z, hz', hv⟩ fun y hy => H y (List.mem_cons_of_mem _ hy)

/-- What one opening's record holds at a vertex, the row holds there. -/
theorem seenAt_rec {W : Three.Whole} {r : Proof.TailRead} {j : ℕ} {z : Opened}
    (hone : OneTable W r j) (hz : (j, z) ∈ ownRowsW W r) {d p : ℕ} {v : ByteArray}
    (hdp : d ≠ 0 ∨ p = 0) (h : seenAt z.2.2.seen d p = some v) :
    seenAt (recOf W r j) d p = some v := by
  unfold recOf
  refine seenAt_flat (fun y : ℕ × Opened => y.2.2.2.seen) d p v
    ((ownRowsW W r).filter fun y => y.1 == j)
    ⟨(j, z), List.mem_filter.2 ⟨hz, beq_self_eq_true j⟩, h⟩ fun y hy v' hv' => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hy
  obtain ⟨j', y'⟩ := y
  obtain rfl : j' = j := by simpa using h2
  exact hone y' z h1 hz d p v' v hdp hv' h

theorem mapM_mono {α β : Type} (f g : α → Option β) : ∀ (l : List α) (bs : List β),
    (∀ a ∈ l, ∀ b, f a = some b → g a = some b) → l.mapM f = some bs → l.mapM g = some bs
  | [], _, _, h => h
  | a0 :: l, bs, H, h => by
    rw [List.mapM_cons] at h ⊢
    cases e0 : f a0 with
    | none => rw [e0] at h; cases h
    | some b0 =>
      cases e1 : l.mapM f with
      | none => rw [e0, e1] at h; cases h
      | some bs0 =>
        rw [e0, e1] at h
        rw [H a0 List.mem_cons_self b0 e0,
          mapM_mono f g l bs0 (fun a ha => H a (List.mem_cons_of_mem _ ha)) e1]
        exact h

/-- A whole path that is read out of a record is read out of each record that holds at least the
same. -/
theorem pathFrom_mono {a : ℕ} {s s' : List (ℕ × ℕ × ByteArray)} {x : ℕ} {pt : List (Dig 256)}
    (H : ∀ d p v, d ≠ 0 → seenAt s d p = some v → seenAt s' d p = some v)
    (h : pathFrom a s x = some pt) : pathFrom a s' x = some pt := by
  unfold pathFrom at h ⊢
  refine mapM_mono _ _ _ _ (fun k hk b hb => ?_) h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hk' := List.mem_range.1 hk
  rw [H _ _ _ (by omega) hv]
  rfl

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
  {tabs : List (ℕ × List (ℕ × Row3))} {K' : ℕ} {C : CK} {ds : List RDT} {base : ℕ}
  {A : RoundSplits (uLT C ds)} {Wr : RoundsQueryLayout 256 K' (uLT C ds) A}
  {emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L} {R : RootsOfChain 256 (uLT C ds)}
  {rd : OPos (uLT C ds) → Bool} {T : Forest 256 L} {n : ℕ} {sh : Fmt.Shape} {c : Dig 256}

/-- **The paths of all checks of one tree are read off one table.** -/
theorem isTree_path (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (hone : OneTable W r (base + n))
    (H : IsTree C ds Wr emb R rd (opensT C ds base tabs) T n sh c) :
    ∀ e ∈ T.cs, e.2.path =
      tpath (vertexOf sh.a (recOf W r (base + n))) T.depth 0 (e.1 * 2 ^ T.depth + e.2.j) := by
  intro e he
  obtain ⟨e0, q, op, hq, -, hop, he2⟩ := H.checks e he
  have hpl := place_posAtST C ds n e.2.j q hq
  have hn : treeAt C ds q = n := congrArg Prod.fst hpl
  have hx : leafAt C ds q = e.2.j := congrArg Prod.snd hpl
  obtain ⟨tab, col, ht, hl, -⟩ := opensT_some C ds base tabs q op hop
  obtain ⟨z, run, s0, hz, -, -, -, -, hp⟩ := hrow _ _ _ _ _ _ ht hl
  obtain ⟨t, ht', e1, -⟩ := htabs.row _ z hz
  have hT : treeShT ds (treeAt C ds q) = some z.1 := by
    rw [← hsh q, e1]
    exact shapesFit_at hshape ht'
  rw [hn] at hT hz
  obtain rfl : z.1 = sh := Option.some.inj (hT.symm.trans H.shape)
  rw [hx] at hp
  have hp' := pathFrom_mono (fun d p v hd hv => seenAt_rec hone hz (Or.inl hd) hv) hp
  have epath : e.2.path = op.path := by rw [he2]
  rw [epath, H.depth, e0, Nat.zero_mul, Nat.zero_add, pathFrom_eq hp', tpath_vertexOf]

/-- **So the walk of that forest says yes**, given the other three conditions at the same table. -/
theorem isTree_walk (g : Fam (typedOracleFamily 256 K' L)) (hrow : TabsRow W sb r tabs)
    (htabs : TabsHold W sb r tabs) (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (hone : OneTable W r (base + n))
    (H : IsTree C ds Wr emb R rd (opensT C ds base tabs) T n sh c)
    (hleaf : ∀ e ∈ T.cs, g OracleName.leaf e.2.inp =
      vertexOf sh.a (recOf W r (base + n)) 0 (e.1 * 2 ^ T.depth + e.2.j))
    (hmeets : ∀ m < T.depth,
      Meets (nodeAt g) (vertexOf sh.a (recOf W r (base + n))) m (Octopus.upN m T.idx))
    (hroot : ∀ m ∈ Octopus.upN T.depth T.idx,
      vertexOf sh.a (recOf W r (base + n)) T.depth m = T.treeRoot m) :
    walkP g T T.reads = true :=
  walk_of_table ⟨hleaf, isTree_path hrow htabs hshape hsh hone H, hmeets, hroot⟩

end

end OnBytes.Maker
