-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingPath.lean: the path of an opening that the typing of a whole file lays is a path
read off a table of vertices, in the form of OnBytes/TypedOracleCompiler/Joined/WalkTable.lean.

That file shows that the walk of a forest says yes if its checks are read off one consistent table
of vertices V (`FromTable`, `walk_of_table`). One of its four conditions is on the paths: the path
of a check at the leaf i of a tree of depth d is `tpath V d 0 i`, the table's entries at the
siblings on the way up. This file gives that form at a position of a stretch, with V the record of
vertices of an opening of the file (`vertexOf`, OnBytes/Maker/TablesPath.lean).

  `tpath_vertexOf`   `tpath` at a record of vertices, level by level.
  `opensT_tpath`     the path of the opening at a position is `tpath` at the record of an opening of
                     the position's tree that lists the position's leaf.
  `ext_tpath`        the same for a row of the stored table's table.

Not claimed. The other three conditions of `FromTable`. That the openings of one tree have one
record: where a tree is opened twice, two positions of it can have their paths from two records.
Nothing on soundness.


-/
import OnBytes.Maker.TablesPath
import OnBytes.TypedOracleCompiler.Joined.WalkTable

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (Row3)
open TypedOracleCompiler.Joined (tpath tpath_eq sibOf_eq_xor)

theorem tpath_vertexOf (a : ℕ) (seen : List (ℕ × ℕ × ByteArray)) (x : ℕ) :
    tpath (vertexOf a seen) a 0 x =
      (List.range a).map fun m => vertexOf a seen m ((x / 2 ^ m) ^^^ 1) := by
  rw [tpath_eq]
  exact List.map_congr_left fun m _ => by rw [Nat.zero_add, sibOf_eq_xor]

/-- **The path of the opening at a position, read off a table.** -/
theorem opensT_tpath {W : Three.Whole} {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))}
    (hp : TabsPath W r tabs) (C : _root_.Run.PQ.CK) (ds : List RDT) (base : ℕ)
    (q : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) q))
    (h : opensT C ds base tabs q = some op) :
    ∃ z, (base + treeAt C ds q, z) ∈ ownRowsW W r ∧ leafAt C ds q ∈ z.2.1 ∧
      op.path = tpath (vertexOf z.1.a z.2.2.seen) z.1.a 0 (leafAt C ds q) := by
  obtain ⟨z, hz, hx, e⟩ := opensT_path hp C ds base q op h
  exact ⟨z, hz, hx, by rw [e, tpath_vertexOf]⟩

/-- The same for a row of the stored table's table. -/
theorem ext_tpath {W : Three.Whole} {r : Proof.TailRead} {tab : List (ℕ × Row3)}
    (hp : ExtPath W r tab) (x : ℕ) (c : List UInt64) (s : Bits) (pt : List (Dig 256))
    (h : tab.lookup x = some (c, s, pt)) :
    ∃ t z, (t, z) ∈ storedRowsW W r ∧ x ∈ z.2.1 ∧
      pt = tpath (vertexOf z.1.a z.2.2.seen) z.1.a 0 x := by
  obtain ⟨t, z, hz, hx, e⟩ := hp x c s pt h
  exact ⟨t, z, hz, hx, by rw [pathFrom_eq e, tpath_vertexOf]⟩

end OnBytes.Maker
