-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/StoredRoot.lean: every opening of a stored table in a file as the program's reader has
read it walks to the root that stands in the statement of the chain that opens it; so, where the
second chain alone opens stored tables, all under one item, all these openings have one root and
give one value to each vertex.

Statements and proofs. OnBytes/Maker/ReadTrace.lean says of a stored table's opening as read that
its walk led to the root in the statement's item (`Fmt.itemRoot`). Here this is said at the members
of `storedRows` and `storedRowsW` (OnBytes/Maker/Tables.lean), and laid together with the record
of vertices (OnBytes/Maker/ReadWalks.lean). OnBytes/Maker/OneRoot.lean has the like for the trees.

Main names:
  `trace_stored`: in a trace every stored table's opening walks to its item's root.
  `stored_rootAt`: one chain, at the members of `storedRows`.
  `StoredSecond W`: the data's first and third chain open no stored table.
  `storedW_second`: then the members of `storedRowsW` are those of the second chain.
  `stored_root`: each walks to the root in the item 0 of the second chain's statement.
  `one_tableE`: two of them give one value to each vertex below the root, and at the root.
  `stored_walked`, `stored_size`: each is what the reader of an opening hands out at the second
    chain's configuration's digest; every vertex met has a value of 32 bytes.
Limits: `FileFits` (OnBytes/Maker/TablesFit.lean) and `StoredSecond` are premises, not proved here.
`StoredSecond` speaks of the data alone: the test `storedFit` gives it
(OnBytes/Maker/StoredOfFit.lean). `FileFits` speaks of the data and of the three descriptions: it is
no test, `fileFits_of` (OnBytes/Maker/DataFitsOf.lean) shows it. `one_tableE` also asks `Kept n₂`
(`readChain_kept`). The root is the one in the statement under which the chain was read: nothing is
said of what it commits to. Nothing on soundness (index binding included), opening-form binding, no
two openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.ReadSizes

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-- Of a description's round and a round as read: in front stand the stored tables' openings, each
with the root of its item in the statement. -/
def StoredAtRoot (st : ByteArray) (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) : Prop :=
  ∃ cs co : List OpenedY, ro.opens = cs ++ co ∧
    List.Forall₂ (fun (t : Fmt.Stored) (y : OpenedY) =>
      Fmt.itemRoot st t.item = some y.2.2.root) x.2 cs

/-- **In a trace every stored table's opening walks to its item's root.** -/
theorem trace_stored (h : HId) (cfg st : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) : ∀ (xs : List (Fmt.Round × List Fmt.Stored)) (ros : List Fmt.RoundOut)
      (c : Fmt.Chain) (roots : Array ByteArray), TraceX h cfg st P run b xs ros c roots →
    List.Forall₂ (StoredAtRoot st) xs ros
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, _, T => T.elim
  | _ :: _, [], _, _, T => T.elim
  | x :: xs, ro :: ros, c, roots, T => by
    obtain ⟨R, T'⟩ := T
    refine .cons ?_ (trace_stored h cfg st P run b xs ros _ _ T')
    obtain ⟨cs, co, ho, h1, -⟩ := R.opens
    refine ⟨cs, co, ho, h1.imp fun t y hy => ?_⟩
    obtain ⟨root, hr, O⟩ := hy
    rw [O.rootIs]
    exact hr

/-- **One chain**: each member of `storedRows` walks to the root of its item in the statement. -/
theorem stored_rootAt (W : Three.Whole) (ds : List Three.RDL) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (F : DataFits W (S.base.rounds.zip S.stored) ds) :
    ∀ y ∈ storedRows ds o, Fmt.itemRoot S.base.statement y.1.item = some y.2.2.2.root := by
  obtain ⟨-, -, -, -, T⟩ := readChain_trace S seen b i o j e
  have R := trace_stored Fmt.formatHash _ _ _ _ b _ _ _ _ T
  have F' : List.Forall₂ (fun (x : Fmt.Round × List Fmt.Stored) (d : Three.RDL) =>
      RoundData W (keyOf x) d) (S.base.rounds.zip S.stored) ds := List.forall₂_map_left_iff.1 F
  rintro ⟨t, z⟩ hy
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hy
  obtain ⟨x, ⟨hx, -⟩, cs, co, ho, h1⟩ := (List.forall₂_iff_zip.1 (forall₂_join R F')).2 hp
  have hx' : x.2 = d.stored := hx
  rw [hx'] at h1
  have hin' : (t, z) ∈ d.stored.zip ro.opens := hin
  rw [ho, zip_append_more _ _ _ h1.length_eq] at hin'
  exact (List.forall₂_iff_zip.1 h1).2 hin'

/-- The data's first and third chain open no stored table. -/
def StoredSecond (W : Three.Whole) : Prop :=
  (∀ d ∈ W.ds₁, d.stored = []) ∧ ∀ d ∈ W.ds₃, d.stored = []

theorem storedRows_none {ds : List Three.RDL} (h : ∀ d ∈ ds, d.stored = []) (o : Fmt.ChainOut) :
    ∀ y, y ∉ storedRows ds o := by
  intro y hy
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hy
  have hin' : y ∈ d.stored.zip ro.opens := hin
  rw [h d (List.of_mem_zip hp).1] at hin'
  simp at hin'

/-- Then the members of `storedRowsW` are those of the second chain. -/
theorem storedW_second {W : Three.Whole} (hs : StoredSecond W) {r : Proof.TailRead}
    {y : Fmt.Stored × Opened} (hy : y ∈ storedRowsW W r) : y ∈ storedRows W.ds₂ r.shared.out := by
  rcases List.mem_append.1 hy with hy | hy
  · exact absurd hy (storedRows_none hs.1 _ y)
  · rcases List.mem_append.1 hy with hy | hy
    · exact hy
    · exact absurd hy (storedRows_none hs.2 _ y)

/-- A member of `storedRows` stands with a stored table of the data. -/
theorem stored_of {ds : List Three.RDL} {o : Fmt.ChainOut} {y : Fmt.Stored × Opened}
    (hy : y ∈ storedRows ds o) : ∃ d ∈ ds, y.1 ∈ d.stored := by
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hy
  exact ⟨d, (List.of_mem_zip hp).1, (List.of_mem_zip hin).1⟩

/-- Each is what the reader of an opening hands out at the second chain's configuration's digest.
-/
theorem stored_walked (W : Three.Whole) (hs : StoredSecond W) (S₂ : Fmt.SpecX) (r : Proof.TailRead)
    (b : ByteArray) (n₂ : Fmt.Seen) (i₂ j₂ : ℕ)
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂)) :
    ∀ y ∈ storedRowsW W r, Walked Fmt.formatHash S₂.base.cfg y.2 := by
  intro y hy
  obtain ⟨ro, hro, hz⟩ := stored_mem (storedW_second hs hy)
  exact (readChain_entered S₂ n₂ b i₂ _ j₂ e₂).1 ro hro y.2 hz

/-- Every vertex met in an opening of a stored table has a value of 32 bytes. -/
theorem stored_size (W : Three.Whole) (hs : StoredSecond W) (S₂ : Fmt.SpecX) (r : Proof.TailRead)
    (b : ByteArray) (n₂ : Fmt.Seen) (i₂ j₂ : ℕ)
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂)) :
    ∀ y ∈ storedRowsW W r, ∀ u ∈ y.2.2.2.seen, u.2.2.size = 32 := fun y hy =>
  walked_size_H _ (stored_walked W hs S₂ r b n₂ i₂ j₂ e₂ y hy)

section
variable (W : Three.Whole) (sb a : ℕ) (S₁ S₂ S₃ : Fmt.SpecX) (F : FileFits W sb a S₁ S₂ S₃)
  (hs : StoredSecond W) (r : Proof.TailRead) (b : ByteArray)
include F hs

/-- **Each opening of a stored table walks to the root in the item 0 of the second chain's
statement.** -/
theorem stored_root (n₂ : Fmt.Seen) (i₂ j₂ : ℕ)
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂)) :
    ∀ y ∈ storedRowsW W r, Fmt.itemRoot S₂.base.statement 0 = some y.2.2.2.root := by
  intro y hy
  have hy2 := storedW_second hs hy
  obtain ⟨d, hd, ht⟩ := stored_of hy2
  have h0 := stored_rootAt W W.ds₂ S₂ n₂ b i₂ _ j₂ e₂ F.d₂ y hy2
  rw [(F.a₂ d hd y.1 ht).2] at h0
  exact h0

/-- **One table of vertices for the stored table**: two openings of stored tables give one value to
each vertex below the root, and at the root. n₂: the record of vertices from which the second chain
was read; hk: in it no vertex has two values under one root. -/
theorem one_tableE (n₂ : Fmt.Seen) (hk : Kept n₂) (i₂ j₂ : ℕ)
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂)) :
    ∀ y ∈ storedRowsW W r, ∀ y' ∈ storedRowsW W r, ∀ (d p : ℕ) (v v' : ByteArray),
      (d ≠ 0 ∨ p = 0) → seenAt y.2.2.2.seen d p = some v → seenAt y'.2.2.2.seen d p = some v' →
      v = v' := by
  intro y hy y' hy' d p v v' hd hv hv'
  have R := stored_root W sb a S₁ S₂ S₃ F hs r b n₂ i₂ j₂ e₂
  have hr : y.2.2.2.root = y'.2.2.2.root :=
    Option.some.inj ((R y hy).symm.trans (R y' hy'))
  have Wk := stored_walked W hs S₂ r b n₂ i₂ j₂ e₂
  by_cases h0 : d = 0
  · have hp : p = 0 := by
      rcases hd with hd | hd
      · exact absurd h0 hd
      · exact hd
    subst h0 hp
    rw [(walked_nodes Fmt.formatHash _ (Wk y hy)).2] at hv
    rw [(walked_nodes Fmt.formatHash _ (Wk y' hy')).2] at hv'
    rw [← Option.some.inj hv, ← Option.some.inj hv']
    exact hr
  · obtain ⟨w, E⟩ := readChain_entered S₂ n₂ b i₂ _ j₂ e₂
    have mem : ∀ z ∈ storedRowsW W r,
        z.2 ∈ r.shared.out.rounds.toList.flatMap (·.opens) := fun z hz => by
      obtain ⟨ro, hro, hzz⟩ := stored_mem (storedW_second hs hz)
      exact List.mem_flatMap.2 ⟨ro, hro, hzz⟩
    exact same_root_agree E hk (fun z hz => by
        obtain ⟨ro, hro, hzz⟩ := List.mem_flatMap.1 hz
        exact walked_one Fmt.formatHash _ (w ro hro z hzz)) y.2 y'.2 (mem y hy) (mem y' hy') hr
      (d, p, v) (seenAt_mem hv) (d, p, v') (seenAt_mem hv') h0 rfl rfl

end

/-- The record that a chain's reading leaves is in order, if the one from which it began was. -/
theorem readChain_kept (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) (hk : Kept seen) :
    Kept o.seen := by
  obtain ⟨w, E⟩ := readChain_entered S seen b i o j e
  exact (entered_kept E hk fun z hz => by
    obtain ⟨ro, hro, hzz⟩ := List.mem_flatMap.1 hz
    exact walked_one Fmt.formatHash _ (w ro hro z hzz)).1

end OnBytes.Maker
