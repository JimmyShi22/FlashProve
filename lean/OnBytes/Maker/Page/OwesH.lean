-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/OwesH.lean: what the openings of a file give to a walk over whole paths
(`TreesOwed`, `StoredOwed`: OnBytes/Maker/OwesOfRead.lean), with the hash as a letter h: for three
chains that the strict reader reads at h with the outcome that the verifier program's reader had.

Statements and proofs. Of the five fields of each record three name no hash: one value at each
vertex, 32 bytes, the root. They are taken over from the records at the format's hash. Two name it:
each opening is what the reader of an opening hands out at h, and the bottom level holds the leaf's
hash at h. These are shown anew from the three equations of the strict reader at h, by the laws of
OnBytes/Maker/ReadWalks.lean, ReadTrace.lean, OneRoot.lean, StoredRoot.lean and ReadLeaf.lean that
are general in the hash. What ties a description's names to the data's numbers (`SrcFits`), the
counts of roots and `FileFits` name no hash either.

Main names:
  `OpensTreeH h W r x`: `OpensTree` with the hash as a letter.
  `round_treeAtH`, `chain_treeAtH`, `own_treeAtH`: at the members of `ownRowsW`.
  `own_walkedH`, `own_leafH`: the two fields for the trees.
  `stored_readAtH`, `stored_walkedH`, `stored_leafH`: the two fields for the stored table.
  `TreesOwedH h W r cfg`, `StoredOwedH h W r cfg st`: the two records.
  `ReadAt h S₁ S₂ S₃ file i r`: the three equations of the strict reader at h.
  `treesOwedH_of_readX`, `storedOwedH_of_readX`: from `ThreeRead`, `ReadAt h` and the premises of
    `treesOwed_of_read` and `storedOwed_of_read`.
Under "there is": in `TreesOwedH.leaf` the start, fixed by `runOfTree W r z.1 = some start`; in
`TreesOwedH.root` the start, fixed inside `TreeAt`. `Walked` and `OpensTreeH` hold letters of the
reader's call (field, bytes of a salt, file, place; `OpensTreeH` also cfg) that nothing else ties.
Limits: that the strict reader reads at h with that outcome is a premise (at the hash over the
realised oracle: OnBytes/Maker/Page/AtOracle.lean). The tests on the data are premises. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
beyond the reader's record or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.OwesOfRead

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)
open OnBytes.Three (rootsIn)
open OnBytes.Params (Rounds)

section
variable (h : HId)

/-! ## The trees -/

/-- What is said of an opening under the number j, at the hash h. -/
def OpensTreeH (W : Three.Whole) (r : TailRead) (x : ℕ × Opened) : Prop :=
  ∃ start, TreeAt W r x.1 x.2.2.2.root start ∧ ∃ (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ)
    (b : ByteArray) (i : ℕ),
    Fmt.readOpeningW (m := Id) h cfg f salt x.2.1 start x.2.2.1 b i = some x.2.2.2

theorem round_treeAtH (W : Three.Whole) (r : TailRead) (c : ℕ) (hc : c ≤ 2) (cfg : ByteArray)
    (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) (d : Three.RDL)
    (H : RootedAt h cfg (chainOf r c).run (rootsOf3 r c) x ro)
    (hl : x.2.length = d.stored.length)
    (F : List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) j => SrcNames W r c s.2 j) x.1.opens d.opens) :
    ∀ z ∈ d.opens.zip (ro.opens.drop d.stored.length), OpensTreeH h W r z := by
  obtain ⟨cs, co, ho, l1, h2⟩ := H
  rintro ⟨j, y⟩ hz
  rw [ho, List.drop_left' (l1.trans hl)] at hz
  obtain ⟨s, hn, rs, hs, hroot, f, salt, b, i, hi⟩ :=
    (List.forall₂_iff_zip.1 (forall₂_join h2 F)).2 hz
  refine ⟨rs.2, ?_, cfg, f, salt, b, i, hi⟩
  show TreeAt W r j y.2.2.root rs.2
  rw [hroot]
  obtain ⟨sh, src⟩ := s
  cases src with
  | given ρ σ =>
    obtain rfl : (ρ, σ) = rs := Option.some.inj hs
    exact hn
  | own n =>
    have hn' : j = Three.wholeNo W.t₁ W.t₂ (c, n) := hn
    unfold srcFull at hs
    cases hr : (rootsOf3 r c)[n]? with
    | none => simp only [hr] at hs; cases hs
    | some ρ =>
      cases hu : (chainOf r c).run with
      | none => simp only [hr, hu] at hs; cases hs
      | some σ =>
        simp only [hr, hu] at hs
        obtain rfl : (ρ, σ) = rs := Option.some.inj hs
        exact ⟨c, n, hn', hc, hr, hu⟩

/-- One chain. -/
theorem chain_treeAtH (W : Three.Whole) (r : TailRead) (c : ℕ) (hc : c ≤ 2) (S : Fmt.SpecX)
    (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (ds : List Three.RDL)
    (e : Fmt.readChainX (m := Id) h S seen b i = some (chainOf r c, j))
    (full : rootsOf3 r c = (chainOf r c).rounds.toList.flatMap fun ro => Fmt.rootsOf ro.vals)
    (F : SrcFits W r c (S.base.rounds.zip S.stored) ds) :
    ∀ z ∈ ownRows ds (chainOf r c), OpensTreeH h W r z := by
  obtain ⟨-, -, -, -, T⟩ := readX_trace h S seen b i _ j e
  have R := trace_rooted h _ _ _ _ b _ _ _ _ T
  rw [show (#[] : Array ByteArray).toList ++
    ((chainOf r c).rounds.toList.flatMap fun ro => Fmt.rootsOf ro.vals) = rootsOf3 r c from by
      rw [full]; rfl] at R
  intro z hz
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hz
  obtain ⟨x, ⟨hl, hF⟩, hR⟩ := (List.forall₂_iff_zip.1 (forall₂_join R F)).2 hp
  exact round_treeAtH h W r c hc _ x ro d hR hl hF z hin

/-- The three equations of the strict reader at h, each chain from the record of vertices that the
chain before it left. -/
structure ReadAt (S₁ S₂ S₃ : Fmt.SpecX) (file : ByteArray) (i : ℕ) (r : TailRead) : Prop where
  first : Fmt.readChainX (m := Id) h S₁ [] file i = some (r.first.out, r.first.next)
  shared : Fmt.readChainX (m := Id) h S₂ r.first.out.seen file r.place.next =
    some (r.shared.out, r.shared.next)
  second : Fmt.readChainX (m := Id) h S₃ r.shared.out.seen file r.shared.next =
    some (r.second.out, r.second.next)

variable {h} {S₁ S₂ S₃ : Fmt.SpecX} {file : ByteArray} {i : ℕ} {r : TailRead}
  (A : ReadAt h S₁ S₂ S₃ file i r)
include A

/-- Every opening of a tree. -/
theorem own_treeAtH (W : Three.Whole) (F₁ : SrcFits W r 0 (S₁.base.rounds.zip S₁.stored) W.ds₁)
    (F₂ : SrcFits W r 1 (S₂.base.rounds.zip S₂.stored) W.ds₂)
    (F₃ : SrcFits W r 2 (S₃.base.rounds.zip S₃.stored) W.ds₃) :
    ∀ z ∈ ownRowsW W r, OpensTreeH h W r z := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact chain_treeAtH h W r 0 (by omega) S₁ _ file _ _ W.ds₁ A.first (roots_eq r.first) F₁ z hz
  · rcases List.mem_append.1 hz with hz | hz
    · exact chain_treeAtH h W r 1 (by omega) S₂ _ file _ _ W.ds₂ A.shared (roots_eq r.shared) F₂ z
        hz
    · exact chain_treeAtH h W r 2 (by omega) S₃ _ file _ _ W.ds₃ A.second (roots_eq r.second) F₃ z
        hz

/-- Every opening of a tree, at one configuration's digest. -/
theorem own_walkedH (W : Three.Whole) (cfg : ByteArray) (c₁ : S₁.base.cfg = cfg)
    (c₂ : S₂.base.cfg = cfg) (c₃ : S₃.base.cfg = cfg) :
    ∀ z ∈ ownRowsW W r, Walked h cfg z.2 := by
  obtain ⟨w₁, -⟩ := readX_entered h S₁ _ file _ _ _ A.first
  obtain ⟨w₂, -⟩ := readX_entered h S₂ _ file _ _ _ A.shared
  obtain ⟨w₃, -⟩ := readX_entered h S₃ _ file _ _ _ A.second
  rw [c₁] at w₁
  rw [c₂] at w₂
  rw [c₃] at w₃
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · obtain ⟨ro, hro, hy⟩ := own_mem hz
    exact w₁ ro hro z.2 hy
  · rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact w₂ ro hro z.2 hy
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact w₃ ro hro z.2 hy

omit A in
/-- A tree's opening, at the start that the tables lay. -/
theorem own_leafH {R₁ R₂ R₃ : Rounds} (h₁ : rootsIn R₁ = r.first.roots.length)
    (h₂ : rootsIn R₂ = r.shared.roots.length) (h₃ : rootsIn R₃ = r.second.roots.length)
    {z : ℕ × Opened} (O : OpensTreeH h (Three.Whole.of R₁ R₂ R₃) r z) :
    ∃ start, runOfTree (Three.Whole.of R₁ R₂ R₃) r z.1 = some start ∧
      ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), (x, col, salt) ∈ listed z.2 →
        seenAt z.2.2.2.seen z.2.1.a x = some (leafHash h z.2.1 start x col salt) := by
  obtain ⟨start, T, cfg, f, sb, b, k, e⟩ := O
  exact ⟨start, runOfTree_of_treeAt h₁ h₂ h₃ T, opening_leaf h cfg f sb start b k z.2 e⟩

/-! ## The stored table -/

omit A in
/-- One chain: each member of `storedRows` was read at the start cfg. -/
theorem stored_readAtH (W : Three.Whole) (ds : List Three.RDL) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (k : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) h S seen b k = some (o, j))
    (F : DataFits W (S.base.rounds.zip S.stored) ds) :
    ∀ y ∈ storedRows ds o, ∃ (f : Fmt.Fld) (sb : ℕ) (b' : ByteArray) (k' : ℕ),
      Fmt.readOpeningW (m := Id) h S.base.cfg f sb y.2.1 S.base.cfg y.2.2.1 b' k' =
        some y.2.2.2 := by
  obtain ⟨-, -, -, -, T⟩ := readX_trace h S seen b k o j e
  have R := trace_storedAt h _ _ _ _ b _ _ _ _ T
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

/-- Each opening of a stored table, at the second chain's configuration's digest. -/
theorem stored_walkedH (W : Three.Whole) (hs : StoredSecond W) :
    ∀ y ∈ storedRowsW W r, Walked h S₂.base.cfg y.2 := by
  intro y hy
  obtain ⟨ro, hro, hz⟩ := stored_mem (storedW_second hs hy)
  exact (readX_entered h S₂ _ file _ _ _ A.shared).1 ro hro y.2 hz

/-- A stored table's opening, at one listed position. -/
theorem stored_leafH (W : Three.Whole) (sb a : ℕ) (F : FileFits W sb a S₁ S₂ S₃)
    (hs : StoredSecond W) :
    ∀ y ∈ storedRowsW W r, ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray),
      (x, col, salt) ∈ listed y.2 →
      seenAt y.2.2.2.seen y.2.1.a x = some (leafHash h y.2.1 S₂.base.cfg x col salt) := by
  intro y hy
  obtain ⟨f, sb', b', k, e⟩ :=
    stored_readAtH W W.ds₂ S₂ _ file _ _ _ A.shared F.d₂ y (storedW_second hs hy)
  exact opening_leaf h _ f sb' _ b' k y.2 e

end

/-! ## The two records -/

/-- **What the trees' openings give, at the hash h.** -/
structure TreesOwedH (h : HId) (W : Three.Whole) (r : TailRead) (cfg : ByteArray) : Prop where
  one : ∀ z ∈ ownRowsW W r, ∀ z' ∈ ownRowsW W r, z.1 = z'.1 → ∀ (d p : ℕ) (v v' : ByteArray),
    (d ≠ 0 ∨ p = 0) → seenAt z.2.2.2.seen d p = some v → seenAt z'.2.2.2.seen d p = some v' →
    v = v'
  walked : ∀ z ∈ ownRowsW W r, Walked h cfg z.2
  size : ∀ z ∈ ownRowsW W r, ∀ u ∈ z.2.2.2.seen, u.2.2.size = 32
  root : ∀ z ∈ ownRowsW W r, ∃ start, TreeAt W r z.1 z.2.2.2.root start
  leaf : ∀ z ∈ ownRowsW W r, ∃ start, runOfTree W r z.1 = some start ∧
    ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), (x, col, salt) ∈ listed z.2 →
      seenAt z.2.2.2.seen z.2.1.a x = some (leafHash h z.2.1 start x col salt)

/-- **What the stored table's openings give, at the hash h.** -/
structure StoredOwedH (h : HId) (W : Three.Whole) (r : TailRead) (cfg st : ByteArray) : Prop where
  one : ∀ y ∈ storedRowsW W r, ∀ y' ∈ storedRowsW W r, ∀ (d p : ℕ) (v v' : ByteArray),
    (d ≠ 0 ∨ p = 0) → seenAt y.2.2.2.seen d p = some v → seenAt y'.2.2.2.seen d p = some v' →
    v = v'
  walked : ∀ y ∈ storedRowsW W r, Walked h cfg y.2
  size : ∀ y ∈ storedRowsW W r, ∀ u ∈ y.2.2.2.seen, u.2.2.size = 32
  root : ∀ y ∈ storedRowsW W r, Fmt.itemRoot st 0 = some y.2.2.2.root
  leaf : ∀ y ∈ storedRowsW W r, ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray),
    (x, col, salt) ∈ listed y.2 →
    seenAt y.2.2.2.seen y.2.1.a x = some (leafHash h y.2.1 cfg x col salt)

section
variable {h : HId} {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray}
  {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
  {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
  {S₃ : Fmt.SpecX} {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **What the trees' openings give, at the hash h.** -/
theorem treesOwedH_of_readX
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (A : ReadAt h S₁ S₂ S₃ file i r)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (cfg : ByteArray) (c₁ : g₁.cfg = cfg)
    (c₂ : p.shared.given.cfg = cfg) (c₃ : p.second.given.cfg = cfg) :
    TreesOwedH h (Three.Whole.of R₁ R₂ R₃) r cfg := by
  have B := treesOwed_of_read T hS₁ hn o₁ b₁ R₃ hd m hf cfg c₁ c₂ c₃
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (Proof.secondFirstTree r.first) =
        some S₃ := T.second_spec
  obtain ⟨o₂, b₂⟩ := shared_own p r.key T.shared_dry
  obtain ⟨F₁, F₂, F₃, h₁, h₂⟩ := srcFits_of_read T hS₁ hn o₁ o₂ b₁ b₂ R₃ hd m hf
  have h₃ : rootsIn R₃ = r.second.roots.length :=
    third_roots hS₃ r.shared.out.seen file r.shared.next r.second T.second_read
      (alike_items (named_of_read T hS₁ b₁ R₃ hd))
  have O := own_treeAtH A _ F₁ F₂ F₃
  exact
    { one := B.one
      walked := own_walkedH A _ cfg ((describeWith_cfg hS₁).trans c₁)
        ((describeWith_cfg hS₂).trans c₂) ((describeWith_cfg hS₃).trans c₃)
      size := B.size
      root := B.root
      leaf := fun z hz => own_leafH h₁ h₂ h₃ (O z hz) }

/-- **What the stored table's openings give, at the hash h.** -/
theorem storedOwedH_of_readX
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (A : ReadAt h S₁ S₂ S₃ file i r)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (sb a : ℕ) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (a₁ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₁) (a₂ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₂)
    (a₃ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₃) (hs : StoredSecond (Three.Whole.of R₁ R₂ R₃)) :
    StoredOwedH h (Three.Whole.of R₁ R₂ R₃) r p.shared.given.cfg
      (Params.Shared.statement p.table r.place.root) := by
  have B := storedOwed_of_read T hS₁ b₁ R₃ hd m hf sb a s₁ s₂ s₃ a₁ a₂ a₃ hs
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (Proof.secondFirstTree r.first) =
        some S₃ := T.second_spec
  have N := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hf hS₁ hS₂ hS₃ (alike_shapes N) (alike_stored N) s₁ s₂ s₃ a₁ a₂ a₃
  have ec := describeWith_cfg hS₂
  exact
    { one := B.one
      walked := ec ▸ stored_walkedH A _ hs
      size := B.size
      root := B.root
      leaf := ec ▸ stored_leafH A _ sb a F hs }

end

end OnBytes.Maker.Page
