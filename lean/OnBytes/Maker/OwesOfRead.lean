-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OwesOfRead.lean: what the openings of a file as the program's reader has read it give
to a walk over whole paths, gathered in two records: one for the trees, one for the stored table;
from the record of the three chains' reading and tests on the data.

Statements and proofs. The laws lie in OnBytes/Maker/SrcFitsOf.lean, ReadSizes.lean,
TableChain.lean, StoredRoot.lean, ReadLeaf.lean and RootsCount.lean. Here they are called at one
reading (`ThreeRead`, OnBytes/Maker/ThreeRead.lean).

Main names:
  `TreesOwed W r cfg`: of the members of `ownRowsW W r`: two under one number give one value to each
    vertex; each is what the reader of an opening hands out at the digest cfg; every vertex's value
    has 32 bytes; each walks to the root that the tree's sender sent; at each listed position the
    bottom level holds the format's leaf hash at the start `runOfTree W r j`.
  `StoredOwed W r cfg st`: the like of the members of `storedRowsW W r`: the root is the one in the
    item 0 of the statement st, the start of a leaf is cfg.
  `describeWith_cfg`: the configuration's digest of a description that is returned.
  `named_of_read`: the third chain's rounds as read and at made-up names go together.
  `treesOwed_of_read`, `storedOwed_of_read`: the two records.
What is asked besides the reading: the three parameter bytes have one configuration's digest cfg;
the first chain's rounds open own trees alone and its dry run's book holds own trees alone (paid for
a key's one-time chain: `key_own`); the test `Three.Whole.fits`; for the stored table also one
number of bytes of a salt in the three plans, `StoredAt` and `StoredSecond`.
Under `StoredSecond` the premises `StoredAt` at the first and the third chain are idle.
Under "there is": in `TreesOwed.leaf` the start, fixed by `runOfTree W r z.1 = some start`; in
`TreesOwed.root` the start, fixed inside `TreeAt`. `Walked` holds the field, the bytes of a salt,
the start, the file and the place of the reader's call under "there are", tied to nothing: so the
start in `walked` and the start in `leaf` are two letters that no clause makes one.
What the records do not hold: that `ownRowsW` and `storedRowsW` hold every opening as read; that
the shape as read is the table's; the salts' sizes; that two numbers have two roots; that a vertex
other than a listed leaf or the root is there.
Limits: these premises are not proved here. All is said at the format's hash (with the hash as a
letter: OnBytes/Maker/Page/OwesH.lean): nothing ties it to another verifier's hash. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
beyond the reader's record or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.SrcFitsOf
import OnBytes.Maker.ReadLeaf
import OnBytes.Maker.RootsCount

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Three (tagChain rootsIn)
open OnBytes.Params (Rounds)
open _root_.Run (seenAt)

/-- **What the trees' openings give.** -/
structure TreesOwed (W : Three.Whole) (r : TailRead) (cfg : ByteArray) : Prop where
  /-- two openings under one number give one value to each vertex -/
  one : ∀ z ∈ ownRowsW W r, ∀ z' ∈ ownRowsW W r, z.1 = z'.1 → ∀ (d p : ℕ) (v v' : ByteArray),
    (d ≠ 0 ∨ p = 0) → seenAt z.2.2.2.seen d p = some v → seenAt z'.2.2.2.seen d p = some v' →
    v = v'
  /-- each is what the reader of an opening hands out at the digest cfg -/
  walked : ∀ z ∈ ownRowsW W r, Walked Fmt.formatHash cfg z.2
  /-- every vertex's value has 32 bytes -/
  size : ∀ z ∈ ownRowsW W r, ∀ u ∈ z.2.2.2.seen, u.2.2.size = 32
  /-- each walks to the root that the tree's sender sent -/
  root : ∀ z ∈ ownRowsW W r, ∃ start, TreeAt W r z.1 z.2.2.2.root start
  /-- the leaf's hash at the bottom, at the start that the tables lay -/
  leaf : ∀ z ∈ ownRowsW W r, ∃ start, runOfTree W r z.1 = some start ∧
    ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), (x, col, salt) ∈ listed z.2 →
      seenAt z.2.2.2.seen z.2.1.a x = some (leafHash Fmt.formatHash z.2.1 start x col salt)

/-- **What the stored table's openings give.** st: the statement of the chain that opens them. -/
structure StoredOwed (W : Three.Whole) (r : TailRead) (cfg st : ByteArray) : Prop where
  one : ∀ y ∈ storedRowsW W r, ∀ y' ∈ storedRowsW W r, ∀ (d p : ℕ) (v v' : ByteArray),
    (d ≠ 0 ∨ p = 0) → seenAt y.2.2.2.seen d p = some v → seenAt y'.2.2.2.seen d p = some v' →
    v = v'
  walked : ∀ y ∈ storedRowsW W r, Walked Fmt.formatHash cfg y.2
  size : ∀ y ∈ storedRowsW W r, ∀ u ∈ y.2.2.2.seen, u.2.2.size = 32
  root : ∀ y ∈ storedRowsW W r, Fmt.itemRoot st 0 = some y.2.2.2.root
  leaf : ∀ y ∈ storedRowsW W r, ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray),
    (x, col, salt) ∈ listed y.2 →
    seenAt y.2.2.2.seen y.2.1.a x = some (leafHash Fmt.formatHash y.2.1 cfg x col salt)

/-- The configuration's digest of a description that is returned is that of the parameter bytes. -/
theorem describeWith_cfg {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.cfg = g.cfg := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

/-- The statement of a description that is returned is the argument. -/
theorem describeWith_statement {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.statement = st := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **The third chain's rounds as read and the data's third list go together**, name by name. -/
theorem named_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    LAlike (RoundAlike (NamesGo r.first r.shared r.first.roots.length r.shared.roots.length))
      R₃' R₃ := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have c₁ : r.first.roots.length = rootsIn R₁ :=
    readChain_roots hS₁ [] file i r.first T.first_read
  have c₂ : r.shared.roots.length = rootsIn R₂ :=
    readChain_roots hS₂ r.first.out.seen file r.place.next r.shared T.shared_read
  have hx : (secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 r.shared.roots.length))).rounds
      (secondStart p dry (tagChain 1 r.first.roots.length)) = some R₃ := by
    unfold Three.dry3 at hd
    rw [T.shared_dry] at hd
    rw [c₁, c₂]
    have hd' : (((secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (rootsIn R₂)))).rounds
      (secondStart p dry (tagChain 1 (rootsIn R₁)))).bind fun R₃ =>
        some (R₁, R₂, R₃)) = some (R₁, R₂, R₃) := hd
    cases hX : (secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (rootsIn R₂)))).rounds
        (secondStart p dry (tagChain 1 (rootsIn R₁))) with
    | none =>
      rw [hX] at hd'
      cases hd'
    | some Y =>
      rw [hX] at hd'
      have e : (R₁, R₂, Y) = (R₁, R₂, R₃) := Option.some.inj hd'
      rw [(Prod.mk.inj (Prod.mk.inj e).2).2]
  have A := second_named p dry dry2 r.first r.shared r.shared.roots.length b₁
    (shared_own p r.key T.shared_dry).2
  rw [T.second_rounds, hx] at A
  cases A with
  | some q => exact q

/-- **What the trees' openings give, from the record of the three chains' reading.** -/
theorem treesOwed_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (cfg : ByteArray) (c₁ : g₁.cfg = cfg)
    (c₂ : p.shared.given.cfg = cfg) (c₃ : p.second.given.cfg = cfg) :
    TreesOwed (Three.Whole.of R₁ R₂ R₃) r cfg := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (secondFirstTree r.first) = some S₃ :=
    T.second_spec
  obtain ⟨o₂, b₂⟩ := shared_own p r.key T.shared_dry
  obtain ⟨F₁, F₂, F₃, h₁, h₂⟩ := srcFits_of_read T hS₁ hn o₁ o₂ b₁ b₂ R₃ hd m hf
  have h₃ : rootsIn R₃ = r.second.roots.length :=
    third_roots hS₃ r.shared.out.seen file r.shared.next r.second T.second_read
      (alike_items (named_of_read T hS₁ b₁ R₃ hd))
  have O := own_treeAt _ S₁ S₂ S₃ r file _ _ _ _ _ _ _ _ _ T.first_read T.shared_read T.second_read
    F₁ F₂ F₃
  exact
    { one := one_table _ S₁ S₂ S₃ r file _ _ _ _ _ _ T.first_read T.shared_read T.second_read F₁ F₂
        F₃ h₁ h₂
      walked := own_walked _ cfg S₁ S₂ S₃ r file _ _ _ _ _ _ _ _ _ T.first_read T.shared_read
        T.second_read ((describeWith_cfg hS₁).trans c₁) ((describeWith_cfg hS₂).trans c₂)
        ((describeWith_cfg hS₃).trans c₃)
      size := own_size _ S₁ S₂ S₃ r file _ _ _ _ _ _ _ _ _ T.first_read T.shared_read T.second_read
      root := fun z hz => (O z hz).imp fun _ h => h.1
      leaf := fun z hz => own_leaf h₁ h₂ h₃ (O z hz) }

/-- **What the stored table's openings give, from the record of the three chains' reading.** -/
theorem storedOwed_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (sb a : ℕ) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (a₁ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₁) (a₂ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₂)
    (a₃ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₃) (hs : StoredSecond (Three.Whole.of R₁ R₂ R₃)) :
    StoredOwed (Three.Whole.of R₁ R₂ R₃) r p.shared.given.cfg
      (Params.Shared.statement p.table r.place.root) := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (secondFirstTree r.first) = some S₃ :=
    T.second_spec
  have A := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hf hS₁ hS₂ hS₃ (alike_shapes A) (alike_stored A) s₁ s₂ s₃ a₁ a₂ a₃
  have hk : Kept r.first.out.seen := readChain_kept S₁ [] file i _ _ T.first_read kept_nil
  have ec := describeWith_cfg hS₂
  have es := describeWith_statement hS₂
  exact
    { one := one_tableE _ sb a S₁ S₂ S₃ F hs r file _ hk _ _ T.shared_read
      walked := ec ▸ stored_walked _ hs S₂ r file _ _ _ T.shared_read
      size := stored_size _ hs S₂ r file _ _ _ T.shared_read
      root := es ▸ stored_root _ sb a S₁ S₂ S₃ F hs r file _ _ _ T.shared_read
      leaf := ec ▸ stored_leaf _ sb a S₁ S₂ S₃ F hs r file _ _ _ T.shared_read }

end

end OnBytes.Maker
