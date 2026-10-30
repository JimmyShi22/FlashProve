-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Collides.lean: "this key file shows a collision of the leaf hash" and "this proof
file shows one", as propositions on the file's bytes, the public data and a hash; and that at a file
which the verifier program's reader has read, if the tests on the plain data pass, either the six
parts of the typing return or the file shows such a collision.

Definitions, statements and proofs. OnBytes/Maker/Page/TwiceOrCollide.lean has the proposition at a
reading r and plain data W (`CollidesIn`). Here r is the value that the program's reader returns at
the file, and W are the data of the rounds that the dry runs state at r's key.
OnBytes/Maker/Page/ReturnsOrCollide.lean has the law at the record of a reading; here it is called
at the two readers' own equations.

Main names:
  `oneShapeB W`: a test on the plain data: all stored tables that the rounds open have one shape.
    `shapeOneE_of`: with the tables' own test `storedOK` it gives `ShapeOneE`.
  `KeyCollides h k table file j`, `ProofCollides h c table copy request words block file`: the two
    propositions. h: the hash; request: the value of the item "request"; words: the request file's
    bytes: in this order: no type tells the two apart.
  `key_returns_or_collides`, `proof_returns_or_collides`: at the format's hash.
Under "there is" in the two propositions: r, fixed by the equation of the program's reader at the
file; R, fixed by the equation of the dry runs at r's key; then the letters of `CollidesIn`, each a
member of the file's own lists as read.
Premises of the two laws: the reader's equation; the dry runs' equation; the tests `okAt`,
`Three.Whole.fits`, `storedFit` and `oneShapeB` at these rounds; one number of bytes of a salt and
one configuration's digest in the three chains (`OneSetting`); for a proof file that the first
chain's block names its own trees alone (OnBytes/Maker/ProofOwn.lean pays it at the program's own
blocks).
Whatever h is, the reading in the two propositions is the program's, which reads at `Fmt.formatHash`: at
another h they speak of two hashes.
Limits: none of these premises is shown here; the four tests are to be evaluated. The data are those
of the rounds at the file's own key, not those of a fixed instance. "Collision" is of
pairs of a column and a salt, as in TwiceOrCollide.lean. Nothing on how hard one is to find. Nothing
on opening-form binding, no two openings of a commitment, correctness of extraction, what a root
fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.ReturnsOrCollide
import OnBytes.Maker.OwesAt
import OnBytes.Maker.Files

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-! ## One shape of the stored tables -/

/-- All stored tables that the data's rounds open. -/
def storedOf (W : Three.Whole) : List Fmt.Stored :=
  (W.ds₁ ++ (W.ds₂ ++ W.ds₃)).flatMap (·.stored)

/-- A test on the plain data: all stored tables that the rounds open have one shape. -/
def oneShapeB (W : Three.Whole) : Bool :=
  (storedOf W).all fun t => (storedOf W).all fun t' => t.sh == t'.sh

theorem stored_of_rows {ds : List Three.RDL} {o : Fmt.ChainOut} {y : Fmt.Stored × Opened}
    (hy : y ∈ storedRows ds o) : ∃ d ∈ ds, y.1 ∈ d.stored := by
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hy
  exact ⟨d, (List.of_mem_zip hp).1, (List.of_mem_zip hin).1⟩

theorem storedOf_mem {W : Three.Whole} {r : TailRead} {y : Fmt.Stored × Opened}
    (hy : y ∈ storedRowsW W r) : y.1 ∈ storedOf W := by
  unfold storedOf
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨d, hd, h⟩ := stored_of_rows hy
    exact List.mem_flatMap.2 ⟨d, List.mem_append_left _ hd, h⟩
  · rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨d, hd, h⟩ := stored_of_rows hy
      exact List.mem_flatMap.2 ⟨d, List.mem_append_right _ (List.mem_append_left _ hd), h⟩
    · obtain ⟨d, hd, h⟩ := stored_of_rows hy
      exact List.mem_flatMap.2 ⟨d, List.mem_append_right _ (List.mem_append_right _ hd), h⟩

/-- The test, with the tables' own test on each opening, gives one shape as read. -/
theorem shapeOneE_of {W : Three.Whole} {r : TailRead} {a : ℕ} (hB : oneShapeB W = true)
    (hok : ∀ y ∈ storedRowsW W r, storedOK a y = true) : ShapeOneE W r := by
  have key : ∀ y ∈ storedRowsW W r, y.2.1 = y.1.sh := by
    intro y hy
    have := hok y hy
    unfold storedOK at this
    simp only [Bool.and_eq_true] at this
    exact eq_of_beq this.1.1.1
  intro x hx y hy
  rw [key x hx, key y hy]
  unfold oneShapeB at hB
  exact eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 hB _ (storedOf_mem hx)) _
    (storedOf_mem hy))

/-! ## The two propositions -/

/-- **This key file shows a collision of the leaf hash h.** j: the place behind the table's record.
-/
def KeyCollides (h : HId) (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) : Prop :=
  ∃ (r : TailRead) (R : Rounds × Rounds × Rounds),
    (Key.readKey k table file j).fromStart = .ok r ∧ dryKey k r.key = some R ∧
      CollidesIn h (Three.Whole.of R.1 R.2.1 R.2.2) r k.shared.given.cfg

/-- **This proof file shows a collision of the leaf hash h.** block: the first chain's block. -/
def ProofCollides (h : HId) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Prop :=
  ∃ (r : TailRead) (R : Rounds × Rounds × Rounds),
    (readProof c table copy request words block file).fromStart = .ok r ∧
      dryProof c r.key block = some R ∧
      CollidesIn h (Three.Whole.of R.1 R.2.1 R.2.2) r c.shared.given.cfg

/-! ## The two laws -/

/-- **A key file: either the typing's six parts return at the reader's value, or the file shows a
collision of the leaf hash.** cfg: the typing's letter. -/
theorem key_returns_or_collides (C : CK) (a : ℕ) (k : Params.KeyChains)
    (table : Params.TableName) (file : ByteArray) (j : ℕ) (r : TailRead)
    (h : (Key.readKey k table file j).fromStart = .ok r) (R : Rounds × Rounds × Rounds)
    (hR : dryKey k r.key = some R) (hok : okAt a (some R) = true)
    (hfit : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true)
    (hst : storedFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfgS : ByteArray) (sb : ℕ)
    (hs : OneSetting k.oneTime.given k.shared.given k.second.given cfgS sb) (cfg : ByteArray) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      KeyCollides Fmt.formatHash k table file j := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  have hR' := hR
  unfold dryKey at hR'
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own k.oneTime T.first_dry
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS₁' b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit hS₁' T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) hs.s₁ hs.s₂
      hs.s₃ a₁ a₂ a₃
  have sE : ShapeOneE (Three.Whole.of R₁ R₂ R₃) r :=
    shapeOneE_of hB (tables_fit _ sb a S₁ S₂ S₃ F r file _ _ _ _ _ _ _ _ _ T.first_read
      T.shared_read T.second_read).2.2.1
  rcases returns_or_collides C a sb cfg cfgS T hS₁' (fun e => by cases e) o₁ b₁ R₃ hd hok hfit hst
    hs.s₁ hs.s₂ hs.s₃ hs.c₁ hs.c₂ hs.c₃ sE with hr | hc
  · exact Or.inl hr
  · exact Or.inr ⟨r, _, h, hR, by rw [hs.c₂]; exact hc⟩

/-- **A proof file**, the like. hb: the first chain's block names its own trees alone. -/
theorem proof_returns_or_collides (C : CK) (a : ℕ) (c : Params.ProofChains)
    (table : Params.TableName) (copy : ℕ) (request words : ByteArray) (block : Blk FirstEnd)
    (file : ByteArray) (r : TailRead)
    (h : (readProof c table copy request words block file).fromStart = .ok r)
    (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block)
    (R : Rounds × Rounds × Rounds) (hR : dryProof c r.key block = some R)
    (hok : okAt a (some R) = true) (hfit : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true)
    (hst : storedFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfgS : ByteArray) (sb : ℕ)
    (hs : OneSetting c.first.given c.shared.given c.second.given cfgS sb) (cfg : ByteArray) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      ProofCollides Fmt.formatHash c table copy request words block file := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  have hR' := hR
  unfold dryProof at hR'
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS₁' b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit hS₁' T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) hs.s₁ hs.s₂
      hs.s₃ a₁ a₂ a₃
  have sE : ShapeOneE (Three.Whole.of R₁ R₂ R₃) r :=
    shapeOneE_of hB (tables_fit _ sb a S₁ S₂ S₃ F r file _ _ _ _ _ _ _ _ _ T.first_read
      T.shared_read T.second_read).2.2.1
  rcases returns_or_collides C a sb cfg cfgS T hS₁' (fun e => by cases e) o₁ b₁ R₃ hd hok hfit hst
    hs.s₁ hs.s₂ hs.s₃ hs.c₁ hs.c₂ hs.c₃ sE with hr | hc
  · exact Or.inl hr
  · exact Or.inr ⟨r, _, h, hR, by rw [hs.c₂]; exact hc⟩

end OnBytes.Maker.Page
