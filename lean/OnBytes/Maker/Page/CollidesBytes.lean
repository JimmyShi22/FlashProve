-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/CollidesBytes.lean: "this key file shows a collision" and "this proof file shows
one", with the hash's own arguments written out: two entries out of the file's own lists as read
give two different strings of bytes with one answer of the hash, at one number, one label, one index
and one start; and that at a file which the verifier program's reader has read, if the tests on the
plain data pass, either the six parts of the typing return or the file shows such a collision.

Definitions, statements and proofs. OnBytes/Maker/Page/Collides.lean has the two propositions for
pairs of a column and a salt. OnBytes/Maker/Page/LeafInputs.lean leads from such pairs to strings of
bytes at the same members of the file's lists, if the compared entries have one number of words and
one number of bytes. Here that condition is paid by the tables' own tests on a reading and by two
tests on the plain data.

Main names:
  `oneSaltB W`: a test on the plain data: all stored tables that the rounds open have one number of
    bytes of a salt. `oneSalt_of`: what it gives at the openings as read.
  `sizesOne_of_read`, `key_sizesOne`, `proof_sizesOne`: `SizesOne` at a reading.
  `KeyCollidesB h k table file j`, `ProofCollidesB h c table copy request words block file`: the two
    propositions. request: the value of the item "request"; words: the request file's bytes.
  `KeyCollides.bytes`, `ProofCollides.bytes`: from the propositions for pairs.
  `key_returns_or_collidesB`, `proof_returns_or_collidesB`: at the format's hash.
  `key_returns_or_collidesBO`, `proof_returns_or_collidesBO`: at the hash over the realised oracle.
Under "there is" in the two propositions: r, fixed by the equation of the program's reader at the
file; R, fixed by the equation of the dry runs at r's key; then the letters of `CollidesInB`, each a
member of the file's own lists as read.
Premises: those of Collides.lean's and CollidesOracle.lean's laws, and the test `oneSaltB`.
Limits: none of the premises is shown here. Of the five tests two are parts of `okAt`: three are to
be evaluated (`okAt`, `oneShapeB`, `oneSaltB`). Whatever h is, the reading in the two propositions
is the program's, which reads at `Fmt.formatHash`: at another h they speak of two hashes. What `Fmt.formatHash`
computes is the matter of Fmt/Rules23.lean. Nothing on how hard such a file is to make. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.CollidesOracle
import OnBytes.Maker.Page.LeafInputs

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- A test on the plain data: all stored tables that the rounds open have one number of bytes of a
salt. -/
def oneSaltB (W : Three.Whole) : Bool :=
  (storedOf W).all fun t => (storedOf W).all fun t' => t.salt == t'.salt

theorem oneSalt_of {W : Three.Whole} {r : TailRead} (hB : oneSaltB W = true) :
    ∀ x ∈ storedRowsW W r, ∀ y ∈ storedRowsW W r, x.1.salt = y.1.salt := by
  intro x hx y hy
  unfold oneSaltB at hB
  exact eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 hB _ (storedOf_mem hx)) _
    (storedOf_mem hy))

/-- The compared entries have one number of words and one number of bytes, at the record of a
reading. -/
theorem sizesOne_of_read {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start}
    {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
    {S₃ : Fmt.SpecX} {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand} (a sb : ℕ)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true)
    (hZ : oneSaltB (Three.Whole.of R₁ R₂ R₃) = true) : SizesOne (Three.Whole.of R₁ R₂ R₃) r := by
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit hS₁ T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) s₁ s₂ s₃ a₁
      a₂ a₃
  obtain ⟨-, t1, t2, -⟩ := tables_fit _ sb a S₁ S₂ S₃ F r file _ _ _ _ _ _ _ _ _ T.first_read
    T.shared_read T.second_read
  exact sizesOne_of t1 t2 (shapeOneE_of hB t2) (oneSalt_of hZ)

/-! ## The two propositions -/

/-- **This key file shows a collision of the hash h**, with the hash's arguments written out. -/
def KeyCollidesB (h : HId) (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) : Prop :=
  ∃ (r : TailRead) (R : Rounds × Rounds × Rounds),
    (Key.readKey k table file j).fromStart = .ok r ∧ dryKey k r.key = some R ∧
      CollidesInB h (Three.Whole.of R.1 R.2.1 R.2.2) r k.shared.given.cfg

/-- **This proof file shows a collision of the hash h**, the like. -/
def ProofCollidesB (h : HId) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Prop :=
  ∃ (r : TailRead) (R : Rounds × Rounds × Rounds),
    (readProof c table copy request words block file).fromStart = .ok r ∧
      dryProof c r.key block = some R ∧
      CollidesInB h (Three.Whole.of R.1 R.2.1 R.2.2) r c.shared.given.cfg

/-- From pairs to strings of bytes, at the reader's value r and the dry runs' R. -/
theorem KeyCollides.bytes {h : HId} {k : Params.KeyChains} {table : Params.TableName}
    {file : ByteArray} {j : ℕ} (c : KeyCollides h k table file j) (r : TailRead)
    (h₀ : (Key.readKey k table file j).fromStart = .ok r) (R : Rounds × Rounds × Rounds)
    (hR : dryKey k r.key = some R) (z : SizesOne (Three.Whole.of R.1 R.2.1 R.2.2) r) :
    KeyCollidesB h k table file j := by
  obtain ⟨r', R', h', hR', x⟩ := c
  obtain rfl : r' = r := by
    have := h'.symm.trans h₀
    injection this
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  exact ⟨r', R', h₀, hR, x.bytes z⟩

theorem ProofCollides.bytes {h : HId} {c : Params.ProofChains} {table : Params.TableName}
    {copy : ℕ} {request words : ByteArray} {block : Blk FirstEnd} {file : ByteArray}
    (x : ProofCollides h c table copy request words block file) (r : TailRead)
    (h₀ : (readProof c table copy request words block file).fromStart = .ok r)
    (R : Rounds × Rounds × Rounds) (hR : dryProof c r.key block = some R)
    (z : SizesOne (Three.Whole.of R.1 R.2.1 R.2.2) r) :
    ProofCollidesB h c table copy request words block file := by
  obtain ⟨r', R', h', hR', y⟩ := x
  obtain rfl : r' = r := by
    have := h'.symm.trans h₀
    injection this
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  exact ⟨r', R', h₀, hR, y.bytes z⟩

/-! ## A key file -/

section Key
variable (C : CK) (a : ℕ) (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
  (j : ℕ) (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r)
  (R : Rounds × Rounds × Rounds) (hR : dryKey k r.key = some R)
  (hfit : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true)
  (hst : storedFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hZ : oneSaltB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfgS : ByteArray) (sb : ℕ)
  (hs : OneSetting k.oneTime.given k.shared.given k.second.given cfgS sb)
include h hR hfit hst hB hZ hs

theorem key_sizesOne : SizesOne (Three.Whole.of R.1 R.2.1 R.2.2) r := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  unfold dryKey at hR
  rw [T.first_dry] at hR
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨-, b₁⟩ := key_own k.oneTime T.first_dry
  exact sizesOne_of_read a sb T hS₁' b₁ R₃ hd hfit hst hs.s₁ hs.s₂ hs.s₃ hB hZ

/-- **A key file, at the format's hash.** cfg: the typing's letter. -/
theorem key_returns_or_collidesB (hok : okAt a (some R) = true) (cfg : ByteArray) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      KeyCollidesB Fmt.formatHash k table file j :=
  (key_returns_or_collides C a k table file j r h R hR hok hfit hst hB cfgS sb hs cfg).imp id
    fun c => c.bytes r h R hR (key_sizesOne a k table file j r h R hR hfit hst hB hZ cfgS sb hs)

/-- **A key file, at the hash over the realised oracle.** -/
theorem key_returns_or_collidesBO (hok : okAt a (some R) = true) (cfg : ByteArray)
    (hsm : SmallAt (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime)
      k.oneTime.given Params.labelOneTime (Params.OneTime.statement table) file j r) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      KeyCollidesB (Fmt.HO Fmt.oracle) k table file j :=
  (key_returns_or_collidesO C a k table file j r h hsm R hR hok hfit hst hB cfgS sb hs cfg).imp id
    fun c => c.bytes r h R hR (key_sizesOne a k table file j r h R hR hfit hst hB hZ cfgS sb hs)

end Key

/-! ## A proof file -/

section Proof
variable (C : CK) (a : ℕ) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
  (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
  (h : (readProof c table copy request words block file).fromStart = .ok r)
  (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block)
  (R : Rounds × Rounds × Rounds) (hR : dryProof c r.key block = some R)
  (hfit : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true)
  (hst : storedFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hZ : oneSaltB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfgS : ByteArray) (sb : ℕ)
  (hs : OneSetting c.first.given c.shared.given c.second.given cfgS sb)
include h hb hR hfit hst hB hZ hs

theorem proof_sizesOne : SizesOne (Three.Whole.of R.1 R.2.1 R.2.2) r := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  unfold dryProof at hR
  rw [T.first_dry] at hR
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨-, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  exact sizesOne_of_read a sb T hS₁' b₁ R₃ hd hfit hst hs.s₁ hs.s₂ hs.s₃ hB hZ

/-- **A proof file, at the format's hash.** -/
theorem proof_returns_or_collidesB (hok : okAt a (some R) = true) (cfg : ByteArray) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      ProofCollidesB Fmt.formatHash c table copy request words block file :=
  (proof_returns_or_collides C a c table copy request words block file r h hb R hR hok hfit hst hB
      cfgS sb
    hs cfg).imp id fun x => x.bytes r h R hR
      (proof_sizesOne a c table copy request words block file r h hb R hR hfit hst hB hZ cfgS sb hs)

/-- **A proof file, at the hash over the realised oracle.** -/
theorem proof_returns_or_collidesBO (hok : okAt a (some R) = true) (cfg : ByteArray)
    (hsm : ∀ i, readProofHead c.first.given.plan.field file = .ok (copy, i) →
      SmallAt (tailPublic c table) block (firstStart c.first) c.first.given Params.labelFirst
        (Params.First.statement table copy request words) file i r) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      ProofCollidesB (Fmt.HO Fmt.oracle) c table copy request words block file :=
  (proof_returns_or_collidesO C a c table copy request words block file r h hsm hb R hR hok hfit hst
      hB
    cfgS sb hs cfg).imp id fun x => x.bytes r h R hR
      (proof_sizesOne a c table copy request words block file r h hb R hR hfit hst hB hZ cfgS sb hs)

end Proof

end OnBytes.Maker.Page
