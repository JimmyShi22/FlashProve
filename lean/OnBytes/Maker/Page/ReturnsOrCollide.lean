-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/ReturnsOrCollide.lean: at a file that the verifier program's reader has read, if
the tests on the plain data pass, either the six parts of the typing return, or the file shows two
different pairs of a column and a salt with one leaf hash.

A statement and its proof. `returns_of_read` (OnBytes/Maker/TypeFileOfRead.lean) gives the typing's
six parts under the hypothesis `SameTwice`, which no reading gives: the reader ties two listings of
one position by digests alone. OnBytes/Maker/Page/TwiceOrCollide.lean says what a file in which
`SameTwice` fails shows. Here the two are laid together at the format's hash, at which the program
reads.

Main names:
  `readAt_H`: the record of the reading gives the three equations of the strict reader at `Fmt.formatHash`.
  `returns_or_collides`: `typeReturns .. = true ∨ CollidesIn Fmt.formatHash ..`.
  `collides_of_not_returns`: so a file as read at which the test `typeReturns` says no shows a
    collision of the leaf hash.
The letters under "there is" are those of `CollidesIn`: two openings and two entries out of the
file's own lists; the start, fixed by `runOfTree`.
Premises: the record of the reading with the first chain's description; that the first chain names
its own trees alone (`OwnAlone`, `OwnBook`: laws pay them at a key file and at the program's own
blocks); that the data are made of the rounds that `Three.dry3` gives at the reading's key; the
test `okAt` and two of its parts by themselves, `Three.Whole.fits` and `storedFit`; one number of
bytes of a salt and one configuration's digest in the three chains; that two openings of stored
tables have one shape as read (`ShapeOneE`).
Limits: none of these premises is shown here. "Collision" is meant as in TwiceOrCollide.lean: of
pairs of a column and a salt. Nothing on how hard one is to find. Nothing on what the typed string
holds. Nothing on opening-form binding, no two openings of a commitment, correctness of extraction,
what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.TwiceOrCollide
import OnBytes.Maker.TypeFileOfRead
import OnBytes.Maker.StoredOfFit

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)
open OnBytes.Params (Rounds)

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- The record of the reading gives the three equations of the strict reader at the format's
hash. -/
theorem readAt_H (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃) :
    ReadAt Fmt.formatHash S₁ S₂ S₃ file i r :=
  ⟨(readChain_eq _ _ _ _).symm.trans T.first_read, (readChain_eq _ _ _ _).symm.trans T.shared_read,
    (readChain_eq _ _ _ _).symm.trans T.second_read⟩

/-- **Either the typing's six parts return, or the file shows a collision of the leaf hash.**
cfg: the typing's letter; cfgS: the three chains' configuration's digest. -/
theorem returns_or_collides (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (c₁ : g₁.cfg = cfgS) (c₂ : p.shared.given.cfg = cfgS) (c₃ : p.second.given.cfg = cfgS)
    (sE : ShapeOneE (Three.Whole.of R₁ R₂ R₃) r) :
    typeReturns C a (Three.Whole.of R₁ R₂ R₃) sb cfg r = true ∨
      CollidesIn Fmt.formatHash (Three.Whole.of R₁ R₂ R₃) r cfgS := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (Proof.secondFirstTree r.first) =
        some S₃ := T.second_spec
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit hS₁ hS₂ hS₃ (alike_shapes N) (alike_stored N) s₁ s₂ s₃ a₁ a₂ a₃
  have A := readAt_H T
  have TO := treesOwedH_of_readX T A hS₁ hn o₁ b₁ R₃ hd 2 hfit cfgS c₁ c₂ c₃
  have SO := storedOwedH_of_readX T A hS₁ b₁ R₃ hd 2 hfit sb a s₁ s₂ s₃ a₁ a₂ a₃
    (storedSecond_of_fit hst)
  rw [c₂] at SO
  have s1 : ShapeOne (Three.Whole.of R₁ R₂ R₃) r :=
    shapeOne_of_rowOK (tables_fit _ sb a S₁ S₂ S₃ F r file _ _ _ _ _ _ _ _ _ T.first_read
      T.shared_read T.second_read).2.1
  rcases sameTwice_or_collidesIn TO SO s1 sE with hT | hc
  · exact Or.inl (returns_of_read C a sb cfg T hS₁ hn R₃ (alike_stored N) (alike_items N)
      (alike_shapes N) hok s₁ s₂ s₃ hT)
  · exact Or.inr hc

/-- **A file as read at which the typing's test says no shows a collision of the leaf hash.** -/
theorem collides_of_not_returns (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (c₁ : g₁.cfg = cfgS) (c₂ : p.shared.given.cfg = cfgS) (c₃ : p.second.given.cfg = cfgS)
    (sE : ShapeOneE (Three.Whole.of R₁ R₂ R₃) r)
    (hno : typeReturns C a (Three.Whole.of R₁ R₂ R₃) sb cfg r = false) :
    CollidesIn Fmt.formatHash (Three.Whole.of R₁ R₂ R₃) r cfgS :=
  (returns_or_collides C a sb cfg cfgS T hS₁ hn o₁ b₁ R₃ hd hok hfit hst s₁ s₂ s₃ c₁ c₂ c₃
    sE).resolve_left fun h => by rw [hno] at h; cases h

end

end OnBytes.Maker.Page
