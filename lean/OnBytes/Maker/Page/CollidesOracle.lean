-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/CollidesOracle.lean: "either the six parts of the typing return, or the file
shows a collision of the leaf hash", at any hash at which the strict reader reads the file's three
chains with the outcome that the verifier program's reader had; and so at the hash that the realised
oracle on byte strings induces.

Statements and proofs. OnBytes/Maker/Page/ReturnsOrCollide.lean and Collides.lean have the laws at
the format's hash `Fmt.formatHash`, at which the program reads. The laws beneath them have the hash as a
letter. Here the tops are stated with that letter, and then at `Fmt.HO Fmt.oracle`, where
OnBytes/Maker/Page/AtOracle.lean gives the three readings within the bounds `SmallThree`.

Main names:
  `returns_or_collidesAt`: at any h with `ReadAt h`.
  `returns_or_collidesO`: at the realised oracle, at the record of a reading.
  `SmallAt p block1 start1 g₁ l₁ x₁ file i r`: the bounds hold at the record of this file's reading
    whose first description is made of g₁, l₁, x₁, from the place i.
  `key_returns_or_collidesO`, `proof_returns_or_collidesO`: at the two readers' own equations.
The letters under "there is" are those of `KeyCollides` and `ProofCollides`.
Premises: those of the laws at `Fmt.formatHash`, and the bounds.
Limits: none of the premises is shown here. `SmallAt` is stated over all records with that first
description and place, since the three descriptions stand under "there is" in the law that hands the
record out; there is one such record's reading (`threeRead_unique`,
OnBytes/Maker/Page/ReadCollides.lean), so it is the test `SmallThree` at the program's own three
descriptions; no law here says so. Nothing on how hard a collision is to find. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.Collides
import OnBytes.Maker.Page.AtOracle

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **At any hash at which the strict reader reads the three chains with the program's outcome.** -/
theorem returns_or_collidesAt (h : HId) (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (A : ReadAt h S₁ S₂ S₃ file i r)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (c₁ : g₁.cfg = cfgS) (c₂ : p.shared.given.cfg = cfgS) (c₃ : p.second.given.cfg = cfgS)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true) :
    typeReturns C a (Three.Whole.of R₁ R₂ R₃) sb cfg r = true ∨
      CollidesIn h (Three.Whole.of R₁ R₂ R₃) r cfgS := by
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst
  have N := named_of_read T hS₁ b₁ R₃ hd
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit hS₁ T.shared_spec T.second_spec (alike_shapes N) (alike_stored N) s₁ s₂ s₃ a₁
      a₂ a₃
  obtain ⟨-, t1, t2, -⟩ := tables_fit _ sb a S₁ S₂ S₃ F r file _ _ _ _ _ _ _ _ _ T.first_read
    T.shared_read T.second_read
  have TO := treesOwedH_of_readX T A hS₁ hn o₁ b₁ R₃ hd 2 hfit cfgS c₁ c₂ c₃
  have SO := storedOwedH_of_readX T A hS₁ b₁ R₃ hd 2 hfit sb a s₁ s₂ s₃ a₁ a₂ a₃
    (storedSecond_of_fit hst)
  rw [c₂] at SO
  rcases sameTwice_or_collidesIn TO SO (shapeOne_of_rowOK t1) (shapeOneE_of hB t2) with hT | hc
  · exact Or.inl (returns_of_read C a sb cfg T hS₁ hn R₃ (alike_stored N) (alike_items N)
      (alike_shapes N) hok s₁ s₂ s₃ hT)
  · exact Or.inr hc

/-- The three readings at the realised oracle, as one record. -/
theorem readAt_O (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hsm : SmallThree S₁ S₂ S₃ file) : ReadAt (Fmt.HO Fmt.oracle) S₁ S₂ S₃ file i r :=
  ⟨(three_atOracle T hsm).1, (three_atOracle T hsm).2.1, (three_atOracle T hsm).2.2⟩

/-- **At the realised oracle.** -/
theorem returns_or_collidesO (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hsm : SmallThree S₁ S₂ S₃ file)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (c₁ : g₁.cfg = cfgS) (c₂ : p.shared.given.cfg = cfgS) (c₃ : p.second.given.cfg = cfgS)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true) :
    typeReturns C a (Three.Whole.of R₁ R₂ R₃) sb cfg r = true ∨
      CollidesIn (Fmt.HO Fmt.oracle) (Three.Whole.of R₁ R₂ R₃) r cfgS :=
  returns_or_collidesAt _ C a sb cfg cfgS T (readAt_O T hsm) hS₁ hn o₁ b₁ R₃ hd hok hfit hst s₁ s₂
    s₃ c₁ c₂ c₃ hB

end

/-- The bounds hold at the record of this file's reading whose first description is made of g₁, l₁,
x₁, from the place i. -/
def SmallAt (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start) (g₁ : Params.Given) (l₁ : ℕ)
    (x₁ : ByteArray) (file : ByteArray) (i : ℕ) (r : TailRead) : Prop :=
  ∀ (R₁ : Rounds) (dry : FirstEnd) (S₁ : Fmt.SpecX) (seal1 seal2 : ByteArray)
    (R₂ : Rounds) (dry2 : SharedEnd) (S₂ : Fmt.SpecX) (R₃' : Rounds) (S₃ : Fmt.SpecX),
    Params.describeWith g₁ l₁ x₁ .inFile R₁ 0 = some S₁ →
    ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ →
    SmallThree S₁ S₂ S₃ file

section Key
variable (C : CK) (a : ℕ) (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
  (j : ℕ) (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r)
  (hsm : SmallAt (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime)
    k.oneTime.given Params.labelOneTime (Params.OneTime.statement table) file j r)
  (R : Rounds × Rounds × Rounds) (hR : dryKey k r.key = some R) (hok : okAt a (some R) = true)
  (hfit : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true)
  (hst : storedFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfgS : ByteArray) (sb : ℕ)
  (hs : OneSetting k.oneTime.given k.shared.given k.second.given cfgS sb) (cfg : ByteArray)
include h hsm hR hok hfit hst hB hs

/-- **A key file, at the realised oracle.** -/
theorem key_returns_or_collidesO :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      KeyCollides (Fmt.HO Fmt.oracle) k table file j := by
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
  rcases returns_or_collidesO C a sb cfg cfgS T (hsm _ _ _ _ _ _ _ _ _ _ hS₁' T) hS₁'
    (fun e => by cases e) o₁ b₁ R₃ hd hok hfit hst hs.s₁ hs.s₂ hs.s₃ hs.c₁ hs.c₂ hs.c₃ hB with
    hr | hc
  · exact Or.inl hr
  · exact Or.inr ⟨r, _, h, hR, by rw [hs.c₂]; exact hc⟩

end Key

section Proof
variable (C : CK) (a : ℕ) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
  (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
  (h : (readProof c table copy request words block file).fromStart = .ok r)
  (hsm : ∀ i, readProofHead c.first.given.plan.field file = .ok (copy, i) →
    SmallAt (tailPublic c table) block (firstStart c.first) c.first.given Params.labelFirst
      (Params.First.statement table copy request words) file i r)
  (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block)
  (R : Rounds × Rounds × Rounds) (hR : dryProof c r.key block = some R)
  (hok : okAt a (some R) = true) (hfit : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true)
  (hst : storedFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfgS : ByteArray) (sb : ℕ)
  (hs : OneSetting c.first.given c.shared.given c.second.given cfgS sb) (cfg : ByteArray)
include h hsm hb hR hok hfit hst hB hs

/-- **A proof file, at the realised oracle.** -/
theorem proof_returns_or_collidesO :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg r = true ∨
      ProofCollides (Fmt.HO Fmt.oracle) c table copy request words block file := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hi, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  have hR' := hR
  unfold dryProof at hR'
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  rcases returns_or_collidesO C a sb cfg cfgS T (hsm i hi _ _ _ _ _ _ _ _ _ _ hS₁' T) hS₁'
    (fun e => by cases e) o₁ b₁ R₃ hd hok hfit hst hs.s₁ hs.s₂ hs.s₃ hs.c₁ hs.c₂ hs.c₃ hB with
    hr | hc
  · exact Or.inl hr
  · exact Or.inr ⟨r, _, h, hR, by rw [hs.c₂]; exact hc⟩

end Proof

end OnBytes.Maker.Page
