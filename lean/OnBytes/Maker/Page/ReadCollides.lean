-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/ReadCollides.lean: at one first description and one place the record of the
reading of a file's three chains (`ThreeRead`, OnBytes/Maker/ThreeRead.lean) fixes all its other
letters; "this file shows a collision of the leaf hash" as a proposition at that record; and the way
from `CollidesIn` at a record's reading to `KeyCollides` and `ProofCollides`
(OnBytes/Maker/Page/Collides.lean), whose reading is fixed by the equation of the verifier program's
reader.

Definitions, statements and proofs. Who holds the record alone, and not the reader's equation, can
state the collision at the record. No field of the record gives the first description or the place
of the first byte: these two are taken as one on both sides. Each further letter is given by a field
from the letters before.

Main names:
  `threeRead_same`: two records at one public data, block, start, file, place and first description
    have all their other letters in common. `threeRead_unique`: so one reading.
  `ReadCollides h p block1 start1 g₁ l₁ x₁ file i`: there is a record of the reading at a first
    description made of g₁, l₁, x₁, and at its reading the file shows a collision.
  `readCollides_of`: from a record and `CollidesIn`.
  `keyCollides_of_record`, `proofCollides_of_record`: where the program's reader returns at the
    file at all, its value is the record's reading, so `CollidesIn` at the record's reading gives
    `KeyCollides` or `ProofCollides`.
Under "there is" in `ReadCollides`: the first chain's rounds and end, fixed by the dry run's
equation; the first description, fixed by its own equation at these rounds; the record's other
letters, fixed by `threeRead_same`; the third list of rounds, fixed by the equation of `Three.dry3`;
then the letters of `CollidesIn`.
Limits: that the program's reader returns is a premise of the last two laws. One law leads into
`ReadCollides` and none has it as a premise. No file beside this one calls `ReadCollides`,
`readCollides_of`, `keyCollides_of_record` or `proofCollides_of_record`: what others call is
`threeRead_same` and `threeRead_unique`. Nothing on how hard a collision is to find. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.Collides

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- A chain as read is fixed by what the strict reader returns, the place behind it and its view.
-/
theorem chainRead_ext {a b : ChainRead} (h1 : a.out = b.out) (h2 : a.view = b.view)
    (h3 : a.next = b.next) : a = b := by
  cases a
  cases b
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- **At one first description and one place the record fixes all its other letters.** -/
theorem threeRead_same {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start}
    {file : ByteArray} {i : ℕ} {S₁ : Fmt.SpecX}
    {R₁ : Rounds} {dry : FirstEnd} {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds}
    {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}
    {R₁' : Rounds} {dry' : FirstEnd} {r' : TailRead} {seal1' seal2' : ByteArray} {R₂' : Rounds}
    {dry2' : SharedEnd} {S₂' : Fmt.SpecX} {R₃' : Rounds} {S₃' : Fmt.SpecX}
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (T' : ThreeRead p block1 start1 file i R₁' dry' S₁ r' seal1' seal2' R₂' dry2' S₂' R₃' S₃') :
    R₁ = R₁' ∧ dry = dry' ∧ r = r' ∧ seal1 = seal1' ∧ seal2 = seal2' ∧ R₂ = R₂' ∧ dry2 = dry2' ∧
      S₂ = S₂' ∧ R₃ = R₃' ∧ S₃ = S₃' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T'.first_dry))
  obtain ⟨o1, n1⟩ := Prod.mk.inj (Option.some.inj (T.first_read.symm.trans T'.first_read))
  have f : r.first = r'.first :=
    chainRead_ext o1
      (T.first_view.trans ((congrArg (OnBytes.viewOf S₁) o1).trans T'.first_view.symm)) n1
  have e1 : seal1 = seal1' := Option.some.inj (T.first_seal.symm.trans (f ▸ T'.first_seal))
  subst e1
  have pl : r.place = r'.place :=
    Option.some.inj (T.place_read.symm.trans (f ▸ T'.place_read))
  have ky : r.key = r'.key := Option.some.inj (T.key_made.symm.trans T'.key_made)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.shared_dry.symm.trans (ky ▸ T'.shared_dry)))
  have s2 : S₂ = S₂' := Option.some.inj (T.shared_spec.symm.trans (pl ▸ T'.shared_spec))
  subst s2
  obtain ⟨o2, n2⟩ := Prod.mk.inj (Option.some.inj
    (T.shared_read.symm.trans (by rw [f, pl]; exact T'.shared_read)))
  have sh : r.shared = r'.shared :=
    chainRead_ext o2
      (T.shared_view.trans ((congrArg (OnBytes.viewOf S₂) o2).trans T'.shared_view.symm)) n2
  have e2 : seal2 = seal2' := Option.some.inj (T.shared_seal.symm.trans (sh ▸ T'.shared_seal))
  subst e2
  have r3 : R₃ = R₃' :=
    Option.some.inj (T.second_rounds.symm.trans (by rw [f, sh]; exact T'.second_rounds))
  subst r3
  have s3 : S₃ = S₃' := Option.some.inj (T.second_spec.symm.trans (by rw [f]; exact T'.second_spec))
  subst s3
  obtain ⟨o3, n3⟩ := Prod.mk.inj (Option.some.inj
    (T.second_read.symm.trans (by rw [sh]; exact T'.second_read)))
  have sc : r.second = r'.second :=
    chainRead_ext o3
      (T.second_view.trans ((congrArg (OnBytes.viewOf S₃) o3).trans T'.second_view.symm)) n3
  cases r
  cases r'
  simp only at f pl ky sh sc
  subst f pl ky sh sc
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- So the record fixes the reading. -/
theorem threeRead_unique {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start}
    {file : ByteArray} {i : ℕ} {S₁ : Fmt.SpecX}
    {R₁ : Rounds} {dry : FirstEnd} {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds}
    {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}
    {R₁' : Rounds} {dry' : FirstEnd} {r' : TailRead} {seal1' seal2' : ByteArray} {R₂' : Rounds}
    {dry2' : SharedEnd} {S₂' : Fmt.SpecX} {R₃' : Rounds} {S₃' : Fmt.SpecX}
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (T' : ThreeRead p block1 start1 file i R₁' dry' S₁ r' seal1' seal2' R₂' dry2' S₂' R₃' S₃') :
    r = r' := (threeRead_same T T').2.2.1

/-- **This file shows a collision of the leaf hash h**, at the reading that the record fixes. -/
def ReadCollides (h : HId) (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start)
    (g₁ : Params.Given) (l₁ : ℕ) (x₁ : ByteArray) (file : ByteArray) (i : ℕ) : Prop :=
  ∃ (R₁ : Rounds) (dry : FirstEnd) (S₁ : Fmt.SpecX) (r : TailRead) (seal1 seal2 : ByteArray)
    (R₂ : Rounds) (dry2 : SharedEnd) (S₂ : Fmt.SpecX) (R₃' : Rounds) (S₃ : Fmt.SpecX)
    (R₃ : Rounds),
    Params.describeWith g₁ l₁ x₁ .inFile R₁ 0 = some S₁ ∧
      ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ ∧
      Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃) ∧
      CollidesIn h (Three.Whole.of R₁ R₂ R₃) r p.shared.given.cfg

section
variable {h : HId} {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray}
  {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
  {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
  {S₃ : Fmt.SpecX} {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {R₃ : Rounds}

theorem readCollides_of
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ .inFile R₁ 0 = some S₁)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (c : CollidesIn h (Three.Whole.of R₁ R₂ R₃) r p.shared.given.cfg) :
    ReadCollides h p block1 start1 g₁ l₁ x₁ file i :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, hS₁, T, hd, c⟩

end

/-- **A key file: from the record to the reader's equation.** r₀: any value that the program's
reader returns at the file. -/
theorem keyCollides_of_record {h : HId} (k : Params.KeyChains) (table : Params.TableName)
    (file : ByteArray) (j : ℕ) (r₀ : TailRead)
    (h₀ : (Key.readKey k table file j).fromStart = .ok r₀)
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {R₃ : Rounds}
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : k.oneTime.describe table R₁ = some S₁)
    (hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some (R₁, R₂, R₃))
    (c : CollidesIn h (Three.Whole.of R₁ R₂ R₃) r k.shared.given.cfg) :
    KeyCollides h k table file j := by
  obtain ⟨Q₁, d0, Z₁, _, _, _, _, _, _, _, hZ₁, T₀⟩ := threeRead_of_readKey k table file j r₀ h₀
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T₀.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS₁.symm.trans hZ₁)
  obtain rfl := threeRead_unique T T₀
  refine ⟨r, (R₁, R₂, R₃), h₀, ?_, c⟩
  unfold dryKey
  rw [T.first_dry]
  exact hd

/-- **A proof file**, the like. -/
theorem proofCollides_of_record {h : HId} (c : Params.ProofChains) (table : Params.TableName)
    (copy : ℕ) (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r₀ : TailRead)
    (h₀ : (readProof c table copy request words block file).fromStart = .ok r₀) {i : ℕ}
    (hi : readProofHead c.first.given.plan.field file = .ok (copy, i))
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {R₃ : Rounds}
    (T : ThreeRead (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃' S₃)
    (hS₁ : c.first.describe table copy request words R₁ = some S₁)
    (hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some (R₁, R₂, R₃))
    (x : CollidesIn h (Three.Whole.of R₁ R₂ R₃) r c.shared.given.cfg) :
    ProofCollides h c table copy request words block file := by
  obtain ⟨i₀, Q₁, d0, Z₁, _, _, _, _, _, _, _, hi₀, hZ₁, T₀⟩ :=
    threeRead_of_readProof c table copy request words block file r₀ h₀
  obtain rfl : i = i₀ := by
    have := hi.symm.trans hi₀
    injection this with e
    exact (Prod.mk.inj e).2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T₀.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS₁.symm.trans hZ₁)
  obtain rfl := threeRead_unique T T₀
  refine ⟨r, (R₁, R₂, R₃), h₀, ?_, x⟩
  unfold dryProof
  rw [T.first_dry]
  exact hd

end OnBytes.Maker.Page
