-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/RecordBytes.lean: for whoever holds the record of a file's reading (`ThreeRead`)
and not the reader's equation: "the six parts of the typing return, or the file shows a collision"
with the hash's arguments written out; the way from the record to `KeyCollidesB` and
`ProofCollidesB`; and the bounds `SmallAt` from three tests at one record.

Statements and proofs. OnBytes/Maker/Page/CollidesBytes.lean has the tops at the two readers' own
equations. Here the same is said at a record. The law asks `oneSaltB`; the test `saltsFit`
(OnBytes/Maker/TablesRow.lean), which the callers hold, gives it.

Main names:
  `oneSaltB_of_saltsFit`: the test `saltsFit sb W` gives `oneSaltB W`.
  `returns_or_collidesInB`: at a record, at any hash h with `ReadAt h`:
    `typeReturns .. = true ∨ CollidesInB h ..`.
  `keyCollidesB_of_record`, `proofCollidesB_of_record`: where the program's reader returns at the
    file at all, `CollidesInB` at the record's reading gives `KeyCollidesB` or `ProofCollidesB`.
  `smallAt_of`: `SmallThree` at one record of the reading gives `SmallAt`
    (OnBytes/Maker/Page/CollidesOracle.lean): so the bounds are three tests that a program can run
    at that record's three descriptions and the file.
No letter stands under "there is" but those of the propositions named.
Limits: the bounds are tests on the file and on descriptions that hold what was read off it: a run
at some files pays them at these files alone; no law here gives them from the reading. That the
program's reader returns is a premise of the two laws in the middle. Nothing on how hard such a file
is to make. Nothing on opening-form binding, no two openings of a commitment, correctness of
extraction, what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.CollidesBytes
import OnBytes.Maker.Page.ReadCollides
import OnBytes.Maker.TablesRow

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- The test that every stored table has salts of sb bytes gives that all have one number. -/
theorem oneSaltB_of_saltsFit {sb : ℕ} {W : Three.Whole} (h : saltsFit sb W = true) :
    oneSaltB W = true := by
  have key : ∀ t ∈ storedOf W, t.salt = sb := by
    intro t ht
    obtain ⟨d, hd, hm⟩ := List.mem_flatMap.1 ht
    unfold saltsFit at h
    exact eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 h d hd) t hm)
  unfold oneSaltB
  rw [List.all_eq_true]
  intro t ht
  rw [List.all_eq_true]
  intro t' ht'
  rw [key t ht, key t' ht']
  exact beq_self_eq_true _

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **At a record: either the typing's six parts return, or two entries out of the file's own lists
give two different strings of bytes with one answer of h.** -/
theorem returns_or_collidesInB (h : HId) (C : CK) (a sb : ℕ) (cfg cfgS : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (A : ReadAt h S₁ S₂ S₃ file i r)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (c₁ : g₁.cfg = cfgS) (c₂ : p.shared.given.cfg = cfgS) (c₃ : p.second.given.cfg = cfgS)
    (hB : oneShapeB (Three.Whole.of R₁ R₂ R₃) = true)
    (hZ : oneSaltB (Three.Whole.of R₁ R₂ R₃) = true) :
    typeReturns C a (Three.Whole.of R₁ R₂ R₃) sb cfg r = true ∨
      CollidesInB h (Three.Whole.of R₁ R₂ R₃) r cfgS :=
  (returns_or_collidesAt h C a sb cfg cfgS T A hS₁ hn o₁ b₁ R₃ hd hok hfit hst s₁ s₂ s₃ c₁ c₂ c₃
    hB).imp id fun c => c.bytes (sizesOne_of_read a sb T hS₁ b₁ R₃ hd hfit hst s₁ s₂ s₃ hB hZ)

/-- **The bounds at one record of the reading give them at every record with that first description
and place.** -/
theorem smallAt_of
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ .inFile R₁ 0 = some S₁)
    (hsm : SmallThree S₁ S₂ S₃ file) : SmallAt p block1 start1 g₁ l₁ x₁ file i r := by
  intro Q₁ d0 Z₁ z1 z2 Q₂ d2 Z₂ Q₃ Z₃ hZ₁ T₀
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T₀.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS₁.symm.trans hZ₁)
  obtain ⟨-, -, -, -, -, -, -, rfl, -, rfl⟩ := threeRead_same T T₀
  exact hsm

end

/-- **A key file: from the record to the reader's equation**, with the hash's arguments written
out. r₀: any value that the program's reader returns at the file. -/
theorem keyCollidesB_of_record {h : HId} (k : Params.KeyChains) (table : Params.TableName)
    (file : ByteArray) (j : ℕ) (r₀ : TailRead)
    (h₀ : (Key.readKey k table file j).fromStart = .ok r₀)
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {R₃ : Rounds}
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : k.oneTime.describe table R₁ = some S₁)
    (hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some (R₁, R₂, R₃))
    (c : CollidesInB h (Three.Whole.of R₁ R₂ R₃) r k.shared.given.cfg) :
    KeyCollidesB h k table file j := by
  obtain ⟨Q₁, d0, Z₁, _, _, _, _, _, _, _, hZ₁, T₀⟩ := threeRead_of_readKey k table file j r₀ h₀
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T₀.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS₁.symm.trans hZ₁)
  obtain rfl := threeRead_unique T T₀
  refine ⟨r, (R₁, R₂, R₃), h₀, ?_, c⟩
  unfold dryKey
  rw [T.first_dry]
  exact hd

/-- **A proof file**, the like. -/
theorem proofCollidesB_of_record {h : HId} (c : Params.ProofChains) (table : Params.TableName)
    (copy : ℕ) (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r₀ : TailRead)
    (h₀ : (readProof c table copy request words block file).fromStart = .ok r₀) {i : ℕ}
    (hi : readProofHead c.first.given.plan.field file = .ok (copy, i))
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {R₃ : Rounds}
    (T : ThreeRead (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃' S₃)
    (hS₁ : c.first.describe table copy request words R₁ = some S₁)
    (hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some (R₁, R₂, R₃))
    (x : CollidesInB h (Three.Whole.of R₁ R₂ R₃) r c.shared.given.cfg) :
    ProofCollidesB h c table copy request words block file := by
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
