-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Owes.lean: one record of what is asked of a file as read, of its parameters and
of its data. It is one of the premises of `after_read` (OnBytes/Maker/Page/AfterOf.lean), which has
the ten conditions of `AfterRuns` at the typing of the file. No field speaks of an oracle function;
`after_read` asks beside it two records on the oracle functions, that the typing returns, the three
chains' values, the silent rounds' test, the decision's yes at all alike views, and the first of the
commitments.

  `PageOwes .. a sb K f cfg`   the record. Its fields are of three kinds.
    THE READING: the record of the three chains' reading (`read`), the first chain's description
      (`spec₁`, `rand₁`), the dry run of the three chains at the reading's key (`dry3`), and what
      OnBytes/Maker/AcceptAt.lean asks of data and reading together (`fits`).
    THE PARAMETERS: the first chain's rounds and book name own trees alone (`own`, `book`); the
      three chains' parameter bytes have one configuration digest cfg, one number sb of salt bytes
      and the field f (`cfg₁` .. `field₃`).
    TESTS ON THE DATA, each a function that computes, or decidable: `ok`, `page`, `salts`, `small`
      (which also reads the file's length), `blocks`.
  `PageOwes.cfg32`       cfg has 32 bytes.
  `PageOwes.wholeFits`, `.storedFit`, `.second`, `.at₁`, `.at₂`, `.at₃`   what the test `ok` holds
                         on the rounds and the stored tables.
  `PageOwes.kit₁`, `.kit₂`, `.kit₃`   the kit of verifier's messages fits the three plans' fields.
  `PageOwes.hroot`       the stored table's root against the first of the commitments.
  `PageOwes.readOwes`    **what the walks owe of the file as read** (`ReadOwes`), at the hash over
                         the realised oracle.

Every field can be asked of one reading r, which is a letter of the caller. None says that two
readings, or two openings, agree.

Not claimed. That any file meets the record. That the typing returns a value. Nothing on soundness.


-/
import OnBytes.Maker.Page.ReadOwed
import OnBytes.Maker.Page.DataTestsLaws
import OnBytes.Maker.Page.Runs
import OnBytes.Maker.StoredOfFit
import OnBytes.Maker.EntriesPlan

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes OnBytes.Maker OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)
open _root_.Run _root_.Run.PQ

/-- **What is asked of a file as read, of its parameters and of its data.** -/
structure PageOwes (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start) (file : ByteArray)
    (i : ℕ) (R₁ : Rounds) (dry : FirstEnd) (S₁ : Fmt.SpecX) (r : TailRead)
    (seal1 seal2 : ByteArray) (R₂ : Rounds) (dry2 : SharedEnd) (S₂ : Fmt.SpecX) (R₃' : Rounds)
    (S₃ : Fmt.SpecX) (g₁ : Params.Given) (l₁ : ℕ) (x₁ : ByteArray) (n₁ : Fmt.Rand) (R₃ : Rounds)
    (a sb K : ℕ) (f : Fmt.Fld) (cfg : ByteArray) : Prop where
  /-- the reading: the three chains as read -/
  read : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃
  /-- the reading: the first chain's description -/
  spec₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁
  /-- the reading: the first chain has a run's value -/
  rand₁ : n₁ ≠ .none
  /-- the reading: the dry run of the three chains at the reading's key -/
  dry3 : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)
  /-- the reading: what is asked of data and reading together -/
  fits : ReadFits a (Three.Whole.of R₁ R₂ R₃) r S₁ S₂ S₃
  /-- the parameters: the first chain's rounds name own trees alone -/
  own : OwnAlone R₁
  /-- the parameters: so does its book -/
  book : OwnBook dry.book
  /-- the parameters: one configuration digest -/
  cfg₁ : g₁.cfg = cfg
  cfg₂ : p.shared.given.cfg = cfg
  cfg₃ : p.second.given.cfg = cfg
  /-- the parameters: one number of salt bytes -/
  salt₁ : g₁.plan.salt = sb
  salt₂ : p.shared.given.plan.salt = sb
  salt₃ : p.second.given.plan.salt = sb
  /-- the parameters: one field -/
  field₁ : S₁.base.plan.field = f
  field₂ : S₂.base.plan.field = f
  field₃ : S₃.base.plan.field = f
  /-- a test on the data: the tests under which a file's data are laid -/
  ok : okAt a (some (R₁, R₂, R₃)) = true
  /-- a test on the data: what the page's laws on the leaves ask -/
  page : pageFitB a sb (Three.Whole.of R₁ R₂ R₃) = true
  /-- a test on the data: every stored table of the three chains' rounds has salts of sb bytes -/
  salts : saltsFit sb (Three.Whole.of R₁ R₂ R₃) = true
  /-- a test on the descriptions and the file's length -/
  small : SmallThree S₁ S₂ S₃ file
  /-- a test on the data: no round draws more than K blocks -/
  blocks : ∀ d ∈ (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁ ++
    ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂ ++ (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃),
    (bsRound f d.entry d.kind).b ≤ K

namespace PageOwes
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand} {R₃ : Rounds} {a sb K : ℕ}
  {f : Fmt.Fld} {cfg : ByteArray}
  (O : PageOwes p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ g₁ l₁ x₁ n₁ R₃ a
    sb K f cfg)
include O

/-- cfg has 32 bytes. -/
theorem cfg32 : cfg.size = 32 := O.cfg₁ ▸ described_cfg32 O.spec₁

/-- The test on the rounds. -/
theorem wholeFits : Three.Whole.fits R₁ R₂ R₃ 2 = true := by
  have h := O.ok
  unfold okAt at h
  simp only [Bool.and_eq_true] at h
  tauto

/-- The test on the stored tables. -/
theorem storedFit : OnBytes.Maker.storedFit a (Three.Whole.of R₁ R₂ R₃) = true := by
  have h := O.ok
  unfold okAt at h
  simp only [Bool.and_eq_true] at h
  tauto

/-- The stored tables stand in the second chain alone. -/
theorem second : StoredSecond (Three.Whole.of R₁ R₂ R₃) := storedSecond_of_fit O.storedFit

theorem at₁ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₁ := fun d hd t ht => by
  rw [O.second.1 d hd] at ht
  cases ht

theorem at₃ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₃ := fun d hd t ht => by
  rw [O.second.2 d hd] at ht
  cases ht

theorem at₂ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₂ := fun d hd t ht => by
  have h := O.storedFit
  unfold OnBytes.Maker.storedFit at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have h1 := List.all_eq_true.1 (h.2 d hd) t ht
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h1
  exact h1

theorem kit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field (ckP f) K (chalP f K) :=
  kit_at f K S₁ O.field₁

theorem kit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field (ckP f) K (chalP f K) :=
  kit_at f K S₂ O.field₂

theorem kit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field (ckP f) K (chalP f K) :=
  kit_at f K S₃ O.field₃

/-- The three chains, read at the hash over the realised oracle. -/
theorem readAt : ReadAt (Fmt.HO Fmt.oracle) S₁ S₂ S₃ file i r :=
  ⟨(three_atOracle O.read O.small).1, (three_atOracle O.read O.small).2.1,
    (three_atOracle O.read O.small).2.2⟩

/-- **What the walks owe of the file as read.** -/
theorem readOwes : ReadOwes (Fmt.HO Fmt.oracle) cfg (Three.Whole.of R₁ R₂ R₃) r :=
  readOwes_of_read O.read O.readAt O.spec₁ O.rand₁ O.own O.book R₃ O.dry3 2 O.wholeFits cfg O.cfg₁
    O.cfg₂ O.cfg₃ sb a O.salt₁ O.salt₂ O.salt₃ O.at₁ O.at₂ O.at₃ O.second

/-- The digest of the root to which each opening of a stored table has walked is the first of the
commitments, if that is the digest of the root in item 0 of the second chain's statement. -/
theorem hroot (cms : List (_root_.Iop.Dig 256))
    (hc : ∀ root, Fmt.itemRoot (Params.Shared.statement p.table r.place.root) 0 = some root →
      cms.getD 0 default = bytesToDig root) :
    ∀ t z, (t, z) ∈ storedRowsW (Three.Whole.of R₁ R₂ R₃) r →
      bytesToDig z.2.2.root = cms.getD 0 default :=
  hroot_of_read O.read O.spec₁ O.book R₃ O.dry3 2 O.wholeFits sb a O.salt₁ O.salt₂ O.salt₃ O.at₁
    O.at₂
    O.at₃ O.second cms hc

end PageOwes

end OnBytes.Maker.Page
