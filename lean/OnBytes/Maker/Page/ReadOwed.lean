-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/ReadOwed.lean: what the walks of a file's forests owe of the file as read
(`ReadOwes`, OnBytes/Maker/WalksOf.lean) is paid by the record of the three chains' reading.

OnBytes/Maker/Page/OwesH.lean has, from the record `ThreeRead` of a reading of a key file or a proof
file and the three chains' readings by the strict reader at a hash h (`ReadAt`), what the trees'
openings give and what the stored table's openings give, at h. Their fields are the fields of
`ReadOwes` in other brackets. Here they are laid over, and the two counts of roots and the 32 bytes
of each sender's run's value (OnBytes/Maker/RunSize.lean) are paid from the readings.

  `readOwesH_of`       `ReadOwes` at h from the two records at h.
  `readOwes_of_read`   `ReadOwes` at the hash h, the one digest cfg and the data made of the three
                       lists of rounds.
  `hroot_of_read`      the digest of the root to which each opening of a stored table has walked is
                       the first of the commitments, if that is the digest of the root in item 0 of
                       the second chain's statement, under twelve further hypotheses, which are
                       among those of the second (below): the record of the reading, the first
                       chain's description, `OwnBook`, the dry run, `Whole.fits`, one number of salt
                       bytes in the three chains, `StoredAt` at the three lists, `StoredSecond`.

The premises of the second. The record of the reading, the three readings at h, and the first
chain's description, which has a run's value (`hn`). Of the first chain's rounds and book: they name
own trees alone (`OwnAlone`, `OwnBook`). The dry run of the three chains; the test `Whole.fits` on
its three lists. One digest cfg and one number of salt bytes in the three chains' parameter bytes.
The stored tables stand in the second chain alone, at the depth a (`StoredSecond`, `StoredAt`). None
is shown here.

Not claimed. Nothing on any oracle function; nothing on opening-form binding, no two openings,
correctness of extraction or whatever else names a committer or a prover; nothing on soundness.

-/
import OnBytes.Maker.WalksOf
import OnBytes.Maker.Page.OwesH
import OnBytes.Maker.RunSize

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes OnBytes.Maker OnBytes.Proof OnBytes.Params
open _root_.Iop (Dig)
open _root_.Run (bytesToDig HId)

/-- `ReadOwes` at h from the two records at h. -/
theorem readOwesH_of {h : HId} {W : Three.Whole} {r : Proof.TailRead} {cfg st : ByteArray}
    (T : TreesOwedH h W r cfg) (S : StoredOwedH h W r cfg st) (n₁ : W.t₁ = r.first.roots.length)
    (n₂ : W.t₂ = r.shared.roots.length)
    (run32 : ∀ j run, runOfTree W r j = some run → run.size = 32) : ReadOwes h cfg W r where
  one := fun j z z' hz hz' => T.one (j, z) hz (j, z') hz' rfl
  walked := fun j z hz => T.walked (j, z) hz
  size := T.size
  seen := fun j z hz => T.leaf (j, z) hz
  tree := fun j z hz => T.root (j, z) hz
  n₁ := n₁
  n₂ := n₂
  run32 := run32
  oneE := S.one
  walkedE := fun t z hz => S.walked (t, z) hz
  sizeE := S.size
  seenE := fun t z hz => S.leaf (t, z) hz

section
variable {h : HId} {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray}
  {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **What the walks owe of the file as read, from the record of the reading.** -/
theorem readOwes_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (A : ReadAt h S₁ S₂ S₃ file i r)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (cfg : ByteArray) (c₁ : g₁.cfg = cfg)
    (c₂ : p.shared.given.cfg = cfg) (c₃ : p.second.given.cfg = cfg) (sb a : ℕ)
    (s₁ : g₁.plan.salt = sb) (s₂ : p.shared.given.plan.salt = sb)
    (s₃ : p.second.given.plan.salt = sb) (a₁ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₁)
    (a₂ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₂) (a₃ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₃)
    (hs : StoredSecond (Three.Whole.of R₁ R₂ R₃)) :
    ReadOwes h cfg (Three.Whole.of R₁ R₂ R₃) r :=
  readOwesH_of (treesOwedH_of_readX T A hS₁ hn o₁ b₁ R₃ hd m hf cfg c₁ c₂ c₃)
    (c₂ ▸ storedOwedH_of_readX T A hS₁ b₁ R₃ hd m hf sb a s₁ s₂ s₃ a₁ a₂ a₃ hs)
    (readChain_roots hS₁ [] file i r.first T.first_read).symm
    (readChain_roots T.shared_spec r.first.out.seen file r.place.next r.shared T.shared_read).symm
    (runOfTree_32 _ S₁ S₂ S₃ r file _ _ _ _ _ _ _ _ _ T.first_read T.shared_read T.second_read)

/-- **The stored table's root, from the record of the reading.** -/
theorem hroot_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (sb a : ℕ) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (a₁ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₁) (a₂ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₂)
    (a₃ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₃) (hs : StoredSecond (Three.Whole.of R₁ R₂ R₃))
    (cms : List (Dig 256))
    (hc : ∀ root, Fmt.itemRoot (Params.Shared.statement p.table r.place.root) 0 = some root →
      cms.getD 0 default = bytesToDig root) :
    ∀ t z, (t, z) ∈ storedRowsW (Three.Whole.of R₁ R₂ R₃) r →
      bytesToDig z.2.2.root = cms.getD 0 default :=
  fun t z hz =>
    (hc _ ((storedOwed_of_read T hS₁ b₁ R₃ hd m hf sb a s₁ s₂ s₃ a₁ a₂ a₃ hs).root (t, z) hz)).symm

end

end OnBytes.Maker.Page
