-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/OwesOfGood.lean: the record of what is asked of a key file as read, of its
parameters and of its data (`PageOwes`, OnBytes/Maker/Page/Owes.lean), from the flat record of the
verifier program's check of the key file's three chains, the one-time chain's description at the
table, one setting of the three chains (`SameSetting`, twice), the dry runs' three lists at the
reading's key, and six tests. In `pageOwes_of_chains` these four are premises; in `pageOwes_key`
laws pay them.

Statements and proofs. Of the record's twenty-one fields five speak of the reading, eleven of the
parameters, five are tests. Of the first sixteen, six are those four premises handed through (the
first description, the dry runs' equation, two digests, two numbers of bytes of a salt) and two more
lean on them; the others are paid here by laws that lie. The number of bytes of a salt, the field
and the configuration's digest are the one-time chain's own.

Main names:
  `pageOwes_of_chains`: at a key's three chains k, a table, a file and the flat record of the check
    (`ThreeChains`, OnBytes/TieK/Chains.lean).
  `pageOwes_key`: at a good reading of a key file (`KeyGood`, OnBytes/TieK/Good.lean), with the
    three lists of rounds made at a fixed key with the item 0 that fits the table's shape, and the
    plan the planner's.
The six tests: `okAt`, `shapesFit`, `pageFitB`, `saltsFit`, that no round draws more than K blocks:
these five on the plain data of the rounds; and `SmallThree`, on the three descriptions and the
file.
Under "there is" in `pageOwes_key`: the file, tied by the equation of the fixed reading and by
nothing else: a good reading does not name its file; the place behind the table, fixed by the
equation of `Key.readTable` at that file. Who holds the file calls `pageOwes_of_chains`.
Limits: none of the six tests is shown here. `SmallThree` hangs on the file: in `pageOwes_key` it is
asked at every file with that fixed reading: `small_keyGood` (OnBytes/Maker/Page/SmallOf.lean) with
`readKeyChains_size` (OnBytes/TieK/ReadThreeSize.lean) would pay it; no file lays them together. No
file of this library calls `pageOwes_key`. Nothing on soundness.


-/
import OnBytes.Maker.Page.Owes
import OnBytes.Maker.Page.GoodCollides
import OnBytes.Maker.Page.GoodFields

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- **The record, from the flat record of the check of a key file's three chains.** -/
theorem pageOwes_of_chains (a K : ℕ) (k : Params.KeyChains) (table : Params.TableName)
    {file : ByteArray} {j : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
    {S₃ : Fmt.SpecX} {real : FirstEnd} {real2 : SharedEnd}
    (T : ThreeChains (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2)
    (hS : k.oneTime.describe table R₁ = some S₁)
    (s₂ : SameSetting k.oneTime.given k.shared.given)
    (s₃ : SameSetting k.oneTime.given k.second.given) (R : Rounds × Rounds × Rounds)
    (hR : dryKey k r.key = some R) (hok : okAt a (some R) = true)
    (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hpage : pageFitB a k.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit k.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsmall : SmallThree S₁ S₂ S₃ file)
    (hblocks : ∀ d ∈ (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₂ ++
        (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₃),
      (bsRound k.oneTime.given.plan.field d.entry d.kind).b ≤ K) :
    PageOwes (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j R₁ dry
      S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R.2.2 a k.oneTime.given.plan.salt K
      k.oneTime.given.plan.field k.oneTime.given.cfg := by
  have hS' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS
  have Tr := T.toRead
  unfold dryKey at hR
  rw [Tr.first_dry] at hR
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd Tr.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own k.oneTime Tr.first_dry
  have N := named_of_read Tr hS' b₁ R₃ hd
  obtain ⟨f₁, f₂, f₃⟩ := fields_of_read Tr hS'
  exact
    { read := Tr
      spec₁ := hS'
      rand₁ := fun e => by cases e
      dry3 := hd
      fits := (gives_of_chains a T hS' R₃ (alike_stored N) hok hsh
        (sealBare_of_fits (okAt_parts hok).fits)).fits
      own := o₁
      book := b₁
      cfg₁ := rfl
      cfg₂ := s₂.cfg.symm
      cfg₃ := s₃.cfg.symm
      salt₁ := rfl
      salt₂ := s₂.salt.symm
      salt₃ := s₃.salt.symm
      field₁ := f₁
      field₂ := f₂.trans s₂.field.symm
      field₃ := f₃.trans s₃.field.symm
      ok := hok
      page := hpage
      salts := hsalts
      small := hsmall
      blocks := hblocks }

/-- **The record at a good reading of a key file.** key₀: a fixed key at which the three lists R
were made. -/
theorem pageOwes_key (u : KeyPub) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R)
    (d : Params.TableName × ChainsData) (hg : KeyGood u d) (a K : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hpage : pageFitB a p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true)
    (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true)
    (hsmall : ∀ file, readKeyChains u.pol u.lay u.KL file = some d →
      SmallThree d.2.S1 d.2.S2 d.2.S3 file)
    (hblocks : ∀ x ∈ (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₂ ++
        (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₃),
      (bsRound p.chains.key.oneTime.given.plan.field x.entry x.kind).b ≤ K) :
    ∃ file j, readKeyChains u.pol u.lay u.KL file = some d ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg file =
        .ok (d.1, j) ∧
      PageOwes (Key.tailPublic p.chains.key d.1) (Key.oneTime p.chains.key.oneTime)
        (Key.startOf p.chains.key.oneTime) file j d.2.rounds1 d.2.dry d.2.S1 d.2.r d.2.seal1
        d.2.seal2 d.2.rounds2 d.2.dry2 d.2.S2 d.2.rounds3 d.2.S3 p.chains.key.oneTime.given
        Params.labelOneTime (Params.OneTime.statement d.1) .inFile R.2.2 a
        p.chains.key.oneTime.given.plan.salt K p.chains.key.oneTime.given.plan.field
        p.chains.key.oneTime.given.cfg := by
  obtain ⟨file, j, real, real2, hd, ht, hS, T⟩ := good_chains u p hp d hg
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  exact ⟨file, j, hd, ht, pageOwes_of_chains a K p.chains.key d.1 T hS s₂ s₃ R
    (good_dry3 u p hp key₀ h0 hf R hR d hg) hok hsh hpage hsalts (hsmall file hd) hblocks⟩

end OnBytes.Maker.Page
