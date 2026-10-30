-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/OwesOfGoodP.lean: the record of what is asked of a proof file as read, of its
parameters and of its data (`PageOwes`, OnBytes/Maker/Page/Owes.lean), from the flat record of the
verifier program's check of the proof file's three chains, the first chain's description, one
setting of the three chains, the dry runs' three lists at the reading's key, and six tests. In
`pageOwes_of_chainsP` the first four are premises; in `pageOwes_proof` laws pay these four.

Statements and proofs: the like of OnBytes/Maker/Page/OwesOfGood.lean for a proof file. The number
of bytes of a salt, the field and the configuration's digest are the first chain's own. That the
first chain's rounds and book name own trees alone is a premise of the first law; at the program's
own block OnBytes/Maker/ProofOwn.lean pays it.

Main names:
  `pageOwes_of_chainsP`: at a proof's three chains c, a table, the stored copy's number, the
    request's item, the request file's bytes, the first chain's block, a file and the flat record of
    the check.
  `pageOwes_proof`: at a good reading of a proof file (`ProofGood`, OnBytes/TieK/Good.lean), at the
    block that the program's check lays, with the three lists of rounds made at a fixed key.
The six tests: as in OwesOfGood.lean.
Under "there is" in `pageOwes_proof`: the entry file, the copy's number and the proof file, tied by
the equation of the fixed reading and by nothing else; the place behind the head, fixed by the
equation of `readProofHead` at that file; the request's item, fixed by its own equation.
Limits: none of the six tests is shown here. The data are those of the rounds at this request's
block. `SmallThree` hangs on the file: in `pageOwes_proof` it is asked at every entry file, copy's
number and proof file with that fixed reading, and no law of this library pays it in that form. No
file beside this one calls `pageOwes_proof`. Nothing on soundness.


-/
import OnBytes.Maker.Page.OwesOfGood

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- **The record, from the flat record of the check of a proof file's three chains.** -/
theorem pageOwes_of_chainsP (a K : ℕ) (c : Params.ProofChains) (table : Params.TableName)
    (copy : ℕ) (request words : ByteArray) (block : Blk FirstEnd)
    {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
    {S₃ : Fmt.SpecX} {real : FirstEnd} {real2 : SharedEnd}
    (T : ThreeChains (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃' S₃ real real2)
    (hS : c.first.describe table copy request words R₁ = some S₁) (o₁ : OwnAlone R₁)
    (b₁ : OwnBook dry.book) (s₂ : SameSetting c.first.given c.shared.given)
    (s₃ : SameSetting c.first.given c.second.given) (R : Rounds × Rounds × Rounds)
    (hR : dryProof c r.key block = some R) (hok : okAt a (some R) = true)
    (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hpage : pageFitB a c.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit c.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsmall : SmallThree S₁ S₂ S₃ file)
    (hblocks : ∀ d ∈ (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₂ ++
        (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₃),
      (bsRound c.first.given.plan.field d.entry d.kind).b ≤ K) :
    PageOwes (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2 R₂ dry2
      S₂ R₃' S₃ c.first.given Params.labelFirst (Params.First.statement table copy request words)
          .inFile
      R.2.2 a c.first.given.plan.salt K c.first.given.plan.field c.first.given.cfg := by
  have hS' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS
  have Tr := T.toRead
  unfold dryProof at hR
  rw [Tr.first_dry] at hR
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd Tr.shared_dry
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

/-- **The record at a good reading of a proof file.** key₀: a fixed key at which the three lists R
were made, at the block that the program's check lays. -/
theorem pageOwes_proof (u : ProofPub) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (so : Model.Head.StOwn)
    (hso : Model.Head.stFromCall (Model.Verify.words32 u.request) (Model.Verify.words32 u.y)
      p.X.T = .ok so)
    (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
    (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
    (d : Params.TableName × ChainsData) (hg : ProofGood u d) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds)
    (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R) (a K : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hpage : pageFitB a p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true)
    (hsalts : saltsFit p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true)
    (hsmall : ∀ ent copy file,
      readProofChains u.pol u.lay u.KL u.request u.y ent copy file = some d →
      SmallThree d.2.S1 d.2.S2 d.2.S3 file)
    (hblocks : ∀ x ∈ (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₂ ++
        (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₃),
      (bsRound p.chains.proof.first.given.plan.field x.entry x.kind).b ≤ K) :
    ∃ ent copy file i item,
      readProofChains u.pol u.lay u.KL u.request u.y ent copy file = some d ∧
      readProofHead p.chains.proof.first.given.plan.field file = .ok (copy, i) ∧
      Proof.requestItem u.pol u.KL u.request = some item ∧
      PageOwes (tailPublic p.chains.proof d.1) (blockAt p links so.y)
        (firstStart p.chains.proof.first) file i d.2.rounds1 d.2.dry d.2.S1 d.2.r d.2.seal1
        d.2.seal2 d.2.rounds2 d.2.dry2 d.2.S2 d.2.rounds3 d.2.S3 p.chains.proof.first.given
        Params.labelFirst (Params.First.statement d.1 copy item u.request) .inFile R.2.2 a
        p.chains.proof.first.given.plan.salt K p.chains.proof.first.given.plan.field
        p.chains.proof.first.given.cfg := by
  obtain ⟨ent, copy, file, i, item, real, real2, hd, -, hh, hi, hS, T⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  obtain ⟨-, s₂, s₃⟩ := setting_proofGood hg hp
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) T.first_dry
  exact ⟨ent, copy, file, i, item, hd, hh, hi,
    pageOwes_of_chainsP a K p.chains.proof d.1 copy item u.request (blockAt p links so.y) T hS o₁ b₁
        s₂ s₃ R
      (good_dry3P u p hp so hso cov hcov links hl d hg key₀ h0 hf R hR) hok hsh hpage hsalts
      (hsmall ent copy file hd) hblocks⟩

end OnBytes.Maker.Page
