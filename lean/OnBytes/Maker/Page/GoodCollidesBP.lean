-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GoodCollidesBP.lean: where the verifier program has said yes to a proof file, if
three tests on the plain data pass: either the six parts of the typing return at the fixed reading
of that file, or the file shows a collision of the format's hash: two entries out of its own lists
as read give two different strings of bytes with one answer, at one number, label, index and start.

Statements and proofs: the like of OnBytes/Maker/Page/GoodCollidesB.lean for a proof file.

Main names:
  `chainsP_returns_or_collidesInB`: at the record of the reading of a proof's three chains.
  `goodP_returns_or_collidesInB`: at a good reading of a proof file (`ProofGood`).
  `portP_returns_or_collidesB`: at the files F to which the program has said yes (`K.PortYesAt`):
    `typeReturns .. = true ∨ ProofCollidesB Fmt.formatHash p.chains.proof further F.entry item F.request
    block ..`, at F's proof file, block the one that the program's check lays.
The three tests: `okAt`, `oneShapeB`, `saltsFit`, on the plain data of the rounds at this request's
block. The two upper laws ask beside them a fixed key key₀ of the caller's with the item 0 that fits
the tables' shape, and that the dry runs at key₀ return the three lists R at which the tests stand.
No letter stands under "there is" in the last law but those of `ProofCollidesB`.
Limits: the tests are not shown here. The data hang on the request through the block. cfg, the
typing's letter, is free. No file beside this one calls `goodP_returns_or_collidesInB`. Nothing on
how hard such a file is to make. Nothing on opening-form binding, no two openings, correctness of
extraction, what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.GoodCollidesB
import OnBytes.Maker.Page.PortReads
import OnBytes.TieK.HolesOfChains

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- **At the record of the reading of a proof's three chains.** -/
theorem chainsP_returns_or_collidesInB (C : CK) (a : ℕ) (cfg : ByteArray)
    (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ) (request words : ByteArray)
    (block : Blk FirstEnd) {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd}
    {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd}
    {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
    (T : ThreeRead (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃' S₃)
    (hS : c.first.describe table copy request words R₁ = some S₁) (o₁ : OwnAlone R₁)
    (b₁ : OwnBook dry.book) (s₂ : SameSetting c.first.given c.shared.given)
    (s₃ : SameSetting c.first.given c.second.given) (R : Rounds × Rounds × Rounds)
    (hR : dryProof c r.key block = some R) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit c.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) c.first.given.plan.salt cfg r = true ∨
      CollidesInB Fmt.formatHash (Three.Whole.of R.1 R.2.1 R.2.2) r c.shared.given.cfg := by
  have hS' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS
  unfold dryProof at hR
  rw [T.first_dry] at hR
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  exact returns_or_collidesInB Fmt.formatHash C a c.first.given.plan.salt cfg c.shared.given.cfg T
    (readAt_H T) hS' (fun e => by cases e) o₁ b₁ R₃ hd hok (okAt_parts hok).fits
    (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm s₂.cfg rfl (s₃.cfg.symm.trans s₂.cfg) hB
    (oneSaltB_of_saltsFit hsalts)

section
variable (p : Model.Verify.Planned) (so : Model.Head.StOwn) (cov : Model.Head.Covered)
  (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
  (key₀ : TableKey) (h0 : key₀.item = 0)
  (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds)
  (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R) (C : CK) (a : ℕ)
  (cfg : ByteArray) (hok : okAt a (some R) = true)
  (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hsalts : saltsFit p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
include hl h0 hf hR hok hB hsalts

/-- **At a good reading of a proof file.** -/
theorem goodP_returns_or_collidesInB (u : ProofPub)
    (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p)
    (hso : Model.Head.stFromCall (Model.Verify.words32 u.request) (Model.Verify.words32 u.y)
      p.X.T = .ok so)
    (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
    (d : Params.TableName × ChainsData) (hg : ProofGood u d) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.proof.first.given.plan.salt cfg
        d.2.r = true ∨
      CollidesInB Fmt.formatHash (Three.Whole.of R.1 R.2.1 R.2.2) d.2.r
        p.chains.proof.shared.given.cfg := by
  obtain ⟨ent, copy, file, i, item, real, real2, -, -, -, -, hS, T⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  obtain ⟨-, s₂, s₃⟩ := setting_proofGood hg hp
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) T.first_dry
  exact chainsP_returns_or_collidesInB C a cfg p.chains.proof d.1 copy item u.request (blockAt p
      links so.y)
    T.toRead hS o₁ b₁ s₂ s₃ R (good_dry3P u p hp so hso cov hcov links hl d hg key₀ h0 hf R hR) hok
    hB hsalts

/-- **At the files to which the program has said yes.** d: the fixed reading of F's proof file. -/
theorem portP_returns_or_collidesB (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (hso : Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y)
      p.X.T = .ok so)
    (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov) (item : ByteArray)
    (hitem : Proof.requestItem F.pol F.KL F.request = some item) (d : ChainsData)
    (hd : readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
      some (further, d)) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.proof.first.given.plan.salt cfg
        d.r = true ∨
      ProofCollidesB Fmt.formatHash p.chains.proof further F.entry item F.request (blockAt p links so.y)
          F.proof := by
  have he := port_entry F id table further h
  have ho := port_proof_chains F id table further h
  have hg : ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d) :=
    ⟨F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩
  obtain ⟨p', so', cov', item', links', i, d', real, real2, hp', hso', hcov', hi', hl', hh, hd',
    hS, T, -, -⟩ := readProofChains_of F table further he ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : so = so' := Except.ok.inj (hso.symm.trans hso')
  obtain rfl : cov = cov' := Except.ok.inj (hcov.symm.trans hcov')
  obtain rfl : item = item' := Option.some.inj (hitem.symm.trans hi')
  obtain rfl : links = links' := Except.ok.inj (hl.symm.trans hl')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  have Tr : ThreeRead (tailPublic p.chains.proof further) (blockAt p links so.y)
      (firstStart p.chains.proof.first) F.proof i d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
      d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 := T.toRead
  obtain ⟨-, s₂, s₃⟩ := setting_proofGood hg hp
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) Tr.first_dry
  have hR' : dryProof p.chains.proof d.r.key (blockAt p links so.y) = some R :=
    good_dry3P ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ p hp so hso cov hcov links hl (further, d) hg
      key₀ h0 hf R hR
  obtain ⟨q, so₂, cov₂, item₂, links₂, r₀, hq, g1, g2, g3, g4, h₀, -⟩ := port_proof_reads h
  obtain rfl : p = q := Except.ok.inj (hp.symm.trans hq)
  obtain rfl : so = so₂ := Except.ok.inj (hso.symm.trans g1)
  obtain rfl : cov = cov₂ := Except.ok.inj (hcov.symm.trans g2)
  obtain rfl : item = item₂ := Option.some.inj (hitem.symm.trans g3)
  obtain rfl : links = links₂ := Except.ok.inj (hl.symm.trans g4)
  rcases chainsP_returns_or_collidesInB C a cfg p.chains.proof further F.entry item F.request
    (blockAt p links so.y) Tr hS o₁ b₁ s₂ s₃ R hR' hok hB hsalts with hr | hc
  · exact Or.inl hr
  · have hR2 := hR'
    unfold dryProof at hR2
    rw [Tr.first_dry] at hR2
    have hd3 : Three.dry3 (tailPublic p.chains.proof further) d.r.key (d.rounds1, d.dry) =
        some R := hR2
    obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
    exact Or.inr (proofCollidesB_of_record p.chains.proof further F.entry item F.request
      (blockAt p links so.y) F.proof r₀ h₀ hh Tr hS hd3 hc)

end

end OnBytes.Maker.Page
