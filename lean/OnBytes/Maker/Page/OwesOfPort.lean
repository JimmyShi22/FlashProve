-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/OwesOfPort.lean: where the verifier program has said yes, the record of what is
asked of the key file and of the proof file as read (`PageOwes`, OnBytes/Maker/Page/Owes.lean), at
the files themselves, from five tests on the plain data of the three lists R that the dry runs give
at a fixed key key₀ (item 0; it fits the tables' shape); and "the six parts of the typing return, or
the file shows a collision" at the hash over the realised oracle.

Statements and proofs. OnBytes/Maker/Page/OwesOfGood.lean and OwesOfGoodP.lean have the record from
the flat record of the program's check and six tests, the sixth (`SmallThree`) on the file.
OnBytes/Maker/Page/SmallOfP.lean pays the sixth where the program has said yes. `smallAt_of`
(OnBytes/Maker/Page/RecordBytes.lean) leads from it to the bounds `SmallAt`; it is not called here.

Main names:
  `port_proof_parts`: what the program's yes gives at F's proof file and its fixed reading: the
    head's equation, the first description, the flat record of the check, one setting of the three
    chains, the dry runs' lists at the reading's key, the stored copy's number. Other files call it.
  `pageOwes_port_key`: at F's key file and its fixed reading.
  `pageOwes_port_proof`: at F's proof file and its fixed reading; the stored copy's number is F's.
  `port_returns_or_collidesBO`, `portP_returns_or_collidesBO`: the second arm is `KeyCollidesB` or
    `ProofCollidesB` at `Fmt.HO Fmt.oracle`.
The five tests: `okAt`, `shapesFit`, `pageFitB`, `saltsFit`, and that no round draws more than K
blocks: all on the plain data of the rounds. `pageFitB` gives `saltsFit` at the same letters, so the
five are four. Four of the record's twenty-one fields are these premises handed through. The laws on
a collision ask `okAt`, `shapesFit`, `oneShapeB` and `saltsFit`.
Under "there is": the place behind the table or the head, fixed by the equation of `Key.readTable`
or `readProofHead` at F's file; in `port_proof_parts` also the two decisions real and real2, fixed
by the record's fields `first_yes` and `shared_yes`.
Limits: the tests are not shown here. At a proof file the data are those of the rounds at this
request's block. In the two laws on a collision the reading is the program's, at `Fmt.formatHash`, and the
collision is asked at the other hash; no law of this library takes that mixed form as a premise. No
file beside this one calls `pageOwes_port_key`, `pageOwes_port_proof`, `port_returns_or_collidesBO`
or `portP_returns_or_collidesBO`: `port_key_orMO` (OnBytes/Maker/Page/TwinKey.lean) and
`port_proof_orM` (OnBytes/Maker/Page/CollidesM.lean) have a second arm with reader and collision at
one hash. Nothing on opening-form binding, no two openings, correctness of
extraction, what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.SmallOfP
import OnBytes.Maker.Page.OwesOfGoodP

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

section Key
variable (F : K.Files) (id : String) (table further : Params.TableName)
  (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
  (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
  (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
  (h0 : key₀.item = 0)
  (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
  (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
include h hp hd h0 hf hR hok hsh hsalts

/-- **The record at F's key file.** -/
theorem pageOwes_port_key (K : ℕ)
    (hpage : pageFitB a p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true)
    (hblocks : ∀ x ∈ (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₂ ++
        (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₃),
      (bsRound p.chains.key.oneTime.given.plan.field x.entry x.kind).b ≤ K) :
    ∃ j, Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      PageOwes (Key.tailPublic p.chains.key table) (Key.oneTime p.chains.key.oneTime)
        (Key.startOf p.chains.key.oneTime) F.key j d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 p.chains.key.oneTime.given Params.labelOneTime
        (Params.OneTime.statement table) .inFile R.2.2 a p.chains.key.oneTime.given.plan.salt K
        p.chains.key.oneTime.given.plan.field p.chains.key.oneTime.given.cfg := by
  have ho := port_key_chains F id table further h
  have hg : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  exact ⟨j, ht, pageOwes_of_chains a K p.chains.key table T hS s₂ s₃ R
    (good_dry3 ⟨F.pol, F.lay, F.KL⟩ p hp key₀ h0 hf R hR (table, d) hg) hok hsh hpage hsalts
    (small_port_key F id table further h p hp d hd key₀ h0 hf R hR a hok hsh) hblocks⟩

/-- **A key file: the typing's six parts return, or the file shows a collision of the hash over the
realised oracle.** -/
theorem port_returns_or_collidesBO (C : CK) (cfg : ByteArray)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    ∃ j, Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      (typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.key.oneTime.given.plan.salt cfg
          d.r = true ∨
        KeyCollidesB (Fmt.HO Fmt.oracle) p.chains.key table F.key j) := by
  have ho := port_key_chains F id table further h
  have hg : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  have hsm := small_port_key F id table further h p hp d hd key₀ h0 hf R hR a hok hsh
  have Tr := T.toRead
  have hS' : Params.describeWith p.chains.key.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile d.rounds1 0 = some d.S1 := hS
  have hR' : dryKey p.chains.key d.r.key = some R :=
    good_dry3 ⟨F.pol, F.lay, F.KL⟩ p hp key₀ h0 hf R hR (table, d) hg
  obtain ⟨q, j₀, r₀, hq, ht₀, h₀, -⟩ := port_key_reads h
  obtain rfl : p = q := Except.ok.inj (hp.symm.trans hq)
  obtain rfl : j = j₀ := by
    have := ht.symm.trans ht₀
    injection this with e
    exact (Prod.mk.inj e).2
  refine ⟨j, ht, ?_⟩
  have hR2 := hR'
  unfold dryKey at hR2
  rw [Tr.first_dry] at hR2
  have hd3 : Three.dry3 (Key.tailPublic p.chains.key table) d.r.key (d.rounds1, d.dry) =
      some R := hR2
  obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own p.chains.key.oneTime Tr.first_dry
  rcases returns_or_collidesInB (Fmt.HO Fmt.oracle) C a p.chains.key.oneTime.given.plan.salt cfg
    p.chains.key.shared.given.cfg Tr (readAt_O Tr hsm) hS' (fun e => by cases e) o₁ b₁ R₃ hd3 hok
    (okAt_parts hok).fits (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm s₂.cfg rfl
    (s₃.cfg.symm.trans s₂.cfg) hB (oneSaltB_of_saltsFit hsalts) with hr | hc
  · exact Or.inl hr
  · exact Or.inr (keyCollidesB_of_record p.chains.key table F.key j r₀ h₀ Tr hS hd3 hc)

end Key

section Proof
variable (F : K.Files) (id : String) (table further : Params.TableName)
  (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
  (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (so : Model.Head.StOwn)
  (hso : Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y)
    p.X.T = .ok so)
  (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
  (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
  (item : ByteArray) (hitem : Proof.requestItem F.pol F.KL F.request = some item) (d : ChainsData)
  (hd : readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d))
  (key₀ : TableKey) (h0 : key₀.item = 0)
  (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds)
  (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R) (a : ℕ)
  (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
  (hsalts : saltsFit p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true)
include h hp hso hcov hl hitem hd h0 hf hR hok hsh hsalts

omit hok hsh hsalts in
/-- What the two laws on a proof file share: the place behind the head, the record of the reading,
the first description, the setting, and the dry runs at the reading's key. -/
theorem port_proof_parts :
    ∃ i real real2, readProofHead p.chains.proof.first.given.plan.field F.proof =
        .ok (F.entry, i) ∧
      p.chains.proof.first.describe further F.entry item F.request d.rounds1 = some d.S1 ∧
      ThreeChains (tailPublic p.chains.proof further) (blockAt p links so.y)
        (firstStart p.chains.proof.first) F.proof i d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 real real2 ∧
      SameSetting p.chains.proof.first.given p.chains.proof.shared.given ∧
      SameSetting p.chains.proof.first.given p.chains.proof.second.given ∧
      dryProof p.chains.proof d.r.key (blockAt p links so.y) = some R ∧ d.copy = F.entry := by
  have he := port_entry F id table further h
  have ho := port_proof_chains F id table further h
  have hg : ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d) :=
    ⟨F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩
  obtain ⟨p', so', cov', item', links', i, d', real, real2, hp', hso', hcov', hi', hl', hh, hd',
    hS, T, -, hcp⟩ := readProofChains_of F table further he ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : so = so' := Except.ok.inj (hso.symm.trans hso')
  obtain rfl : cov = cov' := Except.ok.inj (hcov.symm.trans hcov')
  obtain rfl : item = item' := Option.some.inj (hitem.symm.trans hi')
  obtain rfl : links = links' := Except.ok.inj (hl.symm.trans hl')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨-, s₂, s₃⟩ := setting_proofGood hg hp
  exact ⟨i, real, real2, hh, hS, T, s₂, s₃,
    good_dry3P ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ p hp so hso cov hcov links hl (further, d) hg
      key₀ h0 hf R hR, hcp⟩

/-- **The record at F's proof file.** -/
theorem pageOwes_port_proof (K : ℕ)
    (hpage : pageFitB a p.chains.proof.first.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true)
    (hblocks : ∀ x ∈ (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₂ ++
        (WholeD.of a (Three.Whole.of R.1 R.2.1 R.2.2)).ds₃),
      (bsRound p.chains.proof.first.given.plan.field x.entry x.kind).b ≤ K) :
    ∃ i, readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, i) ∧
      d.copy = F.entry ∧
      PageOwes (tailPublic p.chains.proof further) (blockAt p links so.y)
        (firstStart p.chains.proof.first) F.proof i d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 p.chains.proof.first.given Params.labelFirst
        (Params.First.statement further F.entry item F.request) .inFile R.2.2 a
        p.chains.proof.first.given.plan.salt K p.chains.proof.first.given.plan.field
        p.chains.proof.first.given.cfg := by
  obtain ⟨i, real, real2, hh, hS, T, s₂, s₃, hR', hcp⟩ := port_proof_parts F id table further h p
    hp so hso cov hcov links hl item hitem d hd key₀ h0 hf R hR
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) T.first_dry
  exact ⟨i, hh, hcp, pageOwes_of_chainsP a K p.chains.proof further F.entry item F.request
    (blockAt p links so.y) T hS o₁ b₁ s₂ s₃ R hR' hok hsh hpage hsalts
    (small_port_proof F id table further h p hp so hso cov hcov links hl d hd key₀ h0 hf R hR a hok
      hsh) hblocks⟩

/-- **A proof file: the typing's six parts return, or the file shows a collision of the hash over
the realised oracle.** -/
theorem portP_returns_or_collidesBO (C : CK) (cfg : ByteArray)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.proof.first.given.plan.salt cfg
        d.r = true ∨
      ProofCollidesB (Fmt.HO Fmt.oracle) p.chains.proof further F.entry item F.request
        (blockAt p links so.y) F.proof := by
  obtain ⟨i, real, real2, hh, hS, T, s₂, s₃, hR', -⟩ := port_proof_parts F id table further h p hp
    so hso cov hcov links hl item hitem d hd key₀ h0 hf R hR
  have hsm := small_port_proof F id table further h p hp so hso cov hcov links hl d hd key₀ h0 hf
    R hR a hok hsh
  have Tr := T.toRead
  have hS' : Params.describeWith p.chains.proof.first.given Params.labelFirst
      (Params.First.statement further F.entry item F.request) .inFile d.rounds1 0 = some d.S1 := hS
  obtain ⟨o₁, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) Tr.first_dry
  obtain ⟨q, so₂, cov₂, item₂, links₂, r₀, hq, g1, g2, g3, g4, h₀, -⟩ := port_proof_reads h
  obtain rfl : p = q := Except.ok.inj (hp.symm.trans hq)
  obtain rfl : so = so₂ := Except.ok.inj (hso.symm.trans g1)
  obtain rfl : cov = cov₂ := Except.ok.inj (hcov.symm.trans g2)
  obtain rfl : item = item₂ := Option.some.inj (hitem.symm.trans g3)
  obtain rfl : links = links₂ := Except.ok.inj (hl.symm.trans g4)
  have hR2 := hR'
  unfold dryProof at hR2
  rw [Tr.first_dry] at hR2
  have hd3 : Three.dry3 (tailPublic p.chains.proof further) d.r.key (d.rounds1, d.dry) =
      some R := hR2
  obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
  rcases returns_or_collidesInB (Fmt.HO Fmt.oracle) C a p.chains.proof.first.given.plan.salt cfg
    p.chains.proof.shared.given.cfg Tr (readAt_O Tr hsm) hS' (fun e => by cases e) o₁ b₁ R₃ hd3
    hok (okAt_parts hok).fits (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm s₂.cfg rfl
    (s₃.cfg.symm.trans s₂.cfg) hB (oneSaltB_of_saltsFit hsalts) with hr | hc
  · exact Or.inl hr
  · exact Or.inr (proofCollidesB_of_record p.chains.proof further F.entry item F.request
      (blockAt p links so.y) F.proof r₀ h₀ hh Tr hS hd3 hc)

end Proof

end OnBytes.Maker.Page
