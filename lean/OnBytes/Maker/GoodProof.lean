-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/GoodProof.lean: what a good reading of a proof file (`ProofGood`,
OnBytes/TieK/Good.lean) gives for the typing of the whole file, at the reading's own values and at
plain data that are made once, from the public input. The like of OnBytes/Maker/GoodKey.lean.

The public input of a proof file holds the request and the reply. The first chain's block is made of
them (`blockAt`): so the plain data stand at one request.

  `blockAt`            the first chain's block as the program's check lays it
  `good_chainsP`       at a good reading: the flat record of the three chains (`ThreeChains`,
                       OnBytes/TieK/Chains.lean) at d's values and at that block, with the file,
                       the place behind its head, the stored copy's number, the request's item and
                       the description's equation
  `proofRefusal_of_chains`   the program's decision on the three chains as read is a yes
  `good_roundsP`       the three lists made at a fixed key that fits are d's first two and a third
                       that has the stored tables, items and openings' shapes of d's third
  `GoodPaysP`, `good_paysP`   at a good reading, from tests on the data: the data fit what was read;
                       the decision is a yes; the key; the binding tree's number of leaves
  `good_returnsP`      the typing returns at a good reading, from the tests, one hypothesis on that
                       reading (`SameTwice`), and that the three plans have one number sb of bytes
                       of a salt

To be minded. A good reading is the reading of ANY proof file that the program accepts at this
public input, whoever wrote it: see OnBytes/Maker/GoodKey.lean on `SameTwice`.

Not claimed. That the tests pass at any public input. `SameTwice` at any reading. That the data are
the same at two requests. Nothing on soundness.
All at the program's own functions: the hash is fixed, no letter.


-/
import OnBytes.Maker.GoodKey

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TieK
open _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds)

/-- The first chain's block as the program's check lays it: the links as built, each with the check
of the link of `linksOf` at its place, and the reply. -/
def blockAt (p : Model.Verify.Planned) (links : Array Model.Stages.LinkH) (y : ℕ) : Blk FirstEnd :=
  firstBlock p.chains.proof.first
    (Model.Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
      p.chains.proof.first p.X.layers.wsLay) (Model.ofNat y)

/-- The program's decision on a proof file's three chains as read is a yes, where the three runs end
well. -/
theorem proofRefusal_of_chains {c : Params.ProofChains} {table : Params.TableName}
    {block : Blk FirstEnd} {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd}
    {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd}
    {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX} {real : FirstEnd} {real2 : SharedEnd}
    (T : ThreeChains (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃' S₃ real real2) :
    proofRefusal c table block r = none := by
  rw [proofRefusal_eq, judge_of_yes "first-chain-" T.first_yes]
  exact tailRefusal_none T.shared_yes T.second_yes

section
variable (u : ProofPub) (p : Model.Verify.Planned)
  (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (so : Model.Head.StOwn)
  (hso : Model.Head.stFromCall (Model.Verify.words32 u.request) (Model.Verify.words32 u.y) p.X.T =
    .ok so)
  (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
  (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
  (d : Params.TableName × ChainsData) (hg : ProofGood u d)
include hp hso hcov hl hg

/-- **At a good reading the flat record of the three chains holds at the reading's own values.** -/
theorem good_chainsP :
    ∃ ent copy file i item real real2,
      readProofChains u.pol u.lay u.KL u.request u.y ent copy file = some d ∧ d.2.copy = copy ∧
      readProofHead p.chains.proof.first.given.plan.field file = .ok (copy, i) ∧
      Proof.requestItem u.pol u.KL u.request = some item ∧
      p.chains.proof.first.describe d.1 copy item u.request d.2.rounds1 = some d.2.S1 ∧
      ThreeChains (tailPublic p.chains.proof d.1) (blockAt p links so.y)
        (firstStart p.chains.proof.first) file i d.2.rounds1 d.2.dry d.2.S1 d.2.r d.2.seal1
        d.2.seal2 d.2.rounds2 d.2.dry2 d.2.S2 d.2.rounds3 d.2.S3 real real2 := by
  obtain ⟨F, table, e1, e2, e3, e4, e5, he, ho, hd⟩ := hg
  obtain ⟨p', so', cov', item, links', i, d', real, real2, hp', hso', hcov', hi, hl', hh, hd', hS,
    T, -, hcp⟩ := readProofChains_of F table d.1 he ho
  rw [e1, e2, e3] at hp'
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  rw [e4, e5] at hso'
  obtain rfl : so = so' := Except.ok.inj (hso.symm.trans hso')
  obtain rfl : cov = cov' := Except.ok.inj (hcov.symm.trans hcov')
  obtain rfl : links = links' := Except.ok.inj (hl.symm.trans hl')
  rw [e1, e2, e3, e4, e5] at hd'
  rw [e1, e3, e4] at hi
  rw [e4] at hS
  obtain rfl : d.2 = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  exact ⟨F.ent, F.entry, F.proof, i, item, real, real2, hd, hcp, hh, hi, hS, T⟩

variable (key₀ : TableKey) (h0 : key₀.item = 0)
  (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
  (R : Rounds × Rounds × Rounds)
  (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R)
include h0 hf hR

/-- **The three lists made at a fixed key that fits are the reading's first two, and a third with
the stored tables, the items and the openings' shapes of the reading's third.** -/
theorem good_roundsP :
    ∃ R₃, R = (d.2.rounds1, d.2.rounds2, R₃) ∧ StoredAlike d.2.rounds3 R₃ ∧
      d.2.rounds3.map (·.1.items) = R₃.map (·.1.items) ∧
      d.2.rounds3.map (fun x => x.1.opens.map (·.1)) = R₃.map (fun x => x.1.opens.map (·.1)) := by
  obtain ⟨ent, copy, file, i, item, real, real2, -, -, -, -, hS, T⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  have hS' : Params.describeWith p.chains.proof.first.given Params.labelFirst
      (Params.First.statement d.1 copy item u.request) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  obtain ⟨R₃, h3, hA, hI, hSh⟩ := dry3_alike T.toRead hS'
  obtain ⟨seeds, -, hk, hfit⟩ := tableKey_open _ _ _ _ _ _ T.key_made
  have hi : d.2.r.key.item = 0 := by rw [hk]
  have ka : TwoLaws.KeyAlike key₀ d.2.r.key :=
    keyAlike_of_fits (tailPublic p.chains.proof noTable).lin.fold.index (h0.trans hi.symm) hf hfit
  have e : dryProof p.chains.proof d.2.r.key (blockAt p links so.y) =
      some (d.2.rounds1, d.2.rounds2, R₃) := by
    unfold dryProof
    rw [T.first_dry]
    exact h3
  rw [dryProof_keyAlike ka, e] at hR
  exact ⟨R₃, (Option.some.inj hR).symm, hA, hI, hSh⟩

/-- What a good reading pays, at the plain data made of R. -/
structure GoodPaysP (a : ℕ) : Prop where
  /-- the data fit what was read, the first chain has the data's number of roots and ends in a
  seal, the key and the three views pass the tests on the words: at the reading's own three
  descriptions -/
  gives : PortGives a R d.2.r d.2.S1 d.2.S2 d.2.S3
  /-- the program's decision on the three chains as read is a yes -/
  yes : proofRefusal p.chains.proof d.1 (blockAt p links so.y) d.2.r = none
  /-- the key in the reading is the program's key of the reading's table -/
  key : tableKey p.chains.proof.shared.given.plan.field p.chains.proof.shared.given.cfg
    (tailPublic p.chains.proof noTable).lin.fold.index d.1 0 = some d.2.r.key
  /-- the binding tree as read has the parameters' number of leaves -/
  places : d.2.r.place.places = 2 ^ p.chains.proof.first.binding.logLeaves

/-- **A good reading pays**, from tests on the data. -/
theorem good_paysP (a : ℕ) (hok : okAt a (some R) = true)
    (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hb : sealBare (Three.Whole.of R.1 R.2.1 R.2.2) = true) : GoodPaysP p so links d R a := by
  obtain ⟨R₃, rfl, hA, hI, hSh⟩ :=
    good_roundsP u p hp so hso cov hcov links hl d hg key₀ h0 hf R hR
  obtain ⟨ent, copy, file, i, item, real, real2, -, -, -, -, hS, T⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  have hS' : Params.describeWith p.chains.proof.first.given Params.labelFirst
      (Params.First.statement d.1 copy item u.request) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  exact
    { gives := gives_of_chains a T hS' R₃ hA hok hsh hb
      yes := proofRefusal_of_chains T
      key := T.key_made
      places := readPlace_places T.place_read }

/-- **The typing returns at a good reading**, from tests on the data, one hypothesis on that
reading, and that the three plans have one number sb of bytes of a salt. -/
theorem good_returnsP (a sb : ℕ) (cfg : ByteArray) (C : CK) (hok : okAt a (some R) = true)
    (s₁ : p.chains.proof.first.given.plan.salt = sb)
    (s₂ : p.chains.proof.shared.given.plan.salt = sb)
    (s₃ : p.chains.proof.second.given.plan.salt = sb)
    (hT : SameTwice (Three.Whole.of R.1 R.2.1 R.2.2) d.2.r) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) sb cfg d.2.r = true := by
  obtain ⟨R₃, rfl, hA, hI, hSh⟩ :=
    good_roundsP u p hp so hso cov hcov links hl d hg key₀ h0 hf R hR
  obtain ⟨ent, copy, file, i, item, real, real2, -, -, -, -, hS, T⟩ :=
    good_chainsP u p hp so hso cov hcov links hl d hg
  have hS' : Params.describeWith p.chains.proof.first.given Params.labelFirst
      (Params.First.statement d.1 copy item u.request) .inFile d.2.rounds1 0 = some d.2.S1 := hS
  exact returns_of_read C a sb cfg T.toRead hS' (fun e => by cases e) R₃ hA hI hSh hok s₁ s₂ s₃ hT

end

end OnBytes.Maker
