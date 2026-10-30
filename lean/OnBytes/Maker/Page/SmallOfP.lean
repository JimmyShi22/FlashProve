-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/SmallOfP.lean: where the verifier program has said yes, the bounds that the
hash's domain asks of the proof file's three descriptions and of the proof file (`SmallThree`,
OnBytes/Maker/Page/AtOracle.lean) follow from two tests on the plain data; and the like for the key
file, at the files themselves.

Statements and proofs: OnBytes/Maker/Page/SmallOf.lean has the law at the record of a reading and
any file within the program's limit on a file's length. What the exit code's facts hold
(`K.PortYesAt`, OnBytes/K/Top.lean) has that limit for the key file and for the proof file among its
clauses.

Main names:
  `port_key_size`, `port_proof_size`: the two clauses.
  `small_port_key`: `SmallThree` at the fixed reading of F's key file and that file.
  `small_port_proof`: at the fixed reading of F's proof file and that file.
No letter stands under "there is".
Limits: the two tests (`okAt`, `shapesFit`) are not shown here; at a proof file they stand at the
data of the rounds at this request's block. Nothing on soundness.


-/
import OnBytes.Maker.Page.SmallOf
import OnBytes.Maker.Page.GoodCollidesBP

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- The key file is within the program's limit on a file's length. -/
theorem port_key_size {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) : F.key.size ≤ Shell.fileLimit := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, hz, -⟩ := h
  exact hz

/-- The proof file is within the program's limit on a file's length. -/
theorem port_proof_size {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) : F.proof.size ≤ Shell.fileLimit := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hz⟩ := h
  exact hz

/-- **A key file.** d: the fixed reading of F's key file; key₀: a fixed key at which the three
lists R were made. -/
theorem small_port_key (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    SmallThree d.S1 d.S2 d.S3 F.key := by
  have ho := port_key_chains F id table further h
  have hg : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  obtain ⟨p', j, d', real, real2, hp', -, hd', -, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  exact small_keyGood ⟨F.pol, F.lay, F.KL⟩ p hp key₀ h0 hf R hR (table, d) hg a hok hsh F.key
    T.whole.symm

/-- **A proof file.** d: the fixed reading of F's proof file. -/
theorem small_port_proof (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (so : Model.Head.StOwn)
    (hso : Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y)
      p.X.T = .ok so)
    (cov : Model.Head.Covered) (hcov : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov)
    (links : Array Model.Stages.LinkH) (hl : Model.Verify.linksOf p.X cov = .ok links)
    (d : ChainsData)
    (hd : readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
      some (further, d))
    (key₀ : TableKey) (h0 : key₀.item = 0)
    (hf : key₀.fits (tailPublic p.chains.proof noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds)
    (hR : dryProof p.chains.proof key₀ (blockAt p links so.y) = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    SmallThree d.S1 d.S2 d.S3 F.proof := by
  have he := port_entry F id table further h
  have ho := port_proof_chains F id table further h
  have hg : ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d) :=
    ⟨F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩
  obtain ⟨p', so', cov', item, links', i, d', real, real2, hp', hso', hcov', -, hl', -, hd', hS,
    T, -, -⟩ := readProofChains_of F table further he ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : so = so' := Except.ok.inj (hso.symm.trans hso')
  obtain rfl : cov = cov' := Except.ok.inj (hcov.symm.trans hcov')
  obtain rfl : links = links' := Except.ok.inj (hl.symm.trans hl')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  have Tr : ThreeRead (tailPublic p.chains.proof further) (blockAt p links so.y)
      (firstStart p.chains.proof.first) F.proof i d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
      d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 := T.toRead
  obtain ⟨-, s₂, s₃⟩ := setting_proofGood hg hp
  obtain ⟨-, b₁⟩ := proof_own_program p.X hl p.built.links p.chains.proof.first
    p.X.layers.wsLay (Model.ofNat so.y) Tr.first_dry
  have hR' : dryProof p.chains.proof d.r.key (blockAt p links so.y) = some R :=
    good_dry3P ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ p hp so hso cov hcov links hl (further, d) hg
      key₀ h0 hf R hR
  have hS' : Params.describeWith p.chains.proof.first.given Params.labelFirst
      (Params.First.statement further F.entry item F.request) .inFile d.rounds1 0 = some d.S1 := hS
  unfold dryProof at hR'
  rw [Tr.first_dry] at hR'
  have hd3 : Three.dry3 (tailPublic p.chains.proof further) d.r.key (d.rounds1, d.dry) =
      some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
  exact small_of_read a p.chains.proof.first.given.plan.salt Tr hS' b₁ R₃ hd3 hok hsh rfl
    s₂.salt.symm s₃.salt.symm F.proof (port_proof_size h)

end OnBytes.Maker.Page
