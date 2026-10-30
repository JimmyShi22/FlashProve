-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/PortChains.lean: from `K.PortYesAt` to the three chains of the key file and of the
proof file, each as one flat record.

`K.PortYesAt F id table further` (OnBytes/K/Top.lean) holds the yes of `Key.check` on the key file
and of `Proof.check` on the proof file, at the chains that the planner makes from the three public
files and at the model's own links. OnBytes/TieK/Chains.lean opens such a yes into the record
`ThreeChains`. OnBytes/TieK/ChainsRead.lean says what the readers of the chains' parameter bytes
have established of the planner's chains. This file puts the three together.

Main names:
  `KeyOpened F table`: the planner's chains, their facts (one digest of the public files in all
    chains; the chains' parameter bytes as read), the key file's size bound, the two tests on the
    one-time chain's public values, and the key file's three chains.
  `ProofOpened F further`: the like for the proof file. The first chain's block is the model's own:
    its links are made of the plan, which comes from the public files alone, and of the request's
    and the reply's words. Every value stands with the equation that makes it from the files.
  `port_key_chains`, `port_proof_chains`: `K.PortYesAt` gives both.
Limits: it claims nothing on soundness. The program does not import this file.

-/
import OnBytes.TieK.PortCommon
import OnBytes.TieK.Chains
import OnBytes.TieK.ChainsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof OnBytes.Tie

/-- The key file's three chains as the program has read and judged them, at the planner's chains.
table: what the program keeps of the key's table. -/
def KeyOpened (F : K.Files) (table : Params.TableName) : Prop :=
  ∃ p j rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2,
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
    Tie.SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]) ∧
    KeyChainsFacts (p.chains.bytes .keyOneTime) (p.chains.bytes .keyShared)
      (p.chains.bytes .keySecond) p.chains.key ∧
    F.key.size ≤ Shell.fileLimit ∧
    (p.chains.key.oneTime.given.plan.field != .two) = false ∧
    (!Key.admitted p.chains.key.oneTime) = false ∧
    Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
      .ok (table, j) ∧
    p.chains.key.oneTime.describe table rounds1 = some S1 ∧
    ThreeChains (Key.tailPublic p.chains.key table) (Key.oneTime p.chains.key.oneTime)
      (Key.startOf p.chains.key.oneTime) F.key j rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2
      rounds3 S3 real real2

/-- The proof file's three chains as the program has read and judged them, at the planner's chains.
further: the table of the stored copy on which the proof was made, as the caller holds it. -/
def ProofOpened (F : K.Files) (further : Params.TableName) : Prop :=
  ∃ p so cov item links i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2,
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
    Tie.SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]) ∧
    ProofChainsFacts (p.chains.bytes .proofFirst) (p.chains.bytes .proofShared)
      (p.chains.bytes .proofSecond) p.chains.proof ∧
    F.proof.size ≤ Shell.fileLimit ∧
    (p.chains.proof.first.given.plan.field != .two ||
      p.chains.proof.first.given.cfg == Fmt.zero32) = false ∧
    Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
      .ok so ∧
    Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
    Proof.requestItem F.pol F.KL F.request = some item ∧
    Model.Verify.linksOf p.X cov = .ok links ∧
    readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, i) ∧
    p.chains.proof.first.describe further F.entry item F.request rounds1 = some S1 ∧
    ThreeChains (tailPublic p.chains.proof further)
      (firstBlock p.chains.proof.first
        (Model.Stages.runLinksH
          (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
          p.chains.proof.first p.X.layers.wsLay) (Model.ofNat so.y))
      (firstStart p.chains.proof.first) F.proof i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2
      rounds3 S3 real real2

/-- **The key file's three chains, from `K.PortYesAt`.** -/
theorem port_key_chains (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) : KeyOpened F table := by
  obtain ⟨_, p, _, -, -, -, -, -, -, -, -, hz, -, hp, -, -, hk, -, -, -, hs, -⟩ := h
  obtain ⟨j, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2, f1, f2,
    h1, h2, h3⟩ := key_check_chains _ _ _ hk
  exact ⟨p, j, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2, hp,
    hs, (planned_chains_open hp).1, hz, f1, f2, h1, h2, h3⟩

/-- **The proof file's three chains, from `K.PortYesAt`.** -/
theorem port_proof_chains (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) : ProofOpened F further := by
  obtain ⟨p, so, cov, item, links, hp, h1, h2, h3, h4, hc, -⟩ := port_common h
  obtain ⟨_, p', _, -, -, -, -, -, -, -, -, -, -, hp', -, -, -, -, -, -, hs, -, -, -, hb⟩ := h
  have ep : p' = p := Except.ok.inj (hp'.symm.trans hp)
  subst ep
  obtain ⟨i, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2, g1, g0,
    g2, g3⟩ := proof_check_chains _ _ _ _ _ _ _ _ hc
  exact ⟨p', so, cov, item, links, i, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2,
    rounds3, S3, real, real2, hp, hs, (planned_chains_open hp).2.2, hb.2.2.2.2.2, g0, h1, h2, h3,
    h4, g1, g2, g3⟩

end OnBytes.TieK
