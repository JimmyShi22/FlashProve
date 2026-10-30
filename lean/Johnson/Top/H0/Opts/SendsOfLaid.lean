-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SendsOfLaid.lean: THE LIBRARY's LIST OF THE SEVEN CHAINS' SENDINGS AT THE THREE
PUBLIC FILES (Johnson.G.sendsOf) HAS, AS ITS FIFTH MEMBER, THE FIRST PROOF CHAIN's SENDINGS OF THE
PROOF FILE's PUBLIC PART (Zp.made.proof.1): where the test protocolDataWellFormed accepts. NO PIN. NO SUB-PROTOCOL
IMPORTS THIS FILE.
WHY. The second reading of the three public files (sendRowsOf, Johnson/G/LinkSig.lean) goes by
sendsOf, which plans at the files' own digest; the public part Zp is made at a constant in the
digest's place, by a copy of the maker at a letter for the second hash function. Whoever compares
the rows with the plan's tenants needs the two lists to be one.
  packMade_inv    what packMade accepts is a list of seven, and the fifth is the record's first
                  proof chain
  sends_of_made   where the maker with the digest as an argument returns m at the files' own digest:
                  sendsOf returns seven, the fifth m.proof.1
  sends_of_laid   THE STATEMENT
CALLED: ProofFile.Law.pub_madeOfAtO (Johnson/Desc/ProofFile/Law/PlainIsMade.lean) · madeOfAtO_older
(Johnson/Desc/Ok/PlanWritten/MadeAtLaws.lean) · madeOfAt_at · madeOfAt_planned
(Johnson/Desc/Ok/NumberPrices/AtDigest.lean: the sendings do not hang on the digest) ·
planned_of_live (Johnson/Goal/Reads/SevenAtLive.lean: the chains' strings are short).
LIMITS. At the format's own second hash function. Nothing on the other six members.
No soundness is claimed.
-/
import Johnson.Desc.ProofFile.Law.PlainIsMade
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import Johnson.Desc.Ok.PlanWritten.MadeAtLaws
import Johnson.Desc.Ok.NumberPrices.AtDigest
import Johnson.Goal.Reads.SevenAtLive
import Johnson.Goal.Tie.ReadThruHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open Johnson.G Johnson.G.OfPlan
open OnBytes.Params (exc_bind)
open OnBytes.Model.Verify (planned configuration)
open OnBytes.Tie (plannedAt exc_step)
open VerifiableInference.Number (sendsFrom packMade madeOfAt madeOfAt_at madeOfAt_planned)
open VerifiableInference.PlanWritten (madeOfAtO_older plannedAtO_older)
open VerifiableInference.Desc (fixedConfigurationDigest theCfg_size)

theorem packMade_inv {p : OnBytes.Model.Verify.Planned} {s : List ChainSends} {m : Made} :
    packMade p s = .ok m → ∃ k0 k1 k2 e p1 p2, s = [k0, k1, k2, e, m.proof.1, p1, p2] := by
  unfold packMade
  split
  · intro h
    obtain rfl := Except.ok.inj h
    exact ⟨_, _, _, _, _, _, rfl⟩
  · intro h
    cases h

theorem sends_of_made {pol lay KL : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL (configuration pol lay KL) = .ok m) :
    ∃ k0 k1 k2 e p1 p2, sendsOf pol lay KL = .ok [k0, k1, k2, e, m.proof.1, p1, p2] := by
  unfold madeOfAt at h
  obtain ⟨p, hp, h⟩ := exc_bind h
  obtain ⟨s, hs, h⟩ := exc_bind h
  have pe : planned pol KL (some lay) = .ok p := hp
  have se : sendsOf pol lay KL = .ok s := by
    rw [sendsOf_eq]
    exact (exc_step _ pe).trans hs
  obtain ⟨k0, k1, k2, e, p1, p2, rfl⟩ := packMade_inv h
  exact ⟨k0, k1, k2, e, p1, p2, se⟩

/-- **The fifth of the seven is the public part's own first proof chain.** -/
theorem sends_of_laid {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub}
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hp : ProofFile.pubPlain OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp) :
    ∃ k0 k1 k2 e p1 p2,
      sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] := by
  obtain ⟨m, hm, hb⟩ := ProofFile.Law.pub_madeOfAtO
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp from hp)
  rw [madeOfAtO_older] at hm
  obtain ⟨p, hpl, hbytes⟩ := FlashProve.planned_of_live OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) hl
  have hpl' : plannedAt Z.pol Z.KL (some Z.lay) fixedConfigurationDigest = .ok p := by
    rw [← plannedAtO_older]
    exact hpl
  have ep : m.p = p := Except.ok.inj ((madeOfAt_planned hm).symm.trans hpl')
  have h2 := madeOfAt_at (c' := configuration Z.pol Z.lay Z.KL) theCfg_size
    (OnBytes.Params.configurationDigest_size _) (by rw [ep]; exact hbytes) hm
  obtain ⟨k0, k1, k2, e, p1, p2, hs⟩ := sends_of_made h2
  refine ⟨k0, k1, k2, e, p1, p2, ?_⟩
  rw [← hb]
  exact hs

end P1Opts

#print axioms P1Opts.packMade_inv
#print axioms P1Opts.sends_of_made
#print axioms P1Opts.sends_of_laid
