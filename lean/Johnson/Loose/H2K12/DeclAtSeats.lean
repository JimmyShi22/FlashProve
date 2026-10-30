-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.FreeAtSeats
/-
Johnson/Loose/H2K12/DeclAtSeats.lean: THE PROOF FILE's DESCRIPTION's DECLARED ROUNDS, CHAIN BY
CHAIN, CUT AT THE PROXIMITY TEST's SEATS: FileDescription.roundsDeclaredByBlocks of descN o mk guardedProximityTestParts Z N c written as
«what the blocks in front declare ++ the kind's block's own rounds ++ what the blocks behind
declare». No premise: roundsDeclaredByBlocks is the flat lists' rounds in a row, by its text. For whoever holds the
description's declared rounds against a written list. Over H2K12/SitsInPure.lean | FreeAtSeats.lean
(flat_rounds). BOOK-KEEPING. NO SOUNDNESS IS CLAIMED.
NOTHING ON HIDING.
  decl_atU | decl_atO | decl_atW     the shared chain's at G_u's and at G_omega's test; the last
      chain's at the own test (in front: nothing).
  decl_atL             the first chain's, at a cut c.blocksInOrder = pre ++ firstEntry same J :: l with
      FirstJ (pL N) J: the entry's rounds are the kind's sub-protocol's.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem decl_atU (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) :
    (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.2.1 =
      (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts (pGu N) : Blk').rounds ++
          ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++
            [sharedEnd ProofFile.Cl (p14N Z N) N]).flatMap (·.rounds)) := by
  rw [← (guEntry_sits ProofFile.Cl N).rounds, ← flat_rounds, ← descN_shared o mk guardedProximityTestParts Z N c]
  rfl

theorem decl_atO (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO) (c : Chain First.S ProofFile.Cl) :
    (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.2.1 =
      (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds ++
          [sharedEnd ProofFile.Cl (p14N Z N) N].flatMap (·.rounds)) := by
  rw [← (omegaEntry_sits ProofFile.Cl nO).rounds, ← flat_rounds,
    ← shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO]
  rfl

theorem decl_atW (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) :
    (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.2.2 =
      (proximityTestKind guardedProximityTestParts (pOwn N) : Blk').rounds ++
        [secondEnd ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')].flatMap (·.rounds) := by
  have e : (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.2.2 =
      (secondPre ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')).flatMap (·.rounds) ++
        ((ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')).rounds ++
          [secondEnd ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')].flatMap (·.rounds)) := by
    rw [← flat_rounds, ← descN_second o mk guardedProximityTestParts Z N c]
    rfl
  rw [e, secondPre_rounds, (ownEntry_sits ProofFile.Cl _).rounds]
  rfl

theorem decl_atL (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (same : First.S → First.S → Bool)
    (pre l : List (Block First.S ProofFile.Cl)) (J : Block First.S ProofFile.Cl)
    (hb : c.blocksInOrder = pre ++ firstEntry same J :: l)
    (hJ : FirstJ (pL N) J) :
    (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.1 =
      pre.flatMap (·.rounds) ++ ((proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds ++ l.flatMap (·.rounds)) := by
  obtain ⟨leave, _, hs⟩ := firstJ_sits same (pL N) J hJ
  rw [← hs.rounds, ← flat_rounds, ← hb]
  rfl

end H2K.JointK

#print axioms H2K.JointK.decl_atU
#print axioms H2K.JointK.decl_atO
#print axioms H2K.JointK.decl_atW
#print axioms H2K.JointK.decl_atL
