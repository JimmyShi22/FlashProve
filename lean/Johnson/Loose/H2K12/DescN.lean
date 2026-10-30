-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.LaterSeatsN
import Johnson.Desc.K12.Law.SitsOnly
import Johnson.Desc.ProofFile.Frames1
/-
Johnson/Loose/H2K12/DescN.lean: OVER THE
LIBRARY PATHS (Johnson/Desc/ProofFile/…): descN: A NAME FOR OTHER
FILES' TERMS, NOT A SECOND TEXT: the proof file's description as ProofFile's fileDescBy makes it, at a
first chain c and at the two later chains' files' own seats at the places' numbers N
(LaterSeatsN.lean: sharedN calls Desc.K14.sharedSeatOf; secondN is P2Third.secondSeatOf with two
fields turned): AND WHAT HOLDS OF ITS TWO LATER CHAINS. CUT OUT OF SitsInPure.lean,
statements to the letter, so that the part which opens ProofFile's texts on the first
chain can be carried apart. NOTHING HERE UNFOLDS ProofFile's Pure · FillCore · chainBy: of fileDescBy it
reads the two fields «shared» and «second» by unfolding. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  descN o mk X Z N c   the description.
  descN_shared | descN_second · descN_only     the two later flat lists, written out
      (Johnson/Desc/K12/Law/SitsChains.lean's shared_cut | second_cut); no other entry of them bears
      the kind K12 (SitsOnly.lean).
  descN_atU | atO | atW     (descN …).runEnd's yes ⇒ AtCut at the written cut.
WHAT IS NOT HERE: the first chain (descN_atL: H2K12/FirstSeatForm.lean · pureZ_sits:
H2K12/SitsInPure.lean) · that onlineDescription returns a descN (k12_sits: H2K12/SitsAtDescPure.lean).
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)
open H2K.Pub (Letters)

/-- The description at a first chain c and the two later chains' files' seats at N. -/
def descN (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (X : Parts T12) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) : FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy o mk Z (sharedN Z N) (secondN X Z N) (fun s => s) (ProofFile.startS Z) c

/-- The shared chain's flat list of the description, written out. -/
theorem descN_shared (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (X : Parts T12) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (c : Chain First.S ProofFile.Cl) :
    (descN o mk X Z N c).shared.blocksInOrder =
      sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ guEntry ProofFile.Cl N ::
        ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++ [sharedEnd ProofFile.Cl (p14N Z N) N]) :=
  shared_cut ProofFile.Cl _ _ N

/-- The last chain's flat list of the description, written out. -/
theorem descN_second (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (X : Parts T12) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (c : Chain First.S ProofFile.Cl) :
    (descN o mk X Z N c).second.blocksInOrder =
      secondPre ProofFile.Cl (p₁₄N Z) (proximityTestKind X (pOwn N) : Blk') ++
        ownEntry ProofFile.Cl (proximityTestKind X (pOwn N) : Blk') ::
          [secondEnd ProofFile.Cl (p₁₄N Z) (proximityTestKind X (pOwn N) : Blk')] :=
  second_cut ProofFile.Cl _ _

/-- On the two later chains no other entry bears the kind K12. -/
theorem descN_only (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (X : Parts T12) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (c : Chain First.S ProofFile.Cl) :
    (∀ E ∈ (descN o mk X Z N c).shared.blocksInOrder, E.place.kind = .K12 →
      E = guEntry ProofFile.Cl N ∨ ∃ nO, N.O = some nO ∧ E = omegaEntry ProofFile.Cl nO) ∧
    ∀ E ∈ (descN o mk X Z N c).second.blocksInOrder, E.place.kind = .K12 →
      E = ownEntry ProofFile.Cl (proximityTestKind X (pOwn N) : Blk') :=
  ⟨shared_only ProofFile.Cl _ _ N, second_only ProofFile.Cl _ _⟩

/-- AT THE SHARED CHAIN's TEST ON G_u: at the written cut (descN_shared). -/
theorem descN_atU (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View)
    (e : (descN o mk guardedProximityTestParts Z N c).S₁ × (descN o mk guardedProximityTestParts Z N c).S₂ ×
      (descN o mk guardedProximityTestParts Z N c).S₃)
    (h : (descN o mk guardedProximityTestParts Z N c).runEnd x v₁ v₂ v₃ = .ok e) :
    AtCut X (pGu N) 0 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N)
      ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++ [sharedEnd ProofFile.Cl (p14N Z N) N])
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave
      ((descN o mk guardedProximityTestParts Z N c).start₂ ((descN o mk guardedProximityTestParts Z N c).pub x)) e.2.1 v₂ :=
  run_atCut2 X (pGu N) (descN o mk guardedProximityTestParts Z N c) x v₁ v₂ v₃ e h _ _ _ _ _
    (descN_shared o mk guardedProximityTestParts Z N c) (guEntry_sits ProofFile.Cl N)

/-- AT THE SHARED CHAIN's TEST ON G_omega, where the plan has one: at the written cut. -/
theorem descN_atO (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View)
    (e : (descN o mk guardedProximityTestParts Z N c).S₁ × (descN o mk guardedProximityTestParts Z N c).S₂ ×
      (descN o mk guardedProximityTestParts Z N c).S₃)
    (h : (descN o mk guardedProximityTestParts Z N c).runEnd x v₁ v₂ v₃ = .ok e) :
    AtCut X (pGomega nO) 0 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N])
      (omegaEntry ProofFile.Cl nO) [sharedEnd ProofFile.Cl (p14N Z N) N]
      (Seat.enter (·.gOmega) fun _ => none) Seat.leave
      ((descN o mk guardedProximityTestParts Z N c).start₂ ((descN o mk guardedProximityTestParts Z N c).pub x)) e.2.1 v₂ :=
  run_atCut2 X (pGomega nO) (descN o mk guardedProximityTestParts Z N c) x v₁ v₂ v₃ e h _ _ _ _ _
    (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO) (omegaEntry_sits ProofFile.Cl nO)

/-- AT THE LAST CHAIN's OWN TEST: at the written cut (descN_second). -/
theorem descN_atW (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View)
    (e : (descN o mk guardedProximityTestParts Z N c).S₁ × (descN o mk guardedProximityTestParts Z N c).S₂ ×
      (descN o mk guardedProximityTestParts Z N c).S₃)
    (h : (descN o mk guardedProximityTestParts Z N c).runEnd x v₁ v₂ v₃ = .ok e) :
    ∃ s₃, (descN o mk guardedProximityTestParts Z N c).start₃ ((descN o mk guardedProximityTestParts Z N c).pub x) e.1 e.2.1 = .ok s₃
      ∧
      AtCut X (pOwn N) (descN o mk guardedProximityTestParts Z N c).lastChainFirstTreeNumber
        (secondPre ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk'))
        (ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk'))
        [secondEnd ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')] enterOwn leaveOwn s₃ e.2.2 v₃ :=
  run_atCut3 X (pOwn N) (descN o mk guardedProximityTestParts Z N c) x v₁ v₂ v₃ e h _ _ _ _ _
    (descN_second o mk guardedProximityTestParts Z N c) (ownEntry_sits ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk'))

end H2K.JointK

#print axioms H2K.JointK.descN_shared
#print axioms H2K.JointK.descN_second
#print axioms H2K.JointK.descN_only
#print axioms H2K.JointK.descN_atU
#print axioms H2K.JointK.descN_atO
#print axioms H2K.JointK.descN_atW
