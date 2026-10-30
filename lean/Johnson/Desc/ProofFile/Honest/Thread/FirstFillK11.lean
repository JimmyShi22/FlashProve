-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillK11.lean: CONDITIONAL: WHICH PROVER's SIDE STANDS AT
THE PLACE OF THE MERGE OF THE WEIGHTS' CLAIMS (kind K11) IN THE PROVER THAT onlineProverFromPublicFiles RETURNS AT THE
FILLING widerFillAt; and, under the library's head, at the place of the first chain's member number
346. Statements with their proofs.

  k11_half_wider   CONDITIONAL: A.H.first.find? (fun g => g.place ==
                   ⟨1, some (A.G.built.size - 1), 9, .K11⟩) = some (K11.headMergeHalf
                   (O.claims A.Z A.G) (I.weights A.Z) (K11.parOf A.Z A.G)): general in the three
                   public files that onlineProverFromPublicFiles reads
  k11_half_head    CONDITIONAL: **∀ blk, cF.blocksInOrder[346]? = some blk → A.H.first.find? (fun g =>
                   g.place == blk.place) = some (K11.headMergeHalf (O.claims Zp G) (I.weights Zp)
                   (K11.parOf Zp G))**

The premises. Of the first: hA: onlineProverFromPublicFiles returns A at the filling: no other (WiderKinds holds with no
premise: widerKinds, Honest/Thread/FirstFillAll.lean). Of the last: h: the library's head
(P5J.AtMgA, Johnson/P5J/MgAtAll.lean) · hG: G is the ground that the maker makes of the head's
public part · hA at the head's three files.

The kind's list holds one side: read off its text (Honest/K11/Part.lean; the place's numbers: the
library's Johnson/Desc/ProofFile/Lot/K11.lean). Where the list's authors have the like at this
filling in a file of their own, theirs is the one to keep and this one to strike. Called:
first_find_all (FirstFillAll.lean) · find_single (FindBasics.lean) · place_of_member, built_25,
ps_346 (HeadFacts.lean) · atPure_at_laid_ground (Honest/AtHeadGround.lean).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. That onlineProverFromPublicFiles returns at any files is a hypothesis; h is a hypothesis. That there
is a ground G with hG under h is not said here. That a sub-protocol stands at the place is said of
the member number 346 under h alone. Through its imports the file stands above the library's folder
ThirdParty/. The second statement: at the library's full size and the format's second hash function alone.
The statements are about lists and places. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName Chain Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

section
variable {W₀ : Type} {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE SIDE THAT IS FOUND AT THE PLACE OF THE MERGE OF THE WEIGHTS' CLAIMS.** CONDITIONAL: onlineProverFromPublicFiles
returns A at the filling. -/
theorem k11_half_wider (hA : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A) :
    A.H.first.find? (fun g => g.place == ⟨1, some (A.G.built.size - 1), 9, .K11⟩) =
      some (K11.headMergeHalf (O.claims A.Z A.G) (I.weights A.Z) (_root_.K11.parOf A.Z A.G)) := by
  refine first_find_all hA (q := (HLot.byPub I.weights (LongLots.plain o S O).k11, .K11))
    (by unfold widerPairs; exact .tail _ (.tail _ (.tail _ (.head _)))) rfl ?_
  exact find_single
    (K11.headMergeHalf (O.claims A.Z A.G) (I.weights A.Z) (_root_.K11.parOf A.Z A.G))

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {G : Ground}

include h in
/-- **THE SIDE THAT IS FOUND AT THE PLACE OF THE MEMBER NUMBER 346.** CONDITIONAL: under the
hypothesis h; G is the ground that is made of the head's public part; onlineProverFromPublicFiles returns A at the head's
three files and the filling. -/
theorem k11_half_head (hG : blankBy pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) :
    ∀ blk, cF.blocksInOrder[346]? = some blk →
      A.H.first.find? (fun g => g.place == blk.place) =
        some (K11.headMergeHalf (O.claims Zp G) (I.weights Zp) (_root_.K11.parOf Zp G)) := by
  intro blk hb
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have ep : blk.place = ⟨1, some 24, 9, .K11⟩ :=
    Option.some.inj ((place_of_member h hb).symm.trans ps_346)
  have e := k11_half_wider hA
  rw [eZ, eG, built_25 h hG] at e
  rw [ep]
  exact e

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.k11_half_wider
#print axioms ProofFile.Honest.FirstFill.k11_half_head
