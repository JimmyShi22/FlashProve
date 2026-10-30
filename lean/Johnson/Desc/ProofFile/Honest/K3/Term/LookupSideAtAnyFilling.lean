-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING, THEN AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: the honest prover's
`onlineFilling` (E2E/TheHonestProver.lean) is the base filling `onlineProverPartsInUse` read through
`tableCoins`; its return has another type; the crossing of the threads to it is not this folder's;
the equation on the lookups' lot is (Honest/K3/Term/LookupLotReadThrough.lean).
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling.
This file does not show that the maker returns at it.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupSideAtAnyFilling.lean: the honest side of the kind
"lookup" (K3): which sides the prover that `onlineProverFromPublicFiles` returns holds at places of the kind K3: first at
any filling, then at the base filling.

Terms. Honest/K3/GLOSSARY.md: filling, lot, half (side), seat, site.

What is shown.
  `lookupSideAtAnyFilling`: at every filling P and every return A of `onlineProverFromPublicFiles` at P: where a lot of P
    has, at A's public part, the halves of `theLotInst cells weights` (Honest/K3/LotInst.lean), and
    every lot of P has there either no half at a place of the kind K3 or that lot's halves: the
    search at a site's place in A's first list finds the seated row `proverSideOfLookupInChainAtOneOwner` at the fast summands
    and their reader.
  `lookupSidesAtAnyFillingAreTheLots`: under the same, every side of A's first list at a place of
    the kind K3 is one of these halves.
  `lookupPairIsOneOfTheTen`, `lookupLotIsALotOfTheBaseFilling`,
  `noOtherLotOfTheBaseFillingHasALookupsPlace`: the premises at the filling
    `onlineProverPartsInUse I o S O` (Honest/K1/Law/WSideAtFill.lean), at every index type, I, o, S, O,
    public part and ground. No premise.
  `lookupSideAtTheBaseProver`, `lookupSidesAtTheBaseProverAreTheLots`: so the two laws there, at
    every return of `onlineProverFromPublicFiles`.

Limits. All statements are implications. That `onlineProverFromPublicFiles` returns at a filling is a premise. The
statements are about lists and places: nothing on what a side plays. The filling read through
another reader (`OnlineProverParts.through`) is not named here. The side is the row that passes no table on.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LotInstFind
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.FirstFindKind
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (KindName)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

/-! ## 1 At any filling -/

/-- **At every filling: the side at a site's place.** Conditional: hA: `onlineProverFromPublicFiles` returns A at P;
hLot: L is a lot of P; hHalves: at A's public part its halves are those of `theLotInst cells
weights`; hOthers: every lot of P has there no half at a place of the kind K3, or L's halves; hsite:
s is a site of A's public part. -/
theorem lookupSideAtAnyFilling {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} (hLot : L ∈ P.lots)
    (hHalves : L.halves A.Z A.G = (theLotInst (Rc := Rc) (X := X) cells weights).halves A.Z A.G)
    (hOthers : ∀ M ∈ P.lots,
      (∀ g ∈ M.halves A.Z A.G, g.place.kind ≠ KindName.K3) ∨ M.halves A.Z A.G = L.halves A.Z A.G)
    (s : Site) (hsite : s ∈ lookSites A.Z) :
    A.H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩
        (((fastFill (Rc := Rc) (sourcesAt cells weights (reqAt A.Z) A.Z)).jobs s).asked)
        ((fastFill (Rc := Rc) (sourcesAt cells weights (reqAt A.Z) A.Z)).wit s) s.at_) :=
  atPure_first_find_kind hA hLot
    (fun M hM => (hOthers M hM).imp
      (fun hk g hg => by rw [(spot_of_site A.Z s hsite).1]; exact hk g hg) id)
    (by rw [hHalves]; exact theLotInst_find cells weights A.Z A.G s hsite)

/-- **At every filling: every side of the kind K3 is a side of the lookups' lot.** Conditional: hA;
hHalves; hOthers, as above. -/
theorem lookupSidesAtAnyFillingAreTheLots {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (cells : Tr → Cells) (weights : W₀ → Weights)
    {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X}
    (hHalves : L.halves A.Z A.G = (theLotInst (Rc := Rc) (X := X) cells weights).halves A.Z A.G)
    (hOthers : ∀ M ∈ P.lots,
      (∀ g ∈ M.halves A.Z A.G, g.place.kind ≠ KindName.K3) ∨ M.halves A.Z A.G = L.halves A.Z A.G) :
    ∀ g ∈ A.H.first, g.place.kind = KindName.K3 →
      g ∈ (theLotInst (Rc := Rc) (X := X) cells weights).halves A.Z A.G := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  intro g hg hk
  rw [eH] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1 hg
  rcases hOthers M hM with hno | hsame
  · exact absurd hk (hno g hgM)
  · rw [← hHalves, ← hsame]
    exact hgM

/-! ## 2 At the base filling -/

section
variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)

/-- K3's lot, with the kind K3, is the sixth of the ten pairs. -/
theorem lookupPairIsOneOfTheTen :
    (HLot.byPub I.weights (LongLots.plain o S O).k3, KindName.K3) ∈ widerPairs I o S O :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- **K3's lot is a lot of the base filling.** No premise. -/
theorem lookupLotIsALotOfTheBaseFilling :
    HLot.byPub I.weights (LongLots.plain o S O).k3 ∈ (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨_, lookupPairIsOneOfTheTen I o S O, rfl⟩)))

/-- **Every lot of the base filling has no half at a place of the kind K3, or K3's lot's halves.**
No premise. -/
theorem noOtherLotOfTheBaseFillingHasALookupsPlace (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ g ∈ M.halves Zq G, g.place.kind ≠ KindName.K3) ∨
      M.halves Zq G = (HLot.byPub I.weights (LongLots.plain o S O).k3 :
        HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((hTen | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at hTen
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hTen
    by_cases e : q.2 = KindName.K3
    · right
      rw [List.inj_on_of_nodup_map widerPairs_nodup hq (lookupPairIsOneOfTheTen I o S O) e]
    · left
      intro g hg
      rw [(FirstFill.widerKinds I o S O Zq G).all q hq g hg]
      exact e
  · left
    intro g hg
    rw [closeLotAt_kinds I S Zq G g hg]
    decide
  · left
    intro g hg
    rw [proxLotAt_kinds I S Zq G g hg]
    decide
  · left
    intro g hg
    have hp : g.place = ⟨1, none, 4, .K1⟩ := by
      rw [wLotAt_halves] at hg
      cases hm : OnBytes.linMessageW Zq.first.lin with
      | none =>
        rw [hm] at hg
        cases hg
      | some msg =>
        rw [hm] at hg
        obtain rfl := List.mem_singleton.1 hg
        rfl
    rw [hp]
    decide

variable {I o S O}
variable {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **At the base filling: the side at a site's place**, at the returned prover's first list: the
seated row `proverSideOfLookupInChainAtOneOwner` at the fast summands and their reader, at A.Z's sources. Conditional: hA:
`onlineProverFromPublicFiles` returns A there; hsite: s is a site of A.Z. -/
theorem lookupSideAtTheBaseProver (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    (s : Site) (hsite : s ∈ lookSites A.Z) :
    A.H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩
        (((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).jobs s).asked)
        ((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).wit s) s.at_) :=
  lookupSideAtAnyFilling hA id (I.weights A.Z) (lookupLotIsALotOfTheBaseFilling I o S O) rfl
    (noOtherLotOfTheBaseFillingHasALookupsPlace I o S O A.Z A.G) s hsite

/-- **At the base filling: every side of the kind K3 is a side of the lookups' lot.** Conditional:
hA. -/
theorem lookupSidesAtTheBaseProverAreTheLots
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind = KindName.K3 →
      g ∈ (theLotInst (Rc := IndexCommitterCoins) (X := Unit) id (I.weights A.Z)).halves A.Z A.G :=
  lookupSidesAtAnyFillingAreTheLots hA id (I.weights A.Z)
    (L := HLot.byPub I.weights (LongLots.plain o S O).k3) rfl
    (noOtherLotOfTheBaseFillingHasALookupsPlace I o S O A.Z A.G)

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupSideAtAnyFilling
#print axioms ProofFile.Honest.K3.Term.lookupSidesAtAnyFillingAreTheLots
#print axioms ProofFile.Honest.K3.Term.lookupPairIsOneOfTheTen
#print axioms ProofFile.Honest.K3.Term.lookupLotIsALotOfTheBaseFilling
#print axioms ProofFile.Honest.K3.Term.noOtherLotOfTheBaseFillingHasALookupsPlace
#print axioms ProofFile.Honest.K3.Term.lookupSideAtTheBaseProver
#print axioms ProofFile.Honest.K3.Term.lookupSidesAtTheBaseProverAreTheLots
