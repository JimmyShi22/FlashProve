-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/LaterChains.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): THE KIND DOES NOT STAND IN THE SHARED CHAIN OR IN THE LAST CHAIN: neither a
member of the online description there nor a side of a prover that the maker returns. The third and
fourth clause of StandsAtOneBorder, and the clauses on the two later chains of
SideIsTheHeadRowAtTheBase and SideIsTheHeadRowAtTheFilling (Honest/K6/Term/Statements.lean).

WHAT IT IS NOT. Facts on labels: a place's kind is a label, and nothing is said on what a member or
a side does. Nothing on the first chain. The library's hypothesis on the first chain (P5J.AtMgA: the
full size and the format's second hash function alone) and "the maker returns" are premises; the maker is
onlineProverFromPublicFiles (Honest/AtPure.lean). Nothing on soundness, completeness or what a proof hides.

WHAT IT IS. No definition; three theorems.

  laterChainsLackTheKind   under the hypothesis: no member of the description's shared chain and no
                           member of its last chain is of the kind K6
  sidesLackAKind           general, the kind a letter: where no side of a list strays from a list of
                           members, and no member is of the kind, no side is
  laterSidesLackTheKind    under the hypothesis, at any return of the maker, the filling a letter:
                           no side of the prover's shared chain or last chain is of the kind

CALLED. ProofFile.Law.shared_kinds and second_kinds (Johnson/Desc/ProofFile/Law/LaterKinds.lean): the
shared chain has the kinds frame, K14, K1 and K12 alone, the last chain frame, K14 and K12 alone;
they ask how the two chains were made, which the hypothesis holds (its field laid.opened).
atPure_tests (Honest/AtPureLaw.lean): the maker returns only where no side strays. atPure_at_laid
(Honest/AtHead.lean): the maker's description is the hypothesis's. any_of_strays
(Honest/Thread/Rows.lean).
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.Thread.Rows
import Johnson.Desc.ProofFile.Law.LaterKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Block Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the library's hypothesis on the first chain, no member of the online description's
shared chain and no member of its last chain is of the kind K6.** -/
theorem laterChainsLackTheKind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∀ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, member.place.kind ≠ .K6) ∧
      (∀ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, member.place.kind ≠ .K6) := by
  obtain ⟨Bs, base, opened⟩ := h.laid.opened
  refine ⟨fun member isMember kind => ?_, fun member isMember kind => ?_⟩
  · have kinds : ProofFile.Law.sharedKind member.place.kind :=
      ProofFile.Law.shared_kinds opened.shared (γ := Cl) member isMember
    rw [kind] at kinds
    rcases kinds with k | k | k | k <;> cases k
  · have kinds : ProofFile.Law.secondKind member.place.kind :=
      ProofFile.Law.second_kinds opened.second (γ := Cl) member isMember
    rw [kind] at kinds
    rcases kinds with k | k | k <;> cases k

/-- General; the kind is a letter. **Where no side strays from the list of members and no member is
of the kind, no side is of the kind.** -/
theorem sidesLackAKind {S C V W Y : Type} {members : List (Block S C)}
    {sides : List (Placed V W Y)} {kind : KindName}
    (noStray : (strays members sides).isEmpty = true)
    (membersLack : ∀ member ∈ members, member.place.kind ≠ kind) :
    ∀ side ∈ sides, side.place.kind ≠ kind := by
  intro side isSide
  obtain ⟨member, isMember, samePlace⟩ :=
    List.any_eq_true.1 (any_of_strays (List.isEmpty_iff.1 noStray) side isSide)
  rw [← beq_iff_eq.1 samePlace]
  exact membersLack member isMember

/-- **Under the same hypothesis, at any return of the maker: no side of the prover's shared chain
and no side of its last chain is of the kind K6.** The filling is a letter. Two premises: the
hypothesis and "the maker returns". -/
theorem laterSidesLackTheKind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (∀ side ∈ A.H.shared, side.place.kind ≠ .K6) ∧
      (∀ side ∈ A.H.second, side.place.kind ≠ .K6) := by
  obtain ⟨-, -, noStrayShared, noStrayLast, -⟩ := atPure_tests hA
  rw [(atPure_at_laid h.laid hA).2] at noStrayShared noStrayLast
  obtain ⟨sharedLacks, lastLacks⟩ := laterChainsLackTheKind h
  exact ⟨sidesLackAKind noStrayShared sharedLacks, sidesLackAKind noStrayLast lastLacks⟩

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.laterChainsLackTheKind
#print axioms ProofFile.Honest.K6.Term.sidesLackAKind
#print axioms ProofFile.Honest.K6.Term.laterSidesLackTheKind
