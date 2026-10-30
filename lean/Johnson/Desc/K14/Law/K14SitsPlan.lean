-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/K14SitsPlan.lean: THE KIND SITS, WITHOUT THE PREMISE "blocks P is some list":
where every block of the description's shared chain passes its test on the plan, the kind's eight
blocks are there. Theorems.

  own_pass_carried   every block of the kind's own list passes, if every block of the CARRIED
                     chain's flat list does (kin: own_pass, at the chain before it is carried:
                     Johnson/Desc/K14/Law/SplitGiven.lean).
  eight_of_pass      so blocks P is some list of eight: where it is none the chain holds one
                     stand-by block whose test on the plan is false.
  k14_sits_plan      **at what onlineDescription returns**: if every block of F's shared chain passes its
                     test on the plan: there are b1 … b8 with blocks (p14Of …) = some [b1, …, b8],
                     and the entry 1 + k of that chain's list is the k-th, carried.
What is not claimed. That a description's whole test on the plan gives the premise: it asks each
block's test: the format's text's matter. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.K14Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Seat (tests last)

theorem own_pass_carried {Cl' : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (ts : List (Block St Unit)) (lst : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ ((chainOf c P ts lst).retype (Cl' := Cl')).blocksInOrder, b.planOk = true) :
    ∀ x ∈ blocksOr P, x.planOk = true := by
  intro x hx
  have hm : bareOf (x.retype (Cl' := Cl')) ∈ ((chainOf c P ts lst).retype (Cl' := Cl')).blocksInOrder := by
    simp only [chainOf, Chain.retype, Chain.blocksInOrder, List.map_nil, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false]
    exact Or.inl (Or.inr ⟨x.retype, ⟨x, Or.inl hx, rfl⟩, rfl⟩)
  have k : ((x.planOk && x.claims.isEmpty) && (x.retype (Cl' := Cl')).hasNoClaimsAndNothingAfter) = true := h _ hm
  rw [Bool.and_eq_true, Bool.and_eq_true] at k
  exact k.1.1

theorem eight_of_pass {Cl' : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (ts : List (Block St Unit)) (lst : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ ((chainOf c P ts lst).retype (Cl' := Cl')).blocksInOrder, b.planOk = true) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  cases hb : blocks P with
  | none =>
    have key := own_pass_carried c P ts lst h
    unfold blocksOr at key
    rw [hb] at key
    have k : false = true := key _ (List.mem_singleton.2 rfl)
    cases k
  | some l =>
    unfold blocks at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hb
    obtain ⟨_, _, rfl⟩ := hb
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **The kind sits, from the tests on the plan.** -/
theorem k14_sits_plan {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hp : ∀ b ∈ F.shared.blocksInOrder, b.planOk = true) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl)
      (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z) c ∧
      blocks (p14Of Z.p.chains (beforePointOf N)) = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
      ∀ (k : Nat) (b : Block St Unit), [b1, b2, b3, b4, b5, b6, b7, b8][k]? = some b →
        (ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z)
          c).shared.blocksInOrder[1 + k]? = some (b.retype (Cl' := ProofFile.Cl)) := by
  obtain ⟨Z, N, B', c, hZ, hN, rfl⟩ := shared_seat_of_pure h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ :=
    eight_of_pass Z.p.chains (p14Of Z.p.chains (beforePointOf N)) (tests N) last hp
  exact ⟨Z, N, B', c, b1, b2, b3, b4, b5, b6, b7, b8, hZ, hN, rfl, hb, fun k b hk =>
    flat_retype_get Z.p.chains (p14Of Z.p.chains (beforePointOf N)) b1 b2 b3 b4 b5 b6 b7 b8
      (tests N) last hb k b hk⟩

end Desc.K14.Law
