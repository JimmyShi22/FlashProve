-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/SeatsAtDesc.lean: THE SEATS' TIES FOR THE SUB-PROTOCOL K4 AND FOR THE LOOKUP
ARGUMENT ON THE CALLS, AT THE FIRST CHAIN (a Fiat–Shamir hash chain) OF THE IOP AS WRITTEN IN LEAN
FOR THE PROOF FILE, AT ONE LINK FOR BOTH: at each of the twelve layers' links 2 g of the chain c of
ONE opening of that IOP: the sentence StatesAt at K4's two runs of claims, at every state of the
verifier, and the four premises on the lookup argument's two runs of the structure ObjAsks.
Statements and proofs: a join of Johnson/Road/K4/Riders/SeatsTies.lean with two laws on the IOP as
written in Lean: K4Of at an opening (k4Of_of_open, Johnson/Road/K4/K04Sits.lean) and IM.k3_of
(Johnson/IMR/K3Seat.lean).

WHY ONE OPENING. Each of the two laws, told from the value that the IOP's make returns, says "there
is a chain c". Both are also told at the letters of an opening (IM.Open): so the two are taken at
one opening, and the link is one term: no step "the two chains are one" is owed.

  `plan_lines`: where the public parameters have p4 = true and NGr = 12: at g < 12 the lookup
    argument on the calls of link 2 g stands at piece 2, and no caller's readers are handed there.
  **`seats_at_open`**: at an opening, in the goals' scope, at g < 12: the two equations come off the
    Meaning.scope_plans (Johnson/Goal/Meaning/PlanShapes.lean) at the opening's own public
    parameters.
  **`seats_at_desc`**: where the IOP's make returns: there is an opening with all twelve.
No new argument.
**Limits.** PREMISES: the goals' scope (VerifierAndGoals.InScope, VerifierAndGoals.readFiles) · THE MAKE OF THE IOP AS
WRITTEN IN LEAN RETURNS (ProofFile.onlineDescription … = .ok F), at our second, non-standard hash (built on
BLAKE2b's compression function), OnBytes.secondHashFunction: shown by no theorem. The two laws on that IOP are
other files' work, called as they stand. It speaks of that IOP's chain: not of the text that
verify() runs. THAT THE READERS WHICH A TABLE's MEANING TAKES AT SEGMENT 2 g ARE K9.readersOfLink AT
THE VERY LINK Lk FOUND HERE is said by nobody: one tie for whoever composes the meaning. Nothing on
soundness. K04_law, the law of the sub-protocol K4 itself, IS NOT PROVED.


-/
import Johnson.Road.K4.Riders.SeatsTies
import Johnson.Road.K4.K04Sits
import Johnson.IMR.K3Seat
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Road.K4.InT (StatesAt)
open VerifiableInference.Desc (Claim Block Link FileDescription K9.statesOfLink K3.pieceAt K3.isHead)
open VerifiableInference.Desc.First (S hearsReply)

/-- Two lines on the plan, at a layers' link 2 g. -/
theorem plan_lines {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {g : ℕ} (hg : g < 12) :
    2 = K3.pieceAt X (2 * g) false ∧ K3Lot.readersAt X (2 * g) = none := by
  have hh : K3.isHead X (2 * g) = false := by
    unfold K3.isHead
    rw [h4, hN, if_pos rfl]
    exact beq_false_of_ne (by omega)
  constructor
  · unfold K3.pieceAt
    rw [hh]
    rfl
  · unfold K3Lot.readersAt
    dsimp only
    rw [hh, h4, if_pos rfl]
    simp

/-- What is said of link 2 g of a first chain c. -/
def SeatsAt (c : VerifiableInference.Desc.Chain S Claim) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (g : ℕ) :
    Prop :=
  ∃ (Lk : Link S Claim) (x : Bool × Par), c.links[2 * g]? = some Lk ∧
    x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none ∧ x.2.link = 2 * g ∧
    (∀ s, StatesAt (K9.statesOfLink Lk) 2 { x.2 with k3Runs := true } "front" s ∧
      StatesAt (K9.statesOfLink Lk) 2 { x.2 with k3Runs := true } "back" s) ∧
    ∃ runO runG,
      (K9.statesOfLink Lk 1).find? (fun r => r.1 == "objects") = some ("objects", runO) ∧
      ObjRun runO ∧
      (K9.statesOfLink Lk 1).find? (fun r => r.1 == "guests") = some ("guests", runG) ∧
      GuestRun runG

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **At an opening of the IOP as written in Lean**, in the goals' scope, at g < 12. -/
theorem seats_at_open {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    SeatsAt c Z Bs.G₀ g := by
  obtain ⟨k4, kN, _⟩ := Meaning.scope_plans hS hR O.public
  obtain ⟨hp, hr⟩ := plan_lines k4 kN hg
  obtain ⟨Lk, b, x, e1, e2, e3, e4, e5, _⟩ := k4Of_of_open hS hR O g hg
  obtain ⟨Lk', b1, b1', f1, f2, f3, f4⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have hLk : Lk' = Lk := Option.some.inj (f1.symm.trans e1)
  rw [hLk] at f2
  have hix : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  rw [hix] at f2
  have he4 : SeatedAs hearsReply b (ProofFile.k4Block x) b.name (k4PlaceAt g) := e4
  have hf4 : SeatedAs hearsReply b1 b1' b1.name (IM.k3Place (2 * g) false) := f4
  refine ⟨Lk, x, e1, e3, e5, fun s => st_at_seat e2 he4 s, ?_⟩
  refine runs_at_seat (i := 2 * g) f2 hf4 f3 rfl ?_ hr
  show IM.k3Ix (2 * g) false + 1 = _
  rw [hix]
  exact hp

/-- **Where the IOP's make returns**: there is an opening, with all twelve layers' links. -/
theorem seats_at_desc (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok F) :
    ∃ Z Bs base c A B, IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B ∧
      ∀ g < 12, SeatsAt c Z Bs.G₀ g := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨Z, Bs, base, c, A, B, O, fun g hg => seats_at_open hS hR O hg⟩

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.plan_lines
#print axioms OnBytes.Road.K4.Riders.seats_at_open
#print axioms OnBytes.Road.K4.Riders.seats_at_desc
