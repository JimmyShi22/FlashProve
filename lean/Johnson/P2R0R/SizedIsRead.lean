-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2R0R/SizedIsRead.lean: AT THE PROOF FILE's PUBLIC PART, WHERE THE DESCRIPTION's TEST ON THE
PLAN ACCEPTS, THE FIRST CHAIN's CODES AND ITS SHAPE OF THE TEST ON THE COMMITTED TABLE, AS THEY ARE
READ BACK OUT OF THE PARAMETER BYTES, ARE THOSE THAT THE PLANNER HAS SIZED. STATED AND PROVED. For
the join of row 0's law of the last table (Johnson/Flat/Last/RowZeroAtZ.lean:
rowZeroOwed_atZ_tight): its premise hSZ, and the join's own equation on the codes.
The forms at the
shared table's constant's letters are in another file (Johnson/Desc/AtSeats/ShCodesOfRead.lean).
Why it is no rfl. A planner's answer holds these two things twice: as sized
(chains.made.sized.proof) and as read back (chains.proof.first | shared). K13.whereOf, and the
closed letter for the codes (P5J.At.cs), read the first chain's as read back; P2Third.lastPar and
p14Of read what is sized.
  plainChainsOf_read · plainPlanned_read · read_at_pub: the plain planner's text taken apart: the
      proof's three chains are what Params.ProofChains.read returns at the made bytes.
  shared_ok: where planOk accepts, blocksOk accepts the shared chain's flat list.
  first_ok: where blocksOk accepts a chain's flat list, the chain's first block's own test on the
      plan accepts.
  front2_at_planOk: where the planOk of the description's own term (ProofFile.fileDescBy) at the shared
      chain's own seat (sharedSeatOf ch …) accepts, so does OkD.AtC.front2 ch: it is the test on the
      plan of the shared chain's front block.
  front2_parts: two of its six clauses, as equations.
  **codes_sized** : Zp.p.chains.proof.first.codes = Zp.p.chains.made.sized.proof.codes; codes_last |
      codes_p14Of: the same at (P2Third.lastPar Zp).codes | (p14Of Zp.p.chains bp).codes.
  **lin_sized** : (K13.whereOf Zp).lin = Zp.p.chains.made.sized.proof.batch.shape; **hSZ_of**: the
      same at (P2Third.lastPar Zp).S; lin_p14Of: at (p14Of Zp.p.chains bp).S.
On what they rest. Two steps each. (a) first = shared, as read back:
Params.ProofChains.read_codes | read_lin: the reader refuses chains whose items "codes" or "the test
on the table" differ. (b) shared as read back = as sized: NO THEOREM OF THE LIBRARY SAYS IT; IT IS A
TEST OF THE DESCRIPTION's OWN planOk (readCodes | readShape). So both equations stand under two
premises: the plain road's public part returns Zp; planOk accepts: and under nothing of the goals'
scope, of the door's tests or of the written sizing (Written).
Limits. One direction: from these two premises. NO EXAMPLE IN LEAN shows them met together at any
files. Nothing on soundness or on hiding.

-/
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.ProofFile.Lot.K14Seat
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.ProofFile.Lot.LastChainFour
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.OnPlan.OkFrontC
import OnBytes.Model.VerifyRead
import OnBytes.Model.VerifyShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2R0
open OnBytes OnBytes.Model OnBytes.Model.Verify
open ProofFile.Law (bind_ok)
open VerifiableInference.Desc (Block Chain FileDescription blocksOk)
open VerifiableInference.OnPublicFiles (OkD.AtC.front2 OkD.AtC.readShape OkD.AtC.readCodes)

/-! ## The planner's reader -/

/-- From the plain planner's chainsOf's yes: the proof's three chains are read from the made
bytes. -/
theorem plainChainsOf_read {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : ProofFile.Plain.chainsOf X lay c = .ok ch) :
    Params.ProofChains.read ch.made.first ch.made.shared ch.made.second = some ch.proof := by
  unfold ProofFile.Plain.chainsOf at h
  obtain ⟨⟨links, shapes⟩, _, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨z, _, h⟩ := bind_ok h
  obtain ⟨u, _, h⟩ := bind_ok h
  obtain ⟨made, _, h⟩ := bind_ok h
  split at h
  · rename_i key link proof hk hl hp
    cases h
    exact hp
  · cases h

/-- The same from the plain planner's yes. -/
theorem plainPlanned_read {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {lay : Option ByteArray} {p : Planned} (hp : ProofFile.Plain.planned o pol KL lay = .ok p) :
    Params.ProofChains.read p.chains.made.first p.chains.made.shared p.chains.made.second =
      some p.chains.proof := by
  unfold ProofFile.Plain.planned at hp
  obtain ⟨X, _, hp⟩ := bind_ok hp
  dsimp only at hp
  obtain ⟨ch, hc, hp⟩ := bind_ok hp
  obtain ⟨b, _, hp⟩ := bind_ok hp
  cases hp
  exact plainChainsOf_read hc

/-- **The same at the proof file's public part.** -/
theorem read_at_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zp : ProofFile.Pub}
    (h : ProofFile.pubPlain o pol lay KL = .ok Zp) :
    Params.ProofChains.read Zp.p.chains.made.first Zp.p.chains.made.shared
      Zp.p.chains.made.second = some Zp.p.chains.proof :=
  plainPlanned_read (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Zp from h)))

/-! ## The shared chain's front block's test on the plan -/

/-- Where the tests on the plan accept, blocksOk accepts the shared chain's flat list. -/
theorem shared_ok {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.shared.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hb⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact hb

/-- Where blocksOk accepts a chain's flat list, the first block's own test on the plan accepts. -/
theorem first_ok {S Cl : Type} (c : Chain S Cl) (h : blocksOk c.blocksInOrder = true) :
    c.first.planOk = true := by
  obtain ⟨l, e⟩ : ∃ l, c.blocksInOrder =
      ({ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } : Block S Cl) :: l := ⟨_, rfl⟩
  unfold blocksOk at h
  rw [e, List.all_cons] at h
  have h1 := (Bool.and_eq_true_iff.1 h).1
  have h2 := (Bool.and_eq_true_iff.1 h1).1
  have h3 : (c.first.planOk && c.first.hasNoClaimsAndNothingAfter) = true := h2
  exact (Bool.and_eq_true_iff.1 h3).1

section Seat
variable {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (ch : Chains)
  (bp : List (Nat × Nat)) (tests : Desc.K14.P14 → List (Block Desc.K14.St Unit))
  (standIns : List String) (last : List (Block Desc.K14.St Unit) → Block Desc.K14.St Unit)
  (fok : Bool) (B : ProofFile.SecondSeat) (getS : σ → VerifiableInference.Desc.First.S)
  (start : ProofFile.InstPub → σ) (c : Chain σ ProofFile.Cl)

/-- **Where the description's planOk accepts, front2 accepts at the shared seat's chains.** -/
theorem front2_at_planOk
    (h : (ProofFile.fileDescBy o mk Z (Desc.K14.sharedSeatOf ch bp tests standIns last fok) B getS start
      c).planOk = true) : OkD.AtC.front2 ch = true := by
  have h1 := first_ok _ (shared_ok _ h)
  obtain ⟨x, y, e⟩ : ∃ x y : Bool,
      (ProofFile.fileDescBy o mk Z (Desc.K14.sharedSeatOf ch bp tests standIns last fok) B getS start
        c).shared.first.planOk = ((OkD.AtC.front2 ch && x) && y) := ⟨_, _, rfl⟩
  rw [e] at h1
  exact (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h1).1).1

end Seat

/-- Two of front2's six clauses, as equations: at the shared chain what is sized is what is read
back. -/
theorem front2_parts {c : Chains} (h : OkD.AtC.front2 c = true) :
    c.made.sized.proof.batch.shape = c.proof.shared.lin ∧
      c.made.sized.proof.codes = c.proof.shared.codes := by
  unfold OkD.AtC.front2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨_, _⟩, hs⟩, hc⟩, _⟩, _⟩ := h
  unfold OkD.AtC.readShape at hs
  unfold OkD.AtC.readCodes at hc
  exact ⟨of_decide_eq_true hs, of_decide_eq_true hc⟩

/-! ## The two equations -/

section Eq
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zp : ProofFile.Pub}

/-- **The first chain's codes as read back are the codes as sized.** -/
theorem codes_sized (hp : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (hf : OkD.AtC.front2 Zp.p.chains = true) :
    Zp.p.chains.proof.first.codes = Zp.p.chains.made.sized.proof.codes :=
  ((front2_parts hf).2.trans (Params.ProofChains.read_codes (read_at_pub hp))).symm

/-- At the last chain's parameters. -/
theorem codes_last (hp : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (hf : OkD.AtC.front2 Zp.p.chains = true) :
    Zp.p.chains.proof.first.codes = (P2Third.lastPar Zp).codes := codes_sized hp hf

/-- At the shared chain's parameters, whatever is named in front of the point. -/
theorem codes_p14Of (hp : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (hf : OkD.AtC.front2 Zp.p.chains = true) (bp : List (Nat × Nat)) :
    Zp.p.chains.proof.first.codes = (Desc.K14.p14Of Zp.p.chains bp).codes := codes_sized hp hf

/-- **The first chain's shape of the test on the committed table, as read back, is the shape as
sized.** -/
theorem lin_sized (hp : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (hf : OkD.AtC.front2 Zp.p.chains = true) :
    (VerifiableInference.Desc.K13.whereOf Zp).lin =
      Zp.p.chains.made.sized.proof.batch.shape := by
  show Zp.p.chains.proof.first.lin = Zp.p.chains.made.sized.proof.batch.shape
  exact ((front2_parts hf).1.trans (Params.ProofChains.read_lin (read_at_pub hp))).symm

/-- **rowZeroOwed_atZ_tight's premise hSZ.** -/
theorem hSZ_of (hp : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (hf : OkD.AtC.front2 Zp.p.chains = true) :
    (VerifiableInference.Desc.K13.whereOf Zp).lin = (P2Third.lastPar Zp).S := lin_sized hp hf

/-- At the shared chain's parameters. -/
theorem lin_p14Of (hp : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (hf : OkD.AtC.front2 Zp.p.chains = true) (bp : List (Nat × Nat)) :
    (VerifiableInference.Desc.K13.whereOf Zp).lin = (Desc.K14.p14Of Zp.p.chains bp).S :=
  lin_sized hp hf

end Eq

end P2R0

#print axioms P2R0.read_at_pub
#print axioms P2R0.front2_at_planOk
#print axioms P2R0.front2_parts
#print axioms P2R0.codes_sized
#print axioms P2R0.codes_last
#print axioms P2R0.codes_p14Of
#print axioms P2R0.lin_sized
#print axioms P2R0.hSZ_of
#print axioms P2R0.lin_p14Of
