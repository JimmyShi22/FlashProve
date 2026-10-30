-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/AreadyClosed.lean: the one equation (K9): FOUR CLOSED PREMISES OF
«Aready» ON ITS SECOND ROAD (the binders hC · hD · hP · hgp of aready_layersC | aready_attC |
aready_headC, Johnson/P5J/K09AreadyC.lean), WITH NO STATE IN THEM: hC · hD FROM THE HEAD; hP · hgp
AT AN OPENING OF THE MAKER ALONE (no form under the head is typed here). A joining: every step is a
call. NO SUB-PROTOCOL IMPORTS THIS FILE.
  place_of_k3At       where the lookup's own block is there at the driver's address of link m, the
                      lookup's public parameters are there: for the calls and for the digits
  bothPlaces_of_open  hC · hD at an opening of the maker: at all 25 links both places are there
  bothPlaces_at_head  the same under the head, at the constant's public record
  k4Par_of_open       hP · hgp at an opening: the parameters that k4ParAt names at link 2 g have the
                      public record's layers and the group g; and
                      k3Runs = true there
THE ROADS. The places: IM.k3_of (Johnson/IMR/K3Seat.lean) has the
lookup's block at the address; K3.theStated_is · theWhole_is · theOwn_is
(Johnson/Desc/First/Look/K3OwnIs.lean) open it: a link, a Bool and the place; the link is the
address's; the Bool is the address's by the piece's number (2 | 3 at the calls, 7 | 8 at the
digits). The parameters: IM.k4_of (Johnson/IMR/K4Seat.lean) has a member of the lot's list with the
number 2 g; LPFK9.k4ParAt_of_mem (Johnson/LPFK9R/K4Ties.lean) says that k4ParAt names that member.
WHY THE DIGITS' PLACE IS NO LAW OF THE PLAN's ENTRIES ALONE. lookAt asks there that digitsNext
answers: numbers. It is had because the description was made: the maker laid the block.
LIMITS. In scope, at the second hash function, where the maker opens. k4Par_of_open is an
implication from "k4ParAt names parameters at link 2 g": that it does is not said. Nothing on what
the places hold. No example of the head. No soundness is claimed.
-/
import Johnson.IMR.K3Seat
import Johnson.IMR.K4Seat
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.LPFK9R.K4Ties
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open ProofFile (Cl)

/-- Where the lookup's own block is there at the driver's address, so is the place. -/
theorem place_of_k3At {X : Verify.Public} {Z : ProofFile.Pub} {m : ℕ} {digits : Bool} {b : Block S Cl}
    (h : IM.k3At X Z (IM.k3Place m digits) = some b) : ∃ p, placeAt X m digits = some p := by
  obtain ⟨B₁, h1, -⟩ := VerifiableInference.Desc.K3.theStated_is _ _ _ _ _ _ _ h
  obtain ⟨b₂, h2, -⟩ := VerifiableInference.Desc.K3.theWhole_is _ _ _ _ _ _ _ h1
  obtain ⟨i, d, p, -, -, hi, hp, hpl, -⟩ := VerifiableInference.Desc.K3.theOwn_is _ _ _ _ _ _ _ h2
  obtain rfl : m = i := Option.some.inj hi
  have hd : d = digits := by
    have e : IM.k3Ix m digits + 1 = VerifiableInference.Desc.K3.pieceAt X m d := hp
    cases digits <;> cases d
    · rfl
    · exfalso
      have e' : (1 + (if m = 24 then 1 else 0)) + 1 =
          (if VerifiableInference.Desc.K3.isHead X m = true then 8 else 7) := e
      split at e' <;> split at e' <;> omega
    · exfalso
      have e' : (6 + (if m = 24 then 1 else 0)) + 1 =
          (if VerifiableInference.Desc.K3.isHead X m = true then 3 else 2) := e
      split at e' <;> split at e' <;> omega
    · rfl
  rw [hd] at hpl
  exact ⟨p, hpl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At an opening of the maker: at all 25 links both places are there.** -/
theorem bothPlaces_of_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ m < 25, ∃ pC pD, placeAt Bs.G₀.W m false = some pC ∧ placeAt Bs.G₀.W m true = some pD := by
  intro m hm
  obtain ⟨-, -, b1, -, -, e1, -⟩ := IM.k3_of hS hR O m hm false
  obtain ⟨-, -, b2, -, -, e2, -⟩ := IM.k3_of hS hR O m hm true
  obtain ⟨pC, hC⟩ := place_of_k3At e1
  obtain ⟨pD, hD⟩ := place_of_k3At e2
  exact ⟨pC, pD, hC, hD⟩

/-- **At an opening: the parameters that k4ParAt names at link 2 g.** -/
theorem k4Par_of_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∀ p4, LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 →
      p4.P = Bs.G₀.W.layers ∧ p4.g = g ∧ p4.k3Runs = true := by
  intro g hg p4 h4
  obtain ⟨-, -, x, -, -, hx, -, hl, hgx, hP, -⟩ := IM.k4_of hS hR O g hg
  rw [LPFK9.k4ParAt_of_mem hx hl] at h4
  obtain rfl := Option.some.inj h4
  exact ⟨hP, hgx, rfl⟩

end

/-- **Under the head, at the constant's public record.** -/
theorem bothPlaces_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ m < 25, ∃ pC pD, placeAt (P5J.At.X Zp) m false = some pC ∧
      placeAt (P5J.At.X Zp) m true = some pD := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀.W = P5J.At.X Zp := O.W
  rw [← e]
  exact bothPlaces_of_open h.toAtMg.scope h.toAtMg.reads O

end P1K9

#print axioms P1K9.place_of_k3At
#print axioms P1K9.bothPlaces_of_open
#print axioms P1K9.k4Par_of_open
#print axioms P1K9.bothPlaces_at_head
