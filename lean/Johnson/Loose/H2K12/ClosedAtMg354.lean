-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Loose.H2K12.ToldOfPins354
import Johnson.P5J.MgAtAll
import Johnson.P5J.LettersAt2
import Johnson.Desc.ProofFile.Law.CarryAtLaw
/-
Johnson/Loose/H2K12/ClosedAtMg354.lean: The
closed debts of the law of the proximity test (the kind K12) at sub-protocol number 354 of the proof file's first
chain (ClosedOfPins354.lean), IN THE LETTERS OF THE COMPOSED MEANING's CONSTANT (Johnson/P5J/MgAtAll.lean; LettersAt.lean).
Statements and proofs: each one call, and equations between two spellings of one term, by rfl.
  six examples: the equations by rfl, alone: the head's codes are the first chain's as read back · its list
    of members is `P5T.msAtR` at the constant's radii · the written list of segments has 25 · the table's numbers
    send at (25, 0) what the core of the numbers sends · the constant's laying is `laidAtCodes` at these codes ·
    the constant's list of seats is the list of rounds' seats' (tree, tenant)s.
  `publicLeft_atMg`, `places_atMg`, `tieAll_atMg`, `shapesListed_atMg`: the four ends.
  `rad_atMg`: the equation on the radius from what `rad_in_scope` (Johnson/HB/LLHARD/RadiiInScope.lean) concludes.
  `publicLeft_atMg₂` (with a seventh example by rfl): all six closed tests from `Written354`,
    "what the first chain's sub-protocols tell is the written list", the laying's return and that equation.
What it is not. Every premise is a premise: `Written354` (from the verifier's entry tests, by
`written354_of_pins`), the laying's return, one equation on a radius, "told", an equation on the letter d. NO
EXAMPLE BY A THEOREM. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open P5J (AtMgA fullLinks TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## The equations by rfl, alone -/

example (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : h.𝔇.cs = Zp.first.codes := rfl
example (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.𝔇.ms = P5T.msAtR Zp (P5J.At.rad Zp Z.lay) := rfl
example : fullLinks.length = 25 := rfl
example : (P5J.At.N Zp cF).sent 25 0 = (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent 25 0 := rfl
example : P5J.At.laid? Zp = K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 := rfl
example : P5J.At.seats Zp = (P5T.planSeats Zp Zp.D.1).map fun p => (p.j, p.t) := rfl

/-! ## The four ends -/

/-- **The six closed tests on the list of members, the list of places and the codes.** -/
theorem publicLeft_atMg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp)
    (d : First.FoldData) (hL : P5J.At.laid? Zp = some d.L)
    (hrad : P5J.At.rad Zp Z.lay 75 0 = e0L)
    (told : ∀ y ∈ h.𝔇.ms, seatOf y ∈ pinsOpen (P5J.At.N Zp cF) O354 fullLinks.length →
      MemberTold h.𝔇.G d.L.shapes y) :
    PublicLeft354 h.𝔇.cs h.𝔇.G d (P5J.At.N Zp cF) fullLinks.length O354 h.𝔇.ms :=
  publicLeft_of_pins W (P5J.At.rad Zp Z.lay) h.𝔇.G d (P5J.At.N Zp cF) hL hrad rfl told

/-- **The one equation on a radius**, from the equation that `rad_in_scope`
(Johnson/HB/LLHARD/RadiiInScope.lean) concludes at place 0 of sending 75, asked wherever the
maker of the rows of the sendings returns. That it returns is read off the head's own test on the radii.
-/
theorem rad_atMg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp)
    (hrows : ∀ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R → P5T.rad? R 75 0 =
      (((((Johnson.G.packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2)) :
    P5J.At.rad Zp Z.lay 75 0 = e0L := by
  obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files h.laid.pub
  have hr := h.plan.radii
  rw [show P5J.At.pseats Zp = P5T.psFull from pseats_written W, W.sends, sends_full] at hr
  obtain ⟨R, hR, eR⟩ := rows_return Zp.pol Z.lay Zp.KL 82 _ _ hr 75 (by decide) mine75_full
  show P5T.radOf ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) 75 0 = e0L
  rw [eR]
  rw [e1, e2] at hR
  exact rad_of_written R (hrows R hR)

example (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : h.𝔇.G.first.blocksInOrder = cF.blocksInOrder := rfl

/-- **All six closed tests, with "told" paid**: from the two entry tests' equations and the equation on the
rows' radius. -/
theorem publicLeft_atMg₂ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp)
    (d : First.FoldData) (hL : P5J.At.laid? Zp = some d.L)
    (hc : First.toldOf cF.blocksInOrder = First.toldCut)
    (hrows : ∀ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R → P5T.rad? R 75 0 =
      (((((Johnson.G.packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2)) :
    PublicLeft354 h.𝔇.cs h.𝔇.G d (P5J.At.N Zp cF) fullLinks.length O354 h.𝔇.ms :=
  publicLeft_of_two W (P5J.At.rad Zp Z.lay) h.𝔇.G d (P5J.At.N Zp cF) hL (rad_atMg h W hrows) rfl hc

/-- **The listed places are the list of rounds' seats.** -/
theorem places_atMg (W : Written354 Zp) (d : First.FoldData) (hL : P5J.At.laid? Zp = some d.L) :
    d.L.places = P5J.At.seats Zp :=
  places_of W d.L hL

/-- **The kind K1's four tests at every member.** -/
theorem tieAll_atMg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp) :
    ∀ y ∈ h.𝔇.ms, K1.Tie h.𝔇.cs (y.1.l.get y.2).1 :=
  fun y hy => tieAll_of W (P5J.At.rad Zp Z.lay) y hy

/-- **The list of shapes has, at a listed member's number, that member's shape.** -/
theorem shapesListed_atMg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp)
    (d : First.FoldData) (hL : P5J.At.laid? Zp = some d.L)
    (hM : d.M = K12.Door.msgsOfChain Zp.made.proof.1) :
    ∀ o y, ListedAt h.𝔇.ms d.L.places o y → d.M[o]? = some (y.1.l.get y.2).1 :=
  fun o y hy => by
    rw [hM]
    exact shapesListed_of W (P5J.At.rad Zp Z.lay) d.L hL o y hy

end H2K12

#print axioms H2K12.publicLeft_atMg
#print axioms H2K12.rad_atMg
#print axioms H2K12.publicLeft_atMg₂
#print axioms H2K12.places_atMg
#print axioms H2K12.tieAll_atMg
#print axioms H2K12.shapesListed_atMg
