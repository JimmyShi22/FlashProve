-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/SeatFacts.lean: THE SEAM's PREMISES ON THE DESCRIPTION, AT THE RELEASE's OWN VALUES: members for the binders hFU | hFO (SeatFits at the shared chain's two sendings) · hlo (the first chain tells t₁ trees) · hG (the shared chain's told trees are those of K14's chainOf at the seat's tests and end) of tupleNine_sh | tupleTen_sh (Johnson/Desc/Sound/SeamAtSh.lean). Tests with code, their laws, and evaluations at the description that ProofFile.onlineDescription makes of stored public files.
  seatUB | seatOB G cs S t₁ layU layO   the plain test seatFaultAt (Johnson/Desc/SeatAt.lean) finds no fault at o_u's seat | at o_omega's and o_sp's seats (tenantSh, Sound/SharedMembers.lean).
  seatFits_U | seatFits_O   a yes gives SeatFits G cs (sendingU S rU t₁ layU layO).l (…).seat | the like at sendingO: THE BINDERS' OWN TERMS, at every radius (by seat_of_noFault).
  lookD pol lay KL   at the description of three public files: the three Bools, hlo's and hG's equations as tests, and a control for each.
  THE EVALUATIONS (#eval prints; #guard holds): the library's small example. VerifierAndGoals.storedPublicFiles: in the file of evaluations SeatFactsFull.lean (not in this library), which wants a larger stack than the default.
Limits. AN EVALUATION AT ONE VALUE IS NO THEOREM: it pays «is it empty?» alone. The description is ProofFile.onlineDescription's at the second hash function's letter secondHashFunction, as in the files of evaluations of the last chain. hG is held on the told trees' log-lengths, words and tenants as Lean's derived equality has them. No soundness is claimed.

-/
import Johnson.Second.Seam.PlanFacts
import Johnson.Desc.Sound.SharedMembers
import Johnson.Desc.Sound.PlanMemProofs
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import OnBytes.Tie.Pv.Plan.PlanLayoutSmall
import OnBytes.Tie.Pv.Plan.PlanKits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Desc.K14.Law.Fence (tenantSh sendingU sendingO)

section
variable {Xi : Type} (G : FileDescription Xi) (cs : Codes) (S : LinShape) (t₁ : ℕ) (layU layO : TreeLay)

def seatAtB (s : OracleShape) (x : ℕ × ℕ) : Bool := (seatFaultAt G cs "" s x.1 x.2).isNone

def seatUB : Bool := seatAtB G cs S.fold.u (tenantSh t₁ layU layO .oU)

def seatOB : Bool :=
  seatAtB G cs S.omega (tenantSh t₁ layU layO .oOmega) &&
    seatAtB G cs S.sharedSplit (tenantSh t₁ layU layO .oSp)


theorem seatFits_U (h : seatUB G cs S t₁ layU layO = true) (rU : ℕ) :
    SeatFits G cs (sendingU S rU t₁ layU layO).l (sendingU S rU t₁ layU layO).seat := by
  intro i
  match i with
  | ⟨0, _⟩ => exact seat_of_noFault G cs "" _ _ _ (Option.isNone_iff_eq_none.1 h)


theorem seatFits_O (h : seatOB G cs S t₁ layU layO = true) (rO rSp : ℕ) :
    SeatFits G cs (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU layO).seat := by
  unfold seatOB at h
  rw [Bool.and_eq_true] at h
  intro i
  match i with
  | ⟨0, _⟩ => exact seat_of_noFault G cs "" _ _ _ (Option.isNone_iff_eq_none.1 h.1)
  | ⟨1, _⟩ => exact seat_of_noFault G cs "" _ _ _ (Option.isNone_iff_eq_none.1 h.2)

end

/-- A row of the sheet: its name, the test, a control that must be false. -/
abbrev Line : Type := String × Bool × Bool

def lookD (pol lay KL : ByteArray) : Except String (List Line) :=
  match ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL, ProofFile.onlineDescription OnBytes.secondHashFunction pol lay KL with
  | .ok Z, .ok F =>
    match F.data "proof file", H2U.placesOfMade Z.made with
    | .ok D, .ok N =>
      let P := _root_.Desc.K14.p14Of Z.p.chains (_root_.Desc.K14.beforePointOf N)
      match (_root_.Desc.K14.withU P.S).bind (layTrees P.codes),
          layTrees P.codes (_root_.Desc.K14.withOmega P.S) with
      | some layU, some layO =>
        let told := oraclesOf F.shared.blocksInOrder
        let made := oraclesOf (_root_.Desc.K14.chainOf Z.p.chains P (K12.Seat.tests N) K12.Seat.last).blocksInOrder
        .ok
          [("factsB at the seat's own P (beforePoint := beforePointOf N)", factsB P,
              factsB { P with codes := {} }),
           ("hFU: seatUB at t₁ := D.t₁ (control: at t₁ + 1)", seatUB F P.codes P.S D.t₁ layU layO,
              seatUB F P.codes P.S (D.t₁ + 1) layU layO),
           ("hFO: seatOB at t₁ := D.t₁ (control: o_omega's shape with a row more)",
              seatOB F P.codes P.S D.t₁ layU layO,
              seatOB F P.codes { P.S with omega := { P.S.omega with mainRows := P.S.omega.mainRows + 1 } }
                D.t₁ layU layO),
           ("hlo: the first chain tells D.t₁ trees (control: D.t₁ + 1)",
              decide ((oraclesOf F.first.blocksInOrder).length = D.t₁),
              decide ((oraclesOf F.first.blocksInOrder).length = D.t₁ + 1)),
           ("hG: the shared chain's told trees are chainOf's (control: chainOf's without its first)",
              decide (told = made) && !told.isEmpty, decide (told = made.drop 1)),
           ("the plan's codes are the made proof's (cs of our last-chain pen's sheets)",
              decide (P.codes = Z.made.proof.1.codes), decide (P.codes = {}))]
      | _, _ => .error "the planner's two layouts refuse"
    | _, _ => .error "the data or the places refuse"
  | _, _ => .error "the public part or the description refuses"

def allAsDue (pol lay KL : ByteArray) : Bool :=
  match lookD pol lay KL with
  | .ok l => !l.isEmpty && l.all fun x => x.2.1 && !x.2.2
  | .error _ => false

-- THE EVALUATIONS
open OnBytes.Tie.Pv.Plan in
#eval lookD (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)
open OnBytes.Tie.Pv.Plan in
#guard allAsDue (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)
-- The full size: SeatFactsFull.lean, a sheet outside the library: under the default stack Lean's evaluator
-- overflows inside ProofFile.onlineDescription at VerifierAndGoals.storedPublicFiles (K13.whereOf's List.sum: more than 10,000 deep).

end Second.Seam

#print axioms Second.Seam.seatFits_U
#print axioms Second.Seam.seatFits_O
