-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/PlanSevenFive.lean: AT LINK 0: THE SEVEN PREMISES ON THE PLAN
(PlanSevenAt.lean beside this file) AT THE FIVE-LIST loFive (the written list's entries that have a
main row) AND THE FIVE SEATS, at the composed meaning's own letters, in the goals' scope. A joining.
A definition and two theorems. A law file; no running text imports it.
  `seatFiveAt ps`, `seatFive_at_laid`   link 0's five seats off a plan's seats; at the letters it is
                    the written seatFive (Johnson/Desc/First/Close/Law/FiveAtFull.lean).
  `plan_seven_five`   at a place of the kind K10 of link 0: PlanSeven (At.N Zp cF) (At.ms Zp
                    Z.lay) (At.arr Zp) fullLinks At.ps k p loFive (seatFiveAt (At.pseats Zp)).

Limits. PlanSevenAt.lean's. Link 0 alone.

-/
import Johnson.LPFE1R.PlanSevenAt
import Johnson.Desc.First.Close.Law.FiveAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First.Close

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- Link 0's five seats, off a plan's seats. -/
def seatFiveAt (ps : List P5T.PSeat) : Fin loFive.length → ℕ × ℕ :=
  fun i => (seatsMain loSix (seatsOfLink ps 0)).getD i.val (0, 0)

theorem seatFive_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    seatFiveAt (P5J.At.pseats Zp) = seatFive := by
  have e1 : P5J.At.pseats Zp = P5T.psFull := L.seats hW
  rw [e1]
  rfl

/-- **The seven at link 0's five-list.** -/
theorem plan_seven_five (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hrr : P5J.rowsRead Z) {k : ℕ}
    {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    (h0 : p.link.getD 0 = 0) :
    PlanSeven (P5J.At.N Zp cF) (P5J.At.ms Zp Z.lay) (P5J.At.arr Zp) P5J.fullLinks P5J.At.ps k p
      loFive (seatFiveAt (P5J.At.pseats Zp)) := by
  rw [seatFive_at_laid hW L]
  have b1 : ∀ x ∈ Sound.msOf mlFull, Sound.seatOf x ∈ P5T.N0Full.group (p.link.getD 0) →
      ∃ i : Fin loFive.length, Sound.Alike x ⟨⟨loFive, seatFive⟩, i⟩ := fun x hx hs =>
    alike_five x hx (by rw [h0] at hs; exact hs)
  have b3 : ∀ x ∈ Sound.msOf mlFull, Sound.seatOf x ∈ P5T.N0Full.group (p.link.getD 0) →
      ∃ i : Fin loFive.length,
        Johnson.G.memMain loFive i ∧ Sound.Alike x ⟨⟨loFive, seatFive⟩, i⟩ := fun x hx hs =>
    alikeMain_five x hx (by rw [h0] at hs; exact hs)
  have b4 : ∀ i : Fin loFive.length, Johnson.G.memMain loFive i →
      seatFive i ∈ P5T.N0Full.group (p.link.getD 0) := fun i hi => by
    rw [h0]
    exact grp_five i hi
  exact plan_seven_of hW L hrr hp hK (by omega) b1 hit_five b3 b4 num_inj_five seat_inj_five

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatFive_at_laid
#print axioms VerifiableInference.Desc.LinkJoin.plan_seven_five
