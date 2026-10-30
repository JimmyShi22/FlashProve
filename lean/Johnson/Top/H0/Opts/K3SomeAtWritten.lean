-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/K3SomeAtWritten.lean: THE TWO TESTS callsSomeB AND digSomeB OF
P5J.At.k3SeatsB ACCEPT AT ALL WRITTEN SEGMENTS, UNDER «live · laid», THE ONE NAMED CONDITION ON THE
ROWS, AND TWO EQUATIONS «the plan's part is the written one». THE END PIECE: other files
meet here. NO BLOCK IMPORTS THIS FILE.
  hSh_laid            live · laid ⟹ at whatever rows the maker of the rows returns:
                      P1Opts.RowsShaped at the plan's seats. NO PIN, NO SCOPE. By sends_of_laid
                      (Opts/SendsOfLaid.lean) · first_is_fifth (Opts/SendsKeys.lean) ·
                      rows_at_plan (Opts/RowsAtPlan.lean) · rowsShaped_of (Opts/RowsShapedOf.lean)
  k3Some_at_written   live · laid · rowsRead Z · hS : At.shape Zp = proofSizedFull.request · hp :
                      At.pseats Zp = P5T.psFull ⟹ ((List.range At.links.length).all fun l =>
                      At.callsSomeB Zp Z.lay l && At.digSomeB Zp Z.lay l) = true: the premise h2
                      of k3SeatsB_of_two (Johnson/HB/LLHARD/K3SeatsFour.lean), to
                      the letter. By k3Some_of_rows (Opts/SomeAtName.lean) · a1_at_written |
                      a2_at_written (Opts/SomeSeatsWritten.lean: by Lean's kernel at the written
                      values, with two negative tests)
WHY TWO EQUATIONS AND NOT THE PIN. hS and hp are what k3Four_at_name (K3SeatsFour.lean) draws out
of «in scope · laid · the test that holds the made plan to the written one accepts»
(first_written_in_scope · seats_in_scope). The files with these two laws are not imported here
(Johnson/Goal/Numbers/MadeInScope.lean · Johnson/P5T/PlanSeatsTie.lean):
the last step is two lines, and it is not taken in this file.
THE PREMISES BEYOND «live · laid», BY NAME: hrr : P5J.rowsRead Z (one named test
on the three public files) · hS · hp. NONE IS SHOWN TO HOLD AT ANY FILES HERE. verify() calls
rowsRead's test by no name of these files. No soundness is claimed.
-/
import Johnson.Top.H0.Opts.SomeAtName
import Johnson.Top.H0.Opts.RowsShapedOf
import Johnson.Top.H0.Opts.RowsAtPlan
import Johnson.Top.H0.Opts.SendsKeys
import Johnson.Top.H0.Opts.SendsOfLaid
import Johnson.Top.H0.Opts.SomeSeatsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

theorem hSh_laid (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∀ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R → RowsShaped R (P5J.At.pseats Zp) := by
  intro R hR
  obtain ⟨k0, k1, k2, e, p1, p2, hs⟩ := sends_of_laid hl L.pub
  exact rowsShaped_of fun k hne => rows_at_plan Zp Zp.D.1 hR hs (first_is_fifth hs) k hne

theorem k3Some_at_written (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hrr : P5J.rowsRead Z)
    (hS : P5J.At.shape Zp = proofSizedFull.request) (hp : P5J.At.pseats Zp = P5T.psFull) :
    ((List.range P5J.At.links.length).all fun l =>
      P5J.At.callsSomeB Zp Z.lay l && P5J.At.digSomeB Zp Z.lay l) = true :=
  k3Some_of_rows L hrr (hSh_laid hl L) (a1_at_written hS hp Z.lay) (a2_at_written hS hp Z.lay)

end P1Opts

#print axioms P1Opts.hSh_laid
#print axioms P1Opts.k3Some_at_written
