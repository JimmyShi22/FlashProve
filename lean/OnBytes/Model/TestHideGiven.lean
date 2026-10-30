-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHideGiven.lean: functions of OnBytes/Model/Hide.lean, Rounds.lean and Tsc.lean,
compared with values of the C++ verifier.
The tests run when this file compiles.

The numbers below are values that the C++ verifier computed while it checked an honest proof for a
small test configuration with 64 token positions. Its weights are made up, generated from a test
seed: no number here comes from a real model's weights. The numbers belong to the sub-proof of the
output head, which has 897 claims there. The repository holds that configuration's public files
(prover/tests/configurations/pinned_no_proof_of_work/) but no tool that prints the numbers, so a
reader cannot make them again from it. Another proof for the same configuration gives another theta.

What is tested.
 1. The weights of the claims: theta^c at six numbers c from 2 up to the last claim's.
 2. The constant of the one equation after each of the first eight claims. Each claim enters here
    with its constant alone.
 3. The numbers of slots: the values of the C++ verifier's slot counter before and after one layer
    of a product tree and three token sumchecks.

What this shows: Fork.kapAt at these numbers, Fork.kap and the constant's part of Fork.push for the
first eight claims, and the counts of slots give the C++ values. It does not show that the two
verifiers check a whole sub-proof in the same way: no message of the proof is read here, and the
coefficients on slots and on entries are not compared.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Model.Tsc

namespace OnBytes.Model.TestHideGiven

/-- The element that batches the output head's claims. -/
def theta : E := E.mk3 16420620390143814072 764070528463702388 12236733831512304661

/-- A state in which theta is drawn and the plan has the output head's 897 claims. -/
def start : Fork :=
  { theta := theta, thetaDrawnF := true, planClaimsF := 897,
    kapMapF := Array.replicate 897 false }

-- theta^c, as the C++ verifier computed it
#guard start.kapAt 0 == some oneE
#guard start.kapAt 2 ==
  some (E.mk3 2122654135990540996 7334243595508173520 16089035765929345413)
#guard start.kapAt 3 ==
  some (E.mk3 15566694587198438447 12397506112015974189 12792880318100186148)
#guard start.kapAt 16 ==
  some (E.mk3 5186679928484767160 15405049716919434396 17992434007280649910)
#guard start.kapAt 100 ==
  some (E.mk3 13388657189998805100 13798038513392733941 7900589928957673576)
#guard start.kapAt 511 ==
  some (E.mk3 12392739154221946267 10095706237260097047 16419496485023330375)
#guard start.kapAt 896 ==
  some (E.mk3 16391371117236618763 4937198188537637017 6656079986209772165)

/-- The constants of the forms of the first eight claims. -/
def constants : List E :=
  [E.mk3 12575578502393639432 280588382041531496 4303353009612025361,
   E.mk3 6787990489541926430 6078834689426114544 9712200119620357808,
   E.mk3 2149423036788084268 17893733650671335031 6071472178215246609,
   E.mk3 13231579554105141117 1750762384209863092 6357981098266917872,
   E.mk3 5412810282101822371 2141862999421520068 16118726699540758806,
   E.mk3 11958549261802121750 12907470322224857133 1232414548976311688,
   E.mk3 1142694031241509141 13670932963717794484 6596476243882104344,
   E.mk3 16221050337287142540 859728985483975303 229802071417653211]

/-- The constant of the one equation after each of these claims. -/
def after : List E :=
  [E.mk3 12575578502393639432 280588382041531496 4303353009612025361,
   E.mk3 9437827872442040417 9705932941478133465 10949685633195413666,
   E.mk3 17944832161636162129 6896191900969401168 16022649552477855559,
   E.mk3 4550771538363667434 827143828062480699 487609202330646493,
   E.mk3 7649796293739103201 12330075371787390956 10386865297774448412,
   E.mk3 7059712043337979274 13621024065857574005 2376544459010534046,
   E.mk3 14577922073258072753 14780143798178276235 4267868823766072582,
   E.mk3 1394526723402847480 13512803197703317245 16315720335685341205]

/-- The constant of the one equation after the first n claims, each with its constant alone. -/
def constantAfter (n : Nat) : Option E :=
  (((constants.take n).map Aff.ofConst).foldlM Fork.lin start).map (·.c0)

#guard (List.range 8).all fun n => constantAfter (n + 1) == after[n]?

-- a layer with 9 + 6 variables: the counter went from 1540 to 1575
#guard 1540 + layerSlots 15 == 1575
-- token sumchecks over 6 variables: 4 end values, 1582 to 1602; 2 end values, 1602 to 1620;
-- 2 end values and 9 further rounds, 1620 to 1656
#guard 1582 + tscSlots 6 4 2 == 1602
#guard 1602 + tscSlots 6 2 2 == 1620
#guard 1620 + tscSlots 6 2 2 9 == 1656

end OnBytes.Model.TestHideGiven
