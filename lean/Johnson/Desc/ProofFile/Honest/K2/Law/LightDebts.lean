-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LightDebts.lean: the kind "the code switch" (K2): THE SIX
PUBLIC TESTS OF `publicOk_of_six` (LightByAddress.lean of this folder) AS SIX NAMED STATEMENTS AT
ALL PLACES OF THE KIND, AT THE LAYOUT AND THE SEGMENTS THAT THE KIND's LOT LAYS; AND THAT TOGETHER
THEY GIVE THE LOT's PUBLIC TEST AT EVERY PLACE. Six definitions of statements; one statement with
its proof.

  `Addressed`       at each place: every own message of every segment in front has an address
  `SwitchesLight`   at each place: the light test at the switches' own data, at their own addresses
  `OpeningLight`    the like at the opening's data
  `DigitsLight`     the like at the digits' data
  `ReadsLight`      the like at the reads' data, at a public instance: it alone reads the instance
  `OwnShares`       at each place: the switch's own sending's share
  `publicOk_of_debts`   the six ⊢ at each place of the kind `publicOk` says yes at that instance

Limits. THE SIX ARE STATEMENTS: NONE IS PROVED HERE, AT ANY PUBLIC PART OR GROUND. One way alone, as
the light test is. Nothing on what the data hold. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LightByAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (u3RowsOf)

/-- Every own message of every segment in front of a place has an address there. -/
def Addressed (Z : Pub) (G : Ground) : Prop :=
  ∀ p ∈ switchPlaces Z G, addressed p ((segmentsOf Z G).take p.link) = true

/-- The light test at the switches' own data, at the addresses that have a switch's seat. -/
def SwitchesLight (S : Sz) (Z : Pub) (G : Ground) : Prop :=
  ∀ p ∈ switchPlaces Z G,
    lightAt (switchData S Z G) (mineSwitch Z G) G.first.layout p
      ((segmentsOf Z G).take p.link) = true

/-- The light test at the opening's data, at the opening's sender's addresses. -/
def OpeningLight (S : Sz) (Z : Pub) (G : Ground) : Prop :=
  ∀ p ∈ switchPlaces Z G,
    lightAt (K1.firstFill S G.first) (mineFirst Z G) G.first.layout p
      ((segmentsOf Z G).take p.link) = true

/-- The light test at the digits' data, at the seats of the array "BZ". -/
def DigitsLight (Z : Pub) (G : Ground) : Prop :=
  ∀ p ∈ switchPlaces Z G,
    lightAt (K1.digitsFill Z G (K3.matsOwn G.W)) (mineDigits Z G) G.first.layout p
      ((segmentsOf Z G).take p.link) = true

/-- The light test at the reads' data at the public instance x, at all other addresses. -/
def ReadsLight (Z : Pub) (G : Ground) (x : ProofFile.Inst) : Prop :=
  ∀ p ∈ switchPlaces Z G,
    lightAt (u3RowsOf Z G x) (mineReads Z G) G.first.layout p
      ((segmentsOf Z G).take p.link) = true

/-- Each switch's own sending's share. -/
def OwnShares (S : Sz) (Z : Pub) (G : Ground) : Prop :=
  ∀ p ∈ switchPlaces Z G, ownShare S Z G G.first.layout p = true

/-- **The six give the lot's public test at every place of the kind.** -/
theorem publicOk_of_debts {S : Sz} {Z : Pub} {G : Ground} {x : ProofFile.Inst} (ha : Addressed Z G)
    (h1 : SwitchesLight S Z G) (h2 : OpeningLight S Z G) (h3 : DigitsLight Z G)
    (h4 : ReadsLight Z G x) (ho : OwnShares S Z G) :
    ∀ p ∈ switchPlaces Z G,
      publicOk (withSwitchData S (K1.lotData S) Z G) G.first.layout p
        ((segmentsOf Z G).take p.link) x = true :=
  fun p hp => publicOk_of_six S Z G x G.first.layout p _ (ha p hp) (h1 p hp) (h2 p hp) (h3 p hp)
    (h4 p hp) (ho p hp)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.Addressed
#print axioms ProofFile.Honest.K2.Law.SwitchesLight
#print axioms ProofFile.Honest.K2.Law.OpeningLight
#print axioms ProofFile.Honest.K2.Law.DigitsLight
#print axioms ProofFile.Honest.K2.Law.ReadsLight
#print axioms ProofFile.Honest.K2.Law.OwnShares
#print axioms ProofFile.Honest.K2.Law.publicOk_of_debts
