-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/DigAtHead.lean: AT THE HEAD `AtMgA`, AT THE SECOND HASH FUNCTION: TWO CLOSED FIELDS
OF WHAT IS LEFT OF THE CONDITION OF THE KIND K9 (hdig and HD of `CoreRest2`,
Johnson/Desc/First/Link/Law/LinkRestAtSort2.lean; of `LinkRest` before it) ARE GIVEN BY THE
DIGITS' ROW (row 11), WHICH THE VERIFIER ASKS. Three theorems. A joining. IT STANDS OVER NO
CANDIDATE ROW.
  `linksOf_pub`: in scope the digits' row ranges over 25 segments.
  `AtMgA.sent_is`: what `K3Asks.sentOf Zp` sends is what the constant's parameters send.
  `AtMgA.k9_dig`: **at each m below 25, at every radius: ∃ y tlD, `digAt (At.X Zp) m = some (y,
  tlD)` ∧ `DigOK (settingOf (At.X Zp).P.frame) y tlD h.𝔇.sent rad Cb.Gl.p`**: hdig and HD, in
  their own texts, at x := y, set := `settingOf (At.X Zp).P.frame`, pp := `Cb.Gl.p`; at rad :=
  `h.𝔇.l3.rad` among all. By `LPFD.asks_rest` (Johnson/Desc/Laid/ProofAsksLaw2.lean: the row has
  accepted where the value is laid) and `asks_dig`
  (Johnson/Desc/First/Look/K3AsksLaw.lean). NO PREMISE BUT THE HEAD.
Limits. At the second hash function alone (the laws on the scope speak of `publicOf`). No
probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.First.Look.K3AsksLaw
import Johnson.Desc.First.Look.K3AsksDoor
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- In scope the digits' row ranges over 25 segments. -/
theorem linksOf_pub {lay : ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol lay Z.KL = .ok Zp) :
    Desc.K3Asks.linksOf Zp.p.X = 25 := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hW : Verify.publicOf Z.pol Z.KL (some lay) = .ok Zp.p.X :=
    (PlanWritten.publicOfO_older Z.pol Z.KL (some lay)).symm.trans (ProofFile.Law.pub_public hpub)
  obtain ⟨hq, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR hW
  unfold Desc.K3Asks.linksOf
  rw [hq, hN]
  rfl

/-- What `sentOf Zp` sends is what the constant's parameters send. -/
theorem AtMgA.sent_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (Desc.K3Asks.sentOf Zp).up = h.𝔇.sent := rfl

/-- **hdig and HD, in their own texts: no premise but the head.** -/
theorem AtMgA.k9_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25)
    (rad : OracleShape → ℕ) :
    ∃ y tlD, Desc.First.Look.digAt (At.X Zp) m = some (y, tlD) ∧
      Desc.First.Look.DigOK (Params.settingOf (At.X Zp).P.frame) y tlD h.𝔇.sent rad Cb.Gl.p := by
  have hd : Desc.K3Asks.digRow Zp.p.X (Desc.K3Asks.sentOf Zp) = true :=
    (LPFD.asks_rest h.toAtMg.laid.asks h.toAtMg.laid.pub).1
  have hl : m < Desc.K3Asks.linksOf Zp.p.X := by
    rw [linksOf_pub h.toAtMg.scope h.toAtMg.laid.pub]
    exact hm
  rw [← h.sent_is]
  exact Desc.K3Asks.asks_dig hd rad m hl

end P5J

#print axioms P5J.linksOf_pub
#print axioms P5J.AtMgA.sent_is
#print axioms P5J.AtMgA.k9_dig
