-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/BelowAtK10.lean: THE LAST PUBLIC CLAUSE: A MEMBER's
NUMBER LIES BELOW THE TABLE's NUMBER OF MESSAGES SENT AT THE PLACE OF THE KIND K10 OF ITS LINK: in
the goals' scope, where the verifier's own value is laid, at all 25 links. A join of two closed
facts and another file's theorem (msgs_at_ten). And with it ALL THREE CLAUSES of what `seed_field`
(SeedAtSeat.lean) takes on public data under the name hB. Theorems. A law file; no running text
imports it.
  `ten_is_sent`     BY THE KERNEL: the written list tenFull (CountsAtName.lean: place's number,
                    messages sent) bears, in order, the 25 numbers of sentAtK10W
                    (SeedPublicFull.lean).
  `tenAt l`         the number of the place of the kind K10 of link l, off that list.
  `below_at_k10`    noK10 (At.seats Zp) lo (At.pseats Zp) l i < (At.N Zp cF).msgsAt PS[tenAt l]?,
                    PS the full size's written list of places. By msgs_at_ten
                    (Johnson/HB/LLHARD/CountsAtName.lean) and below_laid.
  `hB_at_k10`       seed_field's hB, whole, at N := At.N Zp cF · p := PS[tenAt l]? · seats :=
                    At.seats Zp · lo := the l-th written list · seat := seatK10 lo (At.pseats Zp) l
                    · M := msgsOfChain Zp.made.proof.1 · every Ld that laidAtCodes returns.

Limits. At OnBytes.secondHashFunction (msgs_at_ten's letter). The full size alone. Nothing on the verifier's
state. "The value is laid" is spent here also for the entry tests madeRow or cutRow
(Johnson/Desc/Laid/ProofAsks.lean): through msgs_at_ten and below_laid; which of the two each of
these laws spends has not been traced here. Nothing on soundness or on hiding.

-/
import Johnson.LPFE1R.SeedPublicFull
import Johnson.HB.LLHARD.CountsAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.First.Close (noK10 seatK10)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes msgsOfChain)
open P5J (tenFull msgs_at_ten)

/-- The two written lists bear the same 25 numbers. -/
theorem ten_is_sent : tenFull.map (·.2) = sentAtK10W := by decide +kernel

/-- The number of the place of the kind K10 of link l. -/
def tenAt (l : ℕ) : ℕ := (tenFull.getD l (0, 0)).1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- **A member's number lies below the messages sent at K10's place.** -/
theorem below_at_k10 (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (i : Fin (linksFullLit.getD l []).length) :
    noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l i <
      (P5J.At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[tenAt l]? := by
  have hlen : l < tenFull.length := by
    have : tenFull.length = 25 := by decide
    omega
  have hx : tenFull.getD l (0, 0) ∈ tenFull := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  have e : (tenFull.getD l (0, 0)).2 = sentAtK10W.getD l 0 := by
    rw [← ten_is_sent, List.getD_eq_getElem _ _ hlen,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen), List.getElem_map]
  unfold tenAt
  rw [msgs_at_ten hW L hx, e]
  exact below_laid hW L hl i

/-- **seed_field's hB, whole.** -/
theorem hB_at_k10 (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {Ld : Laid}
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld) {l : ℕ} (hl : l < 25)
    (i : Fin (linksFullLit.getD l []).length) :
    (P5J.At.seats Zp).idxOf (seatK10 (linksFullLit.getD l []) (P5J.At.pseats Zp) l i) <
        (P5J.At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[tenAt l]? ∧
      Ld.places[(P5J.At.seats Zp).idxOf
        (seatK10 (linksFullLit.getD l []) (P5J.At.pseats Zp) l i)]? =
          some (seatK10 (linksFullLit.getD l []) (P5J.At.pseats Zp) l i) ∧
      (msgsOfChain Zp.made.proof.1)[(P5J.At.seats Zp).idxOf
        (seatK10 (linksFullLit.getD l []) (P5J.At.pseats Zp) l i)]? =
          some ((linksFullLit.getD l []).get i).1 :=
  ⟨below_at_k10 hW L hl i, (seed_public_laid hW L hLd).2 l hl i, shape_fact_laid hW L hl i⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ten_is_sent
#print axioms VerifiableInference.Desc.LinkJoin.below_at_k10
#print axioms VerifiableInference.Desc.LinkJoin.hB_at_k10
