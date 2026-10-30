-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09Counts.lean: OF WHAT IS LEFT AT THE 25 LINKS OF THE BATCHING
KIND K9 AT THE CLOSED CONSTANT (`LinkList`, `ShutList`: Johnson/Desc/First/Link/Law/) FOUR FIELDS:
THE TABLE's TWO COUNTS (the plan's numbers of commitment trees and of oracle messages) STAND STILL
OVER A LINK's BATCHING's PLACE AND OVER ITS SHUTTING's: treesB, msgsB; treesS, msgsS. Theorems.
After Johnson/P5J/K10Seat.lean (k10_counts_at), whose five lines are kind-free. A law
file; no running text imports it.
  `counts_stay`     the five lines, general in the number: cF.blocksInOrder[k]? = some B · B.oracles.flatten
                    = [] ⊢ the two counts of At.N Zp cF are at At.ps[k + 1]? what they are at
                    At.ps[k]?.
  `batch_tells_none`   in scope, at an opened seat, l < 25: the sub-protocol at number 14 l + ‹the
                    link's hearing sub-protocols› + 2 of the first chain's flat list declares no
                    oracle message: it is K9's own batching, seated alone (Johnson/IMR/:
                    k9_of; alone_oracles).
  `shut_tells_none`   the like at number 14 l + ‹…› + 6: the third of the closing's three (IM's
                    close_of · close_numbers).
  `batchAt_W`       a closed fact on the written lists, by the kernel: batchAt fullLinks At.ps m =
                    14 m + ‹…› + 2 at each m < 25.
  `k9_counts_at`    h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x · m < 25 ⊢ the two counts stay at k
                    := batchAt fullLinks At.ps m AND at k := batchAt fullLinks At.ps m + 4.

Limits. AT OnBytes.secondHashFunction ALONE, in scope. Nothing on the verifier's state. Nothing on the laws.
Nothing on soundness or on hiding.
-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.PlacesPaid
import Johnson.Desc.First.ToldSucc
import Johnson.Desc.ProofFile.Law.KindPlaces
import Johnson.Desc.First.Link.Law.K9KindTiedR
import Johnson.IMR.LinkSeat
import Johnson.IMR.CloseSeat
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc (Block Chain FileDescription Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching closeKinds told_succ_ps)
open VerifiableInference.Desc.LinkJoin (batchAt)

section Seat
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The batching's sub-protocol declares no oracle message. -/
theorem batch_tells_none (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ b, c.blocksInOrder[14 * l + (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 2]? = some b ∧
      b.oracles.flatten = [] := by
  obtain ⟨Lk, p, w, T, _, _, _, _, _, _, hla, hf, _, _, _, _, _, hn, _⟩ := (IM.k9_of hS hR O).2 l hl
  rw [hn] at hf
  refine ⟨_, hf, ?_⟩
  rw [IM.alone_oracles (hla _)]
  rfl

/-- The shutting's sub-protocol declares no oracle message. -/
theorem shut_tells_none (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ b, c.blocksInOrder[14 * l + (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 2 + 4]? = some b ∧
      b.oracles.flatten = [] := by
  obtain ⟨Lk', _, _, _, e1', _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩ := (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk, p, Q, e1, _, _, hc⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e1'.symm.trans e1)
  obtain ⟨b, x, hb, hx, hla⟩ := hc 2 .K9 rfl
  have hf := IM.close_numbers hS hR O hl e1 hb
  rw [hn] at hf
  refine ⟨b, ?_, ?_⟩
  · have e : 14 * l + (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 2 + 4 =
        14 * l + (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 4 + 2 := by omega
    rw [e]
    exact hf
  · rw [IM.alone_oracles hla]
    obtain rfl : VerifiableInference.Desc.K9.shut p (Q.piece + 1) = x := Option.some.inj hx
    rfl

end Seat

/-- A closed fact on the written lists. -/
theorem batchAt_W : (List.range 25).all (fun m =>
    batchAt fullLinks At.ps m == 14 * m + (kindsBeforeBatching (IM.subAt m) (m == 0)).length + 2) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The five lines, general in the number. -/
theorem counts_stay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : ℕ) (B : Block TS ProofFile.Cl)
    (hB : cF.blocksInOrder[k]? = some B) (h0 : B.oracles.flatten = []) :
    (At.N Zp cF).treesAt At.ps[k + 1]? = (At.N Zp cF).treesAt At.ps[k]? ∧
      (At.N Zp cF).msgsAt At.ps[k + 1]? = (At.N Zp cF).msgsAt At.ps[k]? := by
  have hpl := At.places_paid h.scope h.reads h.laid
  rw [At.N_at h.scope h.reads h.laid]
  have e := told_succ_ps (N := P5T.numbersOf (At.pseats Zp)) (s := At.shape Zp) (links := At.links)
    (bs := cF.blocksInOrder) At.ps hpl (ProofFile.Law.flatPlaces_nodup fullLinks true) k B hB
  rw [h0] at e
  simpa using e

/-- **The table's two counts stay over the batching's place and over the shutting's.** -/
theorem k9_counts_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    ((At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 1]? =
        (At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m]? ∧
      (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1]? =
        (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m]?) ∧
    ((At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 4 + 1]? =
        (At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 4]? ∧
      (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 4 + 1]? =
        (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 4]?) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : batchAt fullLinks At.ps m = 14 * m + (kindsBeforeBatching (IM.subAt m) (m == 0)).length + 2 := by
    simpa using List.all_eq_true.1 batchAt_W m (List.mem_range.2 hm)
  obtain ⟨b1, f1, o1⟩ := batch_tells_none h.scope h.reads O hm
  obtain ⟨b5, f5, o5⟩ := shut_tells_none h.scope h.reads O hm
  rw [e]
  exact ⟨counts_stay h _ b1 f1 o1, counts_stay h _ b5 f5 o5⟩

end P5J

#print axioms P5J.batch_tells_none
#print axioms P5J.shut_tells_none
#print axioms P5J.batchAt_W
#print axioms P5J.counts_stay
#print axioms P5J.k9_counts_at
