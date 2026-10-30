-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09CountsMid.lean: THE TABLE's TWO COUNTS (the plan's
numbers of commitment trees and of oracle messages) STAND STILL OVER A LINK's TWO MIDDLE PLACES TOO:
the frame's sub-protocol behind the batching, and the one equation. For the hand-ons of the promise
inside the link's law. Theorems. Over K09Counts.lean beside this file, whose counts_stay is general
in the number. A law file; no running text imports it.
  `behind_tells_none`   in scope, at an opened seat, l < 25: the sub-protocol at number 14 l + ‹the
                    link's hearing sub-protocols› + 2 + 1 of the first chain's flat list declares no
                    oracle message (frame_oracles,
                    Johnson/IMR/FrameQuiet.lean).
  `equation_tells_none`   the like at + 2 + 1 + 1: the first of the closing's three (IM.close_of ·
                    IM.close_numbers · IM.alone_oracles).
  `k9_counts_mid`     h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x · m < 25 ⊢ the two counts stay at
                    k + 1 AND at k + 1 + 1, k := batchAt fullLinks At.ps m.

Limits. AT OnBytes.secondHashFunction ALONE, in scope. Nothing on the verifier's state. Nothing on soundness or
on hiding.
-/
import Johnson.P5J.K09Counts
import Johnson.IMR.FrameQuiet

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
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching closeKinds)
open VerifiableInference.Desc.LinkJoin (batchAt)

section Seat
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The frame's sub-protocol behind the batching declares no oracle message. -/
theorem behind_tells_none (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ b, c.blocksInOrder[14 * l + (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 2 + 1]? = some b ∧
      b.oracles.flatten = [] := by
  obtain ⟨Lk', _, _, _, e1', _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩ := (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk, _, bB, _, e1, _, _, _, hf, ho, _⟩ := IM.frame_oracles hS hR O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e1'.symm.trans e1)
  rw [hn] at hf
  exact ⟨bB, hf, by rw [ho]; rfl⟩

/-- The one equation's sub-protocol declares no oracle message. -/
theorem equation_tells_none (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ b, c.blocksInOrder[14 * l + (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 2 + 1 + 1]? = some b ∧
      b.oracles.flatten = [] := by
  obtain ⟨Lk', _, _, _, e1', _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩ := (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk, p, Q, e1, _, _, hc⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e1'.symm.trans e1)
  obtain ⟨b, x, hb, hx, hla⟩ := hc 0 .K9 rfl
  have hf := IM.close_numbers hS hR O hl e1 hb
  rw [hn] at hf
  refine ⟨b, hf, ?_⟩
  rw [IM.alone_oracles hla]
  obtain rfl := Option.some.inj hx
  rfl

end Seat

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The table's two counts stay over the link's two middle places.** -/
theorem k9_counts_mid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    ((At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 1 + 1]? =
        (At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 1]? ∧
      (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1 + 1]? =
        (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1]?) ∧
    ((At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 1 + 1 + 1]? =
        (At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + 1 + 1]? ∧
      (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1 + 1 + 1]? =
        (At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1 + 1]?) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : batchAt fullLinks At.ps m = 14 * m + (kindsBeforeBatching (IM.subAt m) (m == 0)).length + 2 := by
    simpa using List.all_eq_true.1 batchAt_W m (List.mem_range.2 hm)
  obtain ⟨b2, f2, o2⟩ := behind_tells_none h.scope h.reads O hm
  obtain ⟨b3, f3, o3⟩ := equation_tells_none h.scope h.reads O hm
  rw [e]
  exact ⟨counts_stay h _ b2 f2 o2, counts_stay h _ b3 f3 o3⟩

end P5J

#print axioms P5J.behind_tells_none
#print axioms P5J.equation_tells_none
#print axioms P5J.k9_counts_mid
