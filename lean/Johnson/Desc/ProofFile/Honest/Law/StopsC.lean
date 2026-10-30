-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StopsC.lean: each of the three sets of `honestBatchProverOfFile`
(Honest/StratC.lean), by itself, reads a verifier's message through `drawsAt` alone
(Honest/Law/StratWords.lean: the challenges as Honest/Frame.lean's lists). Membership is an
executable test on these lists (for Hid: and on w.1, w.2.1 and x: `hidB`). So two verifier's
messages at which `drawsAt` is the same are in the same of the three sets, Hid at one (w, x).
Honest/Law/Stops.lean proves this for the three together, at `honestB`.

  `badC_reads`, `stop0C_reads`, `hidC_reads`   the three tests
  `badC_congr`, `stop0C_congr`, `hidC_congr`   the same `drawsAt`, the same membership

Limits.
  * That a map on verifier's messages (such as one that sets the proof-of-work bits to 0) leaves
    `drawsAt` unchanged is not proved here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.StratC
import Johnson.Desc.ProofFile.Honest.Law.Stops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
  [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

theorem badC_reads (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
        (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Bad ↔
      badB F H ((drawsAt C D tF tJ t3 ρ).first, (drawsAt C D tF tJ t3 ρ).second) = true := by
  show badB F H (drawsLo C D tF tJ t3 (Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ)) = true ↔ _
  rw [drawsLo_at]

theorem stop0C_reads (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).stop0
        (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ) =
      stop0B F H (drawsAt C D tF tJ t3 ρ).shared := by
  show stop0B F H (drawsSh C D tF tJ t3 (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ)) = _
  rw [drawsSh_at]

theorem hidC_reads (w : W₀ × Rc × Sd) (x : Xi) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
        (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Hid w x ↔
      hidB F H w.1 w.2.1 x ((drawsAt C D tF tJ t3 ρ).first, (drawsAt C D tF tJ t3 ρ).second) =
        true := by
  show hidB F H w.1 w.2.1 x
    (drawsLo C D tF tJ t3 (Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ)) = true ↔ _
  rw [drawsLo_at]

variable {ρ ρ' : Iop.Rho (chainsOf C D tF tJ t3).sh}

theorem badC_congr (h : drawsAt C D tF tJ t3 ρ = drawsAt C D tF tJ t3 ρ') :
    Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
        (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Bad ↔
      Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ' ∈
        (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Bad := by
  rw [badC_reads, badC_reads, h]

theorem stop0C_congr (h : drawsAt C D tF tJ t3 ρ = drawsAt C D tF tJ t3 ρ') :
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).stop0
        (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ) =
      (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).stop0
        (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ') := by
  rw [stop0C_reads, stop0C_reads, h]

/-- **Two verifier's messages at which `drawsAt` is the same are both in Hid, taken by itself, or
neither is.** -/
theorem hidC_congr (w : W₀ × Rc × Sd) (x : Xi)
    (h : drawsAt C D tF tJ t3 ρ = drawsAt C D tF tJ t3 ρ') :
    Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
        (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Hid w x ↔
      Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ' ∈
        (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Hid w x := by
  rw [hidC_reads, hidC_reads, h]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.badC_reads
#print axioms ProofFile.Honest.stop0C_reads
#print axioms ProofFile.Honest.hidC_reads
#print axioms ProofFile.Honest.badC_congr
#print axioms ProofFile.Honest.stop0C_congr
#print axioms ProofFile.Honest.hidC_congr
