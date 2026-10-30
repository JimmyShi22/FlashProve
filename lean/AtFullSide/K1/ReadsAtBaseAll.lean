-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsAtBaseAll.lean: the family TieReadsS of the item "tie l" at the base prover, at all
25 segments, by sort: hF2 of exchangeAtS_tie_base (AtFullSide/K1/TieAtBase.lean).

  tieReadsS_base   l < 25. Layers: vecTie_layers_head. Attention: vecTie_att_head. The head:
                   vecTie_head_paid. hix: ix_at_reads

Limits. Under ThrS: idle at a Said or Vd of which nothing holds. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K1.ReadsAtBase
import AtFullSide.K1.ReadsIx
import AtFullSide.K1.AttVecTie
import AtFullSide.K1.ReadsHeadPhi
import AtFullSide.K1.VecTieLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.HonestTrace (Seat)
open OnBytes.HonestTrace.U3 (u3Seats)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE SECOND FAMILY, AT ALL 25 SEGMENTS.** -/
theorem tieReadsS_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) (hO : OthersApart A Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) :
    TieReadsS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd
        Kp w) Said (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) (witB I A.Z)
      (ProofFile.Honest.K3.matsOwn (P5J.At.X A.Z) l) (K1.noL l false) l (nReads (P5J.At.X A.Z) l) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hG : ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G := by
    rw [eG]
    exact O.blank
  refine tieReadsS_of_tie h hA cells tok Oth hO test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl
    (ix_at_reads h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl) ?_
  intro st hs hseg
  by_cases h24 : l = 24
  · subst h24
    exact vecTie_head_paid h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hG
      (fun _ => rfl) hs hseg
  · by_cases he : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      obtain ⟨-, -, cpair, -⟩ := seat_clauses h hG hs
      rw [hseg] at cpair
      exact vecTie_layers_head h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said (by omega) hG cpair _
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      obtain ⟨-, -, cpair, -⟩ := seat_clauses h hG hs
      rw [hseg] at cpair
      exact vecTie_att_head h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid (by omega) hG
        cpair _

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieReadsS_base
