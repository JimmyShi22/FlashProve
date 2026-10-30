-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendSmp.lean: the law of a sending in the words of the row that the table of
joints asks of a block that sends sampled members: outside the rounds' lost sets, where the block
says yes, the condition behind holds, and for each new sampled message the record behind holds a
sample at whose seed the library's collision does not hold of the message's word behind.

Main names: clash_val; send_gives_smp.
smp is a letter: a reading of a carried record that returns a message's sample. One premise ties it
to the record: where the record's sample rows of the message are the kind's one row at a seed, the
reading returns a sample whose seed has that seed's sample map.

What is not claimed. A reading that meets that premise: GoodSendForms.lean. The other premises are
send_goodIn_entry's (GoodSend4.lean). Nothing on soundness of a protocol, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.GoodSend4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- The library's collision reads a seed through its sample map alone. -/
theorem clash_val {E : Type} [Field E] (o : OMsg E) (f : o.Str) (ρ ρ' : o.Z.D)
    (h : o.Z.val ρ = o.Z.val ρ') : o.Clash f ρ ↔ o.Clash f ρ' := by
  unfold OMsg.Clash Ood.Clash
  rw [h]

variable {T Cl W : Type} {F : Frame}

/-- **The law of a sending, as the row that is owed for a block that sends sampled members.** -/
theorem send_gives_smp (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (hS : IsSend P stOf b) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (On On' : T × F.E.Str → Prop)
    (hkeep : ∀ a τ x, On a →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x → On' x)
    (smp : T → ∀ k, Option (portOmZ P.codes (shapeAt P k) (rad k.val)).Smp)
    (hsmp : ∀ t k, sampledAt P k → ∀ ρ y, SeedIs P.codes (shapeAt P k) (stOf t)
        ((stOf t).oracles.size - (shapesOf P).length + k.val) ρ y →
      ∃ z, smp t k = some z ∧ (portOmZ P.codes (shapeAt P k) (rad k.val)).Z.val z.1 =
        (portOmZ P.codes (shapeAt P k) (rad k.val)).Z.val ρ) :
    ∀ a, On a → Doomed (uLT (ckP .two) [d₁, d₂])
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).err fun τ =>
        ∀ x, (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
          On' x ∧ ∀ k, sampledAt P k → ∃ z, smp x.1 k = some z ∧
            ¬ (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (fOf x.2 k) z.1 := by
  have g := send_goodIn_entry (W := W) (F := F) P rad hC b stOf hS base d₁ d₂ he₁ hk₁ e he fOf fIn
    hf On On' (fun _ _ => True) (fun _ _ => True) hkeep (fun _ _ _ _ _ _ _ => trivial)
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ x hx => ?_) (g a ha)
  obtain ⟨⟨h1, h2⟩, _⟩ := hτ x hx
  refine ⟨h1, fun k hk => ?_⟩
  obtain ⟨ρ, y, hs, hc⟩ := h2 k hk
  obtain ⟨z, hz, hv⟩ := hsmp _ k hk ρ y hs
  exact ⟨z, hz, fun hcl => hc ((clash_val _ _ z.1 ρ hv).1 hcl)⟩

end VerifiableInference.Desc.K1
