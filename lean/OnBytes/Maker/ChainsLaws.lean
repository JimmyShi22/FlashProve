-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ChainsLaws.lean: the parts of a transcript of a file with three joined chains
(Compile/Joined/Types.lean): what a proof that a verifier of such a file is local (`IOR.IsLocal`,
Ior/Ior.lean) takes from them, beside that file's `rho_tr₁`, `rho_tr₂`, `rho_tr₃`.

  `plains_tr₁`, `plains_tr₂`, `plains_tr₃`   the plain parts of a chain's part of a transcript are
        that chain's part of the transcript's plain parts
  `plain_msgF`, `plain_msgJ`, `plain_msg3`   the like for the three rounds between the chains
  `read_i₁`, `read_i₂`, `read_i₃`   two transcripts answer alike at a chain's position, taken as a
        position of the whole, if and only if their parts for that chain answer alike there
  `parts_congr`   two transcripts with the same verifier's messages and the same plain parts have,
        chain by chain, parts with the same verifier's messages and the same plain parts

Not claimed. Nothing on soundness.

-/
import Compile.Joined.Types

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Compile.Joined

variable (G : Chains)

theorem plains_trJ (τ : Tr G.sh) : (G.trJ τ).plains = G.plJ' τ.plains := Tr.plains_snd τ.2.2

theorem plains_tr₁ (τ : Tr G.sh) : (G.tr₁ τ).plains = G.pl₁ τ.plains := Tr.plains_fst τ.2.2

theorem plains_tr₂ (τ : Tr G.sh) : (G.tr₂ τ).plains = G.pl₂ τ.plains := by
  unfold Chains.tr₂ Chains.pl₂
  rw [Tr.plains_fst, ← plains_trJ]
  rfl

theorem plains_tr₃ (τ : Tr G.sh) : (G.tr₃ τ).plains = G.pl₃ τ.plains := by
  unfold Chains.tr₃ Chains.pl₃
  rw [← plains_trJ]
  exact congrArg Prod.snd (Tr.plains_snd (s := G.s₂) (G.trJ τ).2.2)

theorem plain_msgF (τ : Tr G.sh) : (G.msgF τ).2 = G.plF τ.plains := rfl

theorem plain_msgJ (τ : Tr G.sh) : (G.msgJ τ).2 = G.plJ τ.plains := by
  unfold Chains.msgJ Chains.plJ
  rw [← plains_trJ]
  rfl

theorem plain_msg3 (τ : Tr G.sh) : (G.msg3 τ).2 = G.pl3 τ.plains := by
  unfold Chains.msg3 Chains.pl3
  rw [← plains_trJ]
  exact congrArg Prod.fst (Tr.plains_snd (s := G.s₂) (G.trJ τ).2.2)

/-- Two transcripts answer alike at a position of chain 1 if and only if their parts do. -/
theorem read_i₁ (τ τ' : Tr G.sh) (p : OPos G.s₁) :
    τ.read (G.i₁ p) = τ'.read (G.i₁ p) ↔ (G.tr₁ τ).read p = (G.tr₁ τ').read p :=
  Tr.read_left_eq_iff τ.2.2 τ'.2.2 p

theorem read_iJ' (τ τ' : Tr G.sh) (p : OPos G.shJ) :
    τ.read (G.iJ' p) = τ'.read (G.iJ' p) ↔ (G.trJ τ).read p = (G.trJ τ').read p :=
  Tr.read_right_eq_iff (s := G.s₁) τ.2.2 τ'.2.2 p

/-- The same at a position of chain 2. -/
theorem read_i₂ (τ τ' : Tr G.sh) (p : OPos G.s₂) :
    τ.read (G.i₂ p) = τ'.read (G.i₂ p) ↔ (G.tr₂ τ).read p = (G.tr₂ τ').read p :=
  (read_iJ' G τ τ' _).trans (Tr.read_left_eq_iff (G.trJ τ).2.2 (G.trJ τ').2.2 p)

/-- The same at a position of chain 3. -/
theorem read_i₃ (τ τ' : Tr G.sh) (p : OPos G.s₃) :
    τ.read (G.i₃ p) = τ'.read (G.i₃ p) ↔ (G.tr₃ τ).read p = (G.tr₃ τ').read p :=
  (read_iJ' G τ τ' _).trans
    (Tr.read_right_eq_iff (s := G.s₂) (G.trJ τ).2.2 (G.trJ τ').2.2 (.inr p))

/-- Chain by chain: the same verifier's messages and the same plain parts. -/
theorem parts_congr (τ τ' : Tr G.sh) (hρ : τ.rho = τ'.rho) (hp : τ.plains = τ'.plains) :
    ((G.tr₁ τ).rho = (G.tr₁ τ').rho ∧ (G.tr₁ τ).plains = (G.tr₁ τ').plains) ∧
    ((G.tr₂ τ).rho = (G.tr₂ τ').rho ∧ (G.tr₂ τ).plains = (G.tr₂ τ').plains) ∧
    ((G.tr₃ τ).rho = (G.tr₃ τ').rho ∧ (G.tr₃ τ).plains = (G.tr₃ τ').plains) ∧
    (G.msgF τ).2 = (G.msgF τ').2 ∧ (G.msgJ τ).2 = (G.msgJ τ').2 ∧ (G.msg3 τ).2 = (G.msg3 τ').2 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [G.rho_tr₁, G.rho_tr₁, hρ]
  · rw [plains_tr₁, plains_tr₁, hp]
  · rw [G.rho_tr₂, G.rho_tr₂, hρ]
  · rw [plains_tr₂, plains_tr₂, hp]
  · rw [G.rho_tr₃, G.rho_tr₃, hρ]
  · rw [plains_tr₃, plains_tr₃, hp]
  · rw [plain_msgF, plain_msgF, hp]
  · rw [plain_msgJ, plain_msgJ, hp]
  · rw [plain_msg3, plain_msg3, hp]

end OnBytes.Maker
