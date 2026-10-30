-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ListedAtD.lean: THE FIELD "listed" OF `PlanAt` AT W's COMMITMENT (number 356)
AND AT THE FIRST SEGMENT's OPENING (number 2), AT THE LAID VALUE's OWN DATA D: FROM THE SCOPE, THE
DESCRIPTION's DATA's RETURN, ITS planOk AND THE THREE FLAT LISTS' HEADS ALONE. Two statements with
their proofs: calls of `listed_at_W`, `listed_at_G` (Johnson/Desc/AtSeats/ListedAtFlat.lean) at
the closed form of the pieces, by `six_together`
(Johnson/Desc/Sound/SixTogether.lean). WHO CALLS: the premises hlist of `W_HP_atAll`,
`G_HP_atAll` (Johnson/Desc/K1/Law/RadiiAtTwo.lean): so of the two fields W_HP, G_HP of kind K1's
condition nothing is left but "told". What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.ListedAtFlat
import Johnson.Desc.Sound.SixTogether

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open IM (Open)

/-- The seated description. -/
abbrev FDz (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At W's commitment, at the laid value's data.** -/
theorem listed_W_atD (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {D : WholeD} {file : String}
    (hD : (FDz Z A B c).data file = .ok D) (hp : (FDz Z A B c).planOk = true)
    {b₁ : Block (FDz Z A B c).S₁ (FDz Z A B c).Cl} {l₁ : List (Block (FDz Z A B c).S₁ (FDz Z A B
      c).Cl)}
    {b₂ : Block (FDz Z A B c).S₂ (FDz Z A B c).Cl} {l₂ : List (Block (FDz Z A B c).S₂ (FDz Z A B
      c).Cl)}
    {b₃ : Block (FDz Z A B c).S₃ (FDz Z A B c).Cl} {l₃ : List (Block (FDz Z A B c).S₃ (FDz Z A B
      c).Cl)}
    (q₁ : (FDz Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FDz Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FDz Z A B c).second.blocksInOrder = b₃ :: l₃) (d₁ d₂ : RDT)
    (hds : (D.ds₁.drop (inFront c 356)).take 2 = [d₁, d₂]) :
    ListedAt (Sound.frameAt D (Sound.allOf D) D.key₁ 0) (nTrees (D.ds₁.take (inFront c 356)))
      [d₁, d₂] := by
  obtain ⟨R₁, R₂, R₃, hDD, w₁, _, hFit, hall⟩ := six_together (W := Unit) hD hp q₁ q₂ q₃
  subst hDD
  obtain ⟨hT, hC, _⟩ := hall (fun _ _ _ _ w => w) (fun _ _ _ _ w => w) (fun _ _ _ _ w => w) () ()
  exact listed_at_W hS hR O hT hC w₁ _ (hFit _ _ _) d₁ d₂ hds

/-- **At the first segment's opening, at the laid value's data.** -/
theorem listed_G_atD (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {D : WholeD} {file : String}
    (hD : (FDz Z A B c).data file = .ok D) (hp : (FDz Z A B c).planOk = true)
    {b₁ : Block (FDz Z A B c).S₁ (FDz Z A B c).Cl} {l₁ : List (Block (FDz Z A B c).S₁ (FDz Z A B
      c).Cl)}
    {b₂ : Block (FDz Z A B c).S₂ (FDz Z A B c).Cl} {l₂ : List (Block (FDz Z A B c).S₂ (FDz Z A B
      c).Cl)}
    {b₃ : Block (FDz Z A B c).S₃ (FDz Z A B c).Cl} {l₃ : List (Block (FDz Z A B c).S₃ (FDz Z A B
      c).Cl)}
    (q₁ : (FDz Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FDz Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FDz Z A B c).second.blocksInOrder = b₃ :: l₃) (d₁ d₂ : RDT)
    (hds : (D.ds₁.drop (inFront c 2)).take 2 = [d₁, d₂]) :
    ListedAt (Sound.frameAt D (Sound.allOf D) D.key₁ 0) (nTrees (D.ds₁.take (inFront c 2)))
      [d₁, d₂] := by
  obtain ⟨R₁, R₂, R₃, hDD, w₁, _, hFit, hall⟩ := six_together (W := Unit) hD hp q₁ q₂ q₃
  subst hDD
  obtain ⟨hT, hC, _⟩ := hall (fun _ _ _ _ w => w) (fun _ _ _ _ w => w) (fun _ _ _ _ w => w) () ()
  exact listed_at_G hS hR O hT hC w₁ _ (hFit _ _ _) d₁ d₂ hds

end

end VerifiableInference.Desc.K1
