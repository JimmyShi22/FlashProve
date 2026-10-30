-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/SidesSocket.lean: the socket of a kind's lot in the sides G: at theSides a list of G
is a row of the rows that G is made of, and at overlaySlots a list of G of a kind is a row of the lot
filled in for that kind, wherever the filling's other lots have no side of that kind.

  KeepsRows              letters that leave a row whole: forgetting them gives the row back
  keepsRows_bare, keepsRows_ofThreads   both ways of setting letters do
  first_socket, shared_socket, second_socket   a list of theSides, its letters forgotten, is a row
  filled_slot            at overlaySlots: a list of the first chain of the kind κ is a row of the lot

By what. theSides, overlaySlots, overlay_half (E2E/TheSides.lean); find_of_nodup
(Johnson/SendSim/Seat/LotsGuardTie.lean).

Limits.
- A membership alone: what a row hands in is the kind's.
- filled_slot asks that the filling's lots of other names have no side of the kind: a word on the
  filling, which the kinds of the lots pay.
- Nothing on completeness, soundness or hiding.
-/
import E2E.TheSides
import Johnson.SendSim.Seat.LotsGuardTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (FileDescription KindName)
open ProofFile.Honest
open AtPublicFiles.TheSides

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **Letters that leave a row whole.** -/
def KeepsRows (L : Letters F Bk W₀ Rc Ky Tr X₀ X) : Prop :=
  (∀ r, (L.first r).bare = r) ∧ (∀ r, (L.shared r).bare = r) ∧ ∀ r, (L.second r).bare = r

/-- Letters that say nothing leave a row whole. -/
theorem keepsRows_bare : KeepsRows (Letters.bare (W₀ := W₀) (Rc := Rc) (Ky := Ky) (Tr := Tr)
    (X₀ := X₀) (X := X) F Bk) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- So do the letters of the three chains' threads. -/
theorem keepsRows_ofThreads
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    KeepsRows (Letters.ofThreads F T₁ T₂ T₃ S₁ S₂ S₃) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable {L : Letters F Bk W₀ Rc Ky Tr X₀ X} (hL : KeepsRows L)
  (R : Rows W₀ Rc Xi Ky Tr X₀ X) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
  (f₃ : List (Fall F.S₃))
include hL

/-- **A list of the first chain, its letters forgotten, is a row.** -/
theorem first_socket : ∀ M ∈ (theSides F L R f₁ f₂ f₃).first, M.bare ∈ R.first := by
  intro M hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [hL.1 r]
  exact hr

/-- **The same in the shared chain.** -/
theorem shared_socket : ∀ M ∈ (theSides F L R f₁ f₂ f₃).shared, M.bare ∈ R.shared := by
  intro M hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [hL.2.1 r]
  exact hr

/-- **The same in the last chain.** -/
theorem second_socket : ∀ M ∈ (theSides F L R f₁ f₂ f₃).second, M.bare ∈ R.second := by
  intro M hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [hL.2.2 r]
  exact hr

omit hL

section Slot
variable {W₀ Rc Tr X₀ X : Type} {F : FileDescription ProofFile.Inst} {Bk : ProverCoinCounts}
  {L : Letters F Bk W₀ Rc OnBytes.TableKey Tr X₀ X} {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : ProofFile.Pub}
  {Gr : ProofFile.Ground}

/-- **At overlaySlots a list of the first chain of the kind κ is a row of the lot filled in for that
kind**, where the filling's lots of other names have no side of that kind. -/
theorem filled_slot (hL : KeepsRows L)
    (mine : List (SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (named : ∀ s ∈ mine, P.lots.any (fun M => M.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ M ∈ P.lots, ∀ s, (mine.find? fun s => s.name == M.name) = some s →
      (s.rows Z Gr).map (·.half) = M.halves Z Gr)
    (shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey))
    (hs : shared.map (·.half) = P.shared Z Gr)
    (second : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (h₃ : second.map (·.half) = P.second Z Gr) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
    (f₃ : List (Fall F.S₃))
    {lot : SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst} (hlot : lot ∈ mine)
    {κ : KindName}
    (hkinds : ∀ M ∈ P.lots, M.name ≠ lot.name → ∀ g ∈ M.halves Z Gr, g.place.kind ≠ κ) :
    ∀ M ∈ (theSides F L (overlaySlots P Z Gr mine named apart hm shared hs second h₃).rows f₁ f₂
      f₃).first, M.place.kind = κ → M.bare ∈ lot.rows Z Gr := by
  intro M hM hk
  have hb := first_socket hL _ f₁ f₂ f₃ M hM
  obtain ⟨l, hl, hr⟩ := List.mem_flatMap.1 hb
  obtain ⟨Lt, hLt, rfl⟩ := List.mem_map.1 hl
  by_cases e : Lt.name = lot.name
  · have f : (mine.find? fun s => s.name == Lt.name) = some lot := by
      rw [e]
      exact OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mine apart lot hlot
    have eo : overlayLot mine Lt = lot := by
      unfold overlayLot
      rw [f]
    rw [eo] at hr
    exact hr
  · exfalso
    have hh : M.bare.half ∈ Lt.halves Z Gr := by
      rw [← overlay_half (hm Lt hLt)]
      exact List.mem_map_of_mem hr
    exact hkinds Lt hLt e _ hh hk

end Slot

end AtFullSide.K12

#print axioms AtFullSide.K12.KeepsRows
#print axioms AtFullSide.K12.keepsRows_bare
#print axioms AtFullSide.K12.keepsRows_ofThreads
#print axioms AtFullSide.K12.first_socket
#print axioms AtFullSide.K12.shared_socket
#print axioms AtFullSide.K12.second_socket
#print axioms AtFullSide.K12.filled_slot
