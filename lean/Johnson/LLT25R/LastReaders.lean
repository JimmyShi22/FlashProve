-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastReaders.lean: THE LEDGER's READER OF OOD SAMPLES AT THE TWO TABLES' OWN
READERS: what `Readers₃` (LastOwedCore.lean) asks, at the state's level, where smp₁ is
`smpNamed cs seats` (Johnson/Desc/Sound/SmpNamed.lean: the
kind's own reading at the number seats.idxOf ‹the member's seat›) and smp₂ is `smpSt cs oNo stSh`
(Johnson/Desc/Sound/SmpShared.lean: the same reading at the number oNo ‹the member›). Two lemmas,
one definition.
  `SeatsNumber seats B`: a fact on a book: whichever message number i sits, by B, at a seat w: w is
    on the list and stands there at place i.
  `smpLast_elder`: at a member x whose seat is not Omega's: the ledger's reader is `K1.smpAt` off
    what the first chain hands on, AT ANY NUMBER i THAT SITS AT x's SEAT BY THE HANDED BOOK: from
    `SeatsNumber seats` of that book.
  `smpLast_omega`: at a member x at Omega's seat: it is `K1.smpAt` off the shared chain's last state
    at the number oNo x.
Limits. `SeatsNumber` is a premise: a fact on the first chain's last state. Nothing on soundness.

-/
import Johnson.LLT25R.LastMine
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.SmpShared
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Third (firstOfS FirstEnd₃)
open _root_.Desc.K14 (St)

/-- **The book numbers the messages as the list of seats does.** -/
def SeatsNumber (seats : List (ℕ × ℕ)) (B : TreeBook) : Prop :=
  ∀ i w, seatBy noFirst B i = some w → w ∈ seats ∧ seats.idxOf w = i

variable {P S₁ P₀ S₃' : Type} (cs : Codes) (get : P × S₁ → P₀ × First.S) (Ns : NumbersS)

/-- **At an elder member.** -/
theorem smpLast_elder (seats : List (ℕ × ℕ))
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (a : (P × S₁ × St) × S₃') (x : Mem) (hne : seatOf x ≠ Ns.tenant .oOmega) (f : FirstEnd₃)
    (hf : firstOfS (get (a.1.1, a.1.2.1)).2 = some f) (i : ℕ)
    (hi : seatBy noFirst f.book i = some (seatOf x)) (hS : SeatsNumber seats f.book) :
    smpLast cs (smpNamed cs seats) smp₂ get Ns a x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 f.st i := by
  obtain ⟨hm, hx⟩ := hS i _ hi
  have est : f.st = (get (a.1.1, a.1.2.1)).2.st := by
    unfold firstOfS at hf
    obtain ⟨e', -, rfl⟩ := Option.map_eq_some_iff.1 hf
    rfl
  unfold smpLast
  rw [if_neg (show ¬ x.1.seat x.2 = Ns.tenant .oOmega from hne), smpNamed_at cs seats _ x.1 x.2 hm,
      est]
  show K1.smpAt cs _ _ _ (seats.idxOf (seatOf x)) = _
  rw [hx]

/-- **At Omega.** -/
theorem smpLast_omega (oNo : Mem → ℕ)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (a : (P × S₁ × St) × S₃') (x : Mem) (he : seatOf x = Ns.tenant .oOmega) :
    smpLast cs smp₁ (smpSt cs oNo stSh) get Ns a x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.1.2.2.st (oNo x) := by
  unfold smpLast
  rw [if_pos (show x.1.seat x.2 = Ns.tenant .oOmega from he)]
  rfl

end LLT25

#print axioms LLT25.smpLast_elder
#print axioms LLT25.smpLast_omega
