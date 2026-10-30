-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/ClearKept.lean: the code switch: NO COLLISION AT A KEPT MEMBER's OWN
COMMITTED WORD, AT A SEED WITH THE HELD SEED's VALUES, FROM THE TABLE OF JOINTS' PROMISE: the
collisions' twin of KeptDec.lean's pin_kept.
  clear_kept   where the table's «no collision» (CfAt, at its named reader of OOD samples)
               holds at a member x of the table's list that is alike to the typed kept member: there
               is a seed with the held seed's values at which the typed member's word, as wordAt
               (Sound/MsgSig.lean) makes it, has no collision. By cf_move (Sound/PinMove.lean) and
               smpNamed_bySeat (Sound/SmpNamed.lean), and HeldIsNamed.lean's held_is_named
  clear_of_promise  the same from the table's own «noColl» at the seat (Sound/MeaningSig.lean's
               noCollJT)
WHAT IT IS FOR. It is the premise hc of keptFree_of (K2Caller/KeptFreeOf.lean:
not imported), which turns it, with SlotWord.lean's slot_word, into the law's condition in front «no
held slot of the open word has a collision».
LIMITS. hz is held_is_named's conclusion, taken as a premise. Nothing is shown at a real value. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.HeldIsNamed
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Cb
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (wordAt CfAt Mem Alike SitsAt noCollJT cf_move smpNamed
  smpNamed_bySeat)

variable {r : SwRow} {Xi P : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (seats : List (ℕ × ℕ))

theorem clear_kept (a : P × VerifiableInference.Desc.First.S) (y : Strs) (i : Fin r.lo.length)
    (σ : ((sigOf r.cs r.lo).om i).Smp)
    (hz : ∃ z, smpNamed r.cs seats a ⟨r.lo, seat⟩ i = some z ∧
      ((sigOf r.cs r.lo).om i).Z.val z.1 = ((sigOf r.cs r.lo).om i).Z.val σ.1 ∧ z.2 = σ.2)
    (x : Mem) (hA : Alike x ⟨⟨r.lo, seat⟩, i⟩)
    (hcf : CfAt G r.cs x.1.l x.1.seat (fun b => smpNamed r.cs seats b x.1) x.2 a y) :
    ∃ ρ, ((sigOf r.cs r.lo).om i).Z.val ρ = ((sigOf r.cs r.lo).om i).Z.val σ.1 ∧
      ¬ ((sigOf r.cs r.lo).om i).Clash (wordAt G r.cs r.lo seat y i) ρ := by
  obtain ⟨z, z1, z2, -⟩ := hz
  obtain ⟨z', c1, -, c3⟩ := (cf_move r.cs G (smpNamed r.cs seats) x ⟨⟨r.lo, seat⟩, i⟩ hA a
    (smpNamed_bySeat r.cs seats a x ⟨⟨r.lo, seat⟩, i⟩ hA) y).1 hcf
  have e : z' = z := Option.some.inj (c1.symm.trans z1)
  subst e
  exact ⟨z'.1, z2, c3⟩

theorem clear_of_promise (a : P × VerifiableInference.Desc.First.S) (y : Strs)
    (i : Fin r.lo.length) (σ : ((sigOf r.cs r.lo).om i).Smp)
    (hz : ∃ z, smpNamed r.cs seats a ⟨r.lo, seat⟩ i = some z ∧
      ((sigOf r.cs r.lo).om i).Z.val z.1 = ((sigOf r.cs r.lo).om i).Z.val σ.1 ∧ z.2 = σ.2)
    (ms : List Mem) (q : ℕ × ℕ) (hn : noCollJT r.cs G (smpNamed r.cs seats) ms q.1 q.2 a y)
    (x : Mem) (hx : x ∈ ms) (hq : SitsAt x q.1 q.2) (hA : Alike x ⟨⟨r.lo, seat⟩, i⟩) :
    ∃ ρ, ((sigOf r.cs r.lo).om i).Z.val ρ = ((sigOf r.cs r.lo).om i).Z.val σ.1 ∧
      ¬ ((sigOf r.cs r.lo).om i).Clash (wordAt G r.cs r.lo seat y i) ρ :=
  clear_kept G seat seats a y i σ hz x hA (hn x hx hq)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.clear_kept
#print axioms VerifiableInference.Desc.First.K2Caller.clear_of_promise
