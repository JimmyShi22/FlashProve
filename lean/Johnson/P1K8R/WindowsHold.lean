-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WindowsHold.lean: where the first chain does not stop, every combination lies in its
window, at every member whose half is pinned. The sender of the digits and the proximity test read
this fact.

  windows_hold   the statement at a chain

Limits. A statement on a list of halves. Nothing here bounds a measure.
-/
import Johnson.P1K8R.WindowSet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile.Honest
open ProofFile.Honest.K8 (smallFits cellsAtOf)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First.K8.Honest (leaves)
open OnBytes.FrontRoad (PinHalvesAt parOwn)

variable {W₀ Rc Xi Tr X S Cl : Type}

/-- **Where the chain does not stop, the windows hold.** -/
theorem windows_hold {Zp : ProofFile.Pub} {mats : ℕ → List (ℕ × String × ℕ)} {cells : Tr → Cells}
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) (u : Local W₀ Rc Xi Tr)
    (hpin : PinHalvesAt (parOwn Zp mats) cells hs bs.dropLast)
    (hfit : ∀ b ∈ bs.dropLast, ∀ P, parOwn Zp mats b.place = some P →
      smallFits P = true ∧ b.rounds.length = 1)
    (hlast : ∀ e, bs.getLast? = some e →
      (hs.find? fun h => h.place == e.place) = none ∧ parOwn Zp mats e.place = none)
    (loc ds : List Fmt.Drawn) (h : chainStopAt (some u) bs hs loc ds = none)
    (A B : List (Block S Cl)) (b : Block S Cl) (e : bs = A ++ b :: B)
    (P : VerifiableInference.Desc.First.K8.Par × List (ℕ × String × ℕ))
    (hp : parOwn Zp mats b.place = some P) (d : Fmt.Drawn)
    (hd : (ds.drop (drawsOf A)).head? = some d) :
    leaves P.1 (cellsAtOf (cells u.trace) P.2) d.trits.toArray = none := by
  have hA : chainStopAt (some u) A hs loc ds = none := by
    have h' := h
    rw [e, chainStop_append] at h'
    cases hx : chainStopAt (some u) A hs loc ds with
    | none => rfl
    | some z =>
      rw [hx] at h'
      cases h'
  cases hl : leaves P.1 (cellsAtOf (cells u.trace) P.2) d.trits.toArray with
  | none => rfl
  | some z =>
    have hf := (hid_first_iff hs bs u hpin hfit hlast loc ds).2
      ⟨A, b, B, P, d, e, hA, hp, hd, by rw [hl]; rfl⟩
    rw [h] at hf
    cases hf

end P1K8

#print axioms P1K8.windows_hold
