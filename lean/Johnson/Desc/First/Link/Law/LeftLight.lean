-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LeftLight.lean: THREE OF THE NINE FIELDS OF
`LeftAsks` (LeftThree.lean beside this file), AND ITS PREMISE "A PART IS THERE", OUT OF hLeft's OWN
HYPOTHESES (WorthLeft.lean) AND THE CLAUSE okDig. Theorems. A law file; no running text imports it.
  `part_of_fx`      Fx9 φ Ok (fixed9 φ s) t · atS.get? t = some b ⊢ a part pa is there at s;
                    b.L.arrayOf = pa.L.arrayOf (LeftAsks.arrays); b's ledger is later than pa's (so
                    it has its number of slots).
  `first_of_static`   DigStatic tlD tl F ⊢ each piece's first column is its call's, AT tlD
                    (LeftAsks.first).
  `filled_lt`       a filled slot of a ledger that has its sizes lies below its number of slots.
  `slots_of`        LeftAsks.slots from: pa's ledger has its sizes · every slot that a form of the
                    first four claims names lies in the window of the heard leaves' sumcheck, or is
                    filled in pa's ledger (hOk4's own end,
                    Johnson/Desc/First/Link/Law/WorthAtFront.lean) · THE WINDOW ENDS BELOW THE
                    NUMBER OF SLOTS.
  `slots_of_full`   the same from the full state's ledger: it is later than pa's, has its sizes, and
                    every slot that a form of the first four claims names is filled in it.

Limits. "The window ends below the number of slots" (slots_of) is a premise: paid by nobody here,
and whether the heard leaves' window lies inside the front's ledger at an
honest run has not been read or run. slots_of_full asks in its place "filled at the full state".
That the first four claims are those of which hOk4 speaks (four8 at the fixed structure) is the
caller's. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.LeftThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Values (winOf)

/-- Where t goes on from what is fixed at s: a part is there at s, with t's part's list of arrays.
-/
theorem part_of_fx {α : Type} {φ : S → α} {Ok : α × Option Pub9 → Prop} {s t : S} {b : K9.Part}
    (fx : Fx9 φ Ok (fixed9 φ s) t) (hb : atS.get? t = some b) :
    ∃ pa, atS.get? s = some pa ∧ b.L.arrayOf = pa.L.arrayOf ∧ Later pa.F b.F := by
  obtain ⟨_, _, u, b', hu, hb', G⟩ := fx
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  obtain ⟨pa, hpa, rfl⟩ := Option.map_eq_some_iff.1 hu
  exact ⟨pa, hpa, G.2.2.2.1, G.1⟩

/-- Each piece's first column is its call's, at the plan's structure. -/
theorem first_of_static {tlD tl : HTailF2} {F : Fork} (h : DigStatic tlD tl F) :
    ∀ q < 2, ∀ p ∈ piecesL tlD q, p.c0 = q * tlD.mz := by
  intro q hq p hp
  have e : tl.zOf q = tlD.zOf q := by
    unfold HTailF2.zOf
    rw [h.same.z1, h.same.z2]
  have hp' : p ∈ piecesL tl q := by
    unfold piecesL at hp ⊢
    rw [e]
    exact hp
  rw [(h.pieces q hq p hp').c0, h.same.mz]

theorem filled_lt {F : Fork} {j : ℕ} (hS : Sized F) (h : Filled F j) : j < F.ns := by
  by_contra hn
  unfold Filled at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [hS.2.2]; omega)] at h
  cases h

/-- The slots that the first four claims' forms name lie below the number of slots. -/
theorem slots_of {pa : K9.Part} {g : Forest.Heard} {c : List Claim} (hS : Sized pa.F)
    (h : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList,
      K4Values.InWin (winOf g.leaves) s.1 ∨ Filled pa.F s.1)
    (hw : (winOf g.leaves).1 + (winOf g.leaves).2 ≤ pa.F.ns) :
    ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList, s.1 < pa.F.ns := by
  intro k hk s hs
  rcases h k hk s hs with w | f
  · exact Nat.lt_of_lt_of_le w.2 hw
  · exact filled_lt hS f

/-- The same from the FULL state's ledger: every named slot is filled there. -/
theorem slots_of_full {pa b : K9.Part} {c : List Claim} (hL : Later pa.F b.F) (hS : Sized b.F)
    (h : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList, Filled b.F s.1) :
    ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList, s.1 < pa.F.ns := by
  intro k hk s hs
  rw [← hL.ns]
  exact filled_lt hS (h k hk s hs)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.slots_of_full
#print axioms VerifiableInference.Desc.LinkJoin.part_of_fx
#print axioms VerifiableInference.Desc.LinkJoin.first_of_static
#print axioms VerifiableInference.Desc.LinkJoin.slots_of
