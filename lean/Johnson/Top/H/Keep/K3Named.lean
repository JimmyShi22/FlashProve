-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/K3Named.lean: The kind "lookup" (K3): WHAT THE FORMS THAT ITS DECIDE KEEPS NAME:
behind every yes of K3.block's decide from a ledger that has its sizes: every row, the key side's
end form, the form of the slot of the bits' shown value and the leaves' start form name no entry of
a virtual row, and slots alone that are there and filled in the ledger that decide lays. Statements
and proofs, over Johnson/Top/H/Keep/PadNamed.lean.

Main names:
  decide_named: of K3.block's decide, at any seat.
  PadNames.later: it passes to every later ledger.
  PadNames.noEntry: each row has no entry at all. PadNames.filled: each row meets the library's
    FilledA.

Limits. From a yes alone; "the ledger has its sizes" is a premise. The leaves' ROW is not among
these forms: the run "planes" makes it. Nothing on the forms that a calling kind hands in.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PadNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.PscRun

theorem PadNames.later {g : Forest.Heard} {F G : Fork} (h : PadNames g F) (hL : Later F G) :
    PadNames g G :=
  ⟨h.rows.later hL, h.cEnd.later hL, h.sBit.later hL, h.start.later hL⟩

/-- Each row has no entry at all. -/
theorem PadNames.noEntry {g : Forest.Heard} {F : Fork} (h : PadNames g F) :
    ∀ a ∈ g.rows.toList, a.ents = #[] := fun a ha => bare_ents (h.rows a ha).1

/-- Each row meets the library's "every slot that the form names is there and filled". -/
theorem PadNames.filled {g : Forest.Heard} {F : Fork} (h : PadNames g F) :
    ∀ a ∈ g.rows.toList, FilledA F a := fun a ha => (h.rows a ha).filledA

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide.** -/
theorem decide_named {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ seat.heard s = none ∧
      s' = seat.put s x.1 x.2 ∧ (Sized F → _root_.Fo.Tp.PadNames x.1 x.2) := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, hn, rfl, fun hS => ?_⟩
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      exact _root_.Fo.Tp.lkPad_named p.calls p.pub p.lid F x.2 t [] x.1 hl hS
    · exact absurd hx (by simp)

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.PadNames.noEntry
#print axioms VerifiableInference.OnPublicFiles.decide_named
