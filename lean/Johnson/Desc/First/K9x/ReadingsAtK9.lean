-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/ReadingsAtK9.lean: THE TWO READINGS OF "HEARD" AT K9's OWN TEXT: what the
lookup on the calls (`S.lookHeard?`) and on the digits (`heardD`) was heard to return is left by
K9's lens when it lays a part; so K9's draw steps, and its batching calls, at both. Definitions and
theorems with their proofs.

CUT, TO THE LETTER, OUT OF Johnson/Desc/First/K9x/RanAtAdding.lean (not in this library), which held
them beside laws on K9's steps of adding as an earlier Block.lean's description seated them.
None of these steps is seated: THE ROAD IMPORTS
THIS FILE, NOT THAT ONE. THE TWO DECLARE THE SAME NAMES: THEY ARE NOT TO BE IMPORTED TOGETHER.

  `heardD` · `SetLeaves hd` · `setLeavesLook`, `setLeavesDigits` · `CF hd` · `preCF` ·
    `carriesSetG` · `drawStepsG`.
  New here: `callsK9G`: `Calls (CF hd) (QK9 atS p) (batch atS p)` at every place p and every
    reading that the lens leaves.

Limits. Frame's laws: no error; nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.CallsAtK9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.PscRun (Sized)

/-- The digits' seat's reading of what the lookup heard (K3Seat.lean: `seatDigits`). -/
def heardD (s : S) : Option Forest.Heard := s.tl?.bind (·.heard)

/-- A reading of "heard" that K9's lens leaves when it lays a part. -/
def SetLeaves (hd : S → Option Forest.Heard) : Prop := ∀ s q, hd (atS.set s q) = hd s

theorem setLeavesLook : SetLeaves S.lookHeard? := fun s q => by
  show ((s.putLink q.L).putFork q.F).lookHeard? = s.lookHeard?
  rw [S.look_putFork, S.look_putLink]

theorem tl_putLink' (s : S) (L : LinkCtx) : (s.putLink L).tl? = s.tl? := by
  unfold S.putLink
  split
  · rename_i a hh
    simp [S.tl?, hh]
  · rename_i a hh
    simp [S.tl?, hh]
  · rename_i a hh
    split
    · rename_i ho
      simp [S.tl?, hh, ho]
    · rfl
  · rfl

theorem tl_putFork' (s : S) (F : Fork) : (s.putFork F).tl? = s.tl? := by
  unfold S.putFork
  split
  · rename_i a hh
    simp [S.tl?, hh]
  · rename_i a hh
    simp [S.tl?, hh]
  · rename_i a hh
    split
    · rename_i ho
      simp [S.tl?, hh, ho]
    · rfl
  · rfl

theorem setLeavesDigits : SetLeaves heardD := fun s q => by
  show ((s.putLink q.L).putFork q.F).tl?.bind (·.heard) = s.tl?.bind (·.heard)
  rw [tl_putFork', tl_putLink']

variable (hd : S → Option Forest.Heard)

/-- What was heard, at the reading hd, stands; the ledger only grows, with its sizes. -/
abbrev CF : S → S → Prop := CarriesFo S.fork? hd

theorem preCF : Pre (CF hd) :=
  carriesPre _ _ _ _ _ _ _ _root_.Fo.Later.refl fun _ _ _ => _root_.Fo.Later.trans

/-- Laying a part whose ledger has the same slots carries, at every reading that the lens leaves. -/
theorem carriesSetG (hk : SetLeaves hd) (s : S) (q q' : Part) (h : atS.get? s = some q)
    (hs : OnBytes.PscRun.SlotsSame q.F q'.F) : CF hd s (atS.set s q') :=
  ⟨fun _ hg => (hk s q').trans hg, (carriesSetAtS s q q' h hs).2⟩

/-- K9's draw's block steps, at every reading that the lens leaves. -/
theorem drawStepsG {Cl : Type} (hk : SetLeaves hd) (p : Where) :
    (drawAlone (Cl := Cl) atS p).Steps (CF hd) := by
  intro t rs gs t' H
  match rs, H with
  | [r], H =>
    obtain ⟨s, hs, H⟩ := bindOk (x := atS.part t) H
    obtain ⟨chi, _, H⟩ := bindOk (x := chiOf r) H
    obtain ⟨o, ho, H⟩ := bindOk (x := drawnClean p.rows chi s.owed s.used s.L s.F) H
    rw [← Except.ok.inj H]
    exact carriesSetG hd hk t s _ (thereOk hs) (drawn_slots ho)

/-- **K9's batching's law at every reading that laying K9's part leaves.** -/
theorem callsK9G (hk : SetLeaves hd) (p : Where) : Calls (CF hd) (QK9 atS p) (batch atS p) :=
  callsK9 atS p (drawStepsG hd hk p) fun e s cls F' h₁ h₂ =>
    carriesSetG hd hk e s _ h₁ (addAll_slots cls s.F F' h₂)

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.setLeavesLook
#print axioms VerifiableInference.Desc.K9.tl_putLink'
#print axioms VerifiableInference.Desc.K9.tl_putFork'
#print axioms VerifiableInference.Desc.K9.setLeavesDigits
#print axioms VerifiableInference.Desc.K9.preCF
#print axioms VerifiableInference.Desc.K9.carriesSetG
#print axioms VerifiableInference.Desc.K9.drawStepsG
#print axioms VerifiableInference.Desc.K9.callsK9G
