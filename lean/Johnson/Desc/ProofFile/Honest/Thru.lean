-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thru.lean: part of no list. A prover's input read through a
pair of total functions, `g` on the index and `rd` on the stored tables' pads and encoding
randomness; and parts, prover's sides and lots read through readers of their inputs, by `Part.lift`
(Honest/Frame.lean) at the identity as lens: the own state stays. Definitions with code, and one
law: a lift read through is a lift (`Part.lift_thru`).

  1  `Local.thru`, `Common.thru`   the two inputs
  2  `Part.thru`, `Placed.thru`, `HLot.thru`; `HLot.ext'`, `Move.lift_thru`, `Part.lift_thru`

Kin. FrontRoad/ProverThroughSpec.lean has definitions of this make at a partial reader of the
index with a default (`localThrough`, `commonThrough`, `partThrough`, `halfThrough` and others),
above where this file has to stand.


Limits.
  * `g` and `rd` are total. Nothing is asked of them.
  * Nothing here is said of `play`, `ready`, `runC`, `Good` or `Owed` at what is read through.
  * The law proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ W₀' Rc Rc' Xi Ky Tr : Type}

/-! ## 1 The inputs -/

/-- The input of the first or the second chain, read through: the index by `g`, the stored tables'
pads and encoding randomness by `rd`; the public instance and the trace stay. -/
def Local.thru (g : W₀' → W₀) (rd : Rc' → Rc) (w : Local W₀' Rc' Xi Tr) : Local W₀ Rc Xi Tr :=
  ⟨g w.w₀, rd w.rc, w.x, w.trace⟩

/-- The shared chain's input, read through; the key stays. -/
def Common.thru (g : W₀' → W₀) (rd : Rc' → Rc) (w : Common W₀' Rc' Ky) : Common W₀ Rc Ky :=
  ⟨g w.w₀, rd w.rc, w.key⟩

/-! ## 2 Parts, prover's sides, lots -/

section
variable {V V' V'' W W' W'' X Y : Type}

/-- **A part read through**: `Part.lift` at readers of what the second stop may read and of the
input; the own state stays (the identity as lens). -/
def Part.thru (see : V' → V) (wit : W' → W) (p : Part V W X) : Part V' W' X :=
  p.lift see wit id fun _ y => y

/-- A prover's side read through: its place stays. -/
def Placed.thru (see : V' → V) (wit : W' → W) (h : Placed V W X) : Placed V' W' X :=
  ⟨h.place, h.parts.map (Part.thru see wit)⟩

/-- A lot's honest side read through: its name stays. -/
def HLot.thru (see : V' → V) (wit : W' → W) (L : HLot V W X) : HLot V' W' X :=
  ⟨L.name, fun Z G => (L.halves Z G).map (Placed.thru see wit)⟩

/-- Two lots' honest sides with one name and the same sides are one. -/
theorem HLot.ext' {L L' : HLot V W X} (hn : L.name = L'.name) (hh : L.halves = L'.halves) :
    L = L' := by
  cases L
  cases L'
  dsimp only at hn hh
  subst hn
  subst hh
  rfl

/-- A lift of a lifted move is a lift, at the readers composed. `get`, `set`: any. -/
theorem Move.lift_thru {C : Type} (wit' : W'' → W') (wit : W' → W) (get : X → Y)
    (set : X → Y → X) (mv : Move C W Y) :
    Move.lift wit' id (fun _ y => y) (Move.lift wit get set mv) =
      Move.lift (wit ∘ wit') get set mv := rfl

/-- **A lift read through is a lift**, at the readers composed; the inner lift's lens stays. -/
theorem Part.lift_thru (see' : V'' → V') (wit' : W'' → W') (see : V' → V) (wit : W' → W)
    (get : X → Y) (set : X → Y → X) (p : Part V W Y) :
    (p.lift see wit get set).thru see' wit' = p.lift (see ∘ see') (wit ∘ wit') get set := by
  unfold Part.thru Part.lift
  simp only [List.map_map]
  rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Local.thru
#print axioms ProofFile.Honest.Common.thru
#print axioms ProofFile.Honest.Part.thru
#print axioms ProofFile.Honest.Placed.thru
#print axioms ProofFile.Honest.HLot.thru
#print axioms ProofFile.Honest.HLot.ext'
#print axioms ProofFile.Honest.Move.lift_thru
#print axioms ProofFile.Honest.Part.lift_thru
