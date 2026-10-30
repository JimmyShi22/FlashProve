-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LengthsOfShapes.lean: THE TWO EQUATIONS ON THE CODES' MESSAGE LENGTHS
AT A GROUP THAT HOLDS A WRITTEN LIST's MEMBERS: FROM `ShapesAre` (LayoutOfShapes.lean, beside this
file) AND ONE EQUATION: THE STATEMENT's TABLE OF CODES IS THE WRITTEN ONE. Statements and proofs.

Why. LengthsAt.lean draws the two equations from three on the statement, two of them on the GROUP's
own code numbers, which nobody shows of a verifier's state. But a group in order has its members'
codes' lengths (`LayFacts.main_places`, `mask_places`, Johnson/Desc/Means/Layout.lean), and the
members' shapes are the written ones.
  `placeBits_of_shape`: the bits of places of a message with a written shape that has rows of the
    part: the exponent of the shape's own code in the statement's table.
  `codesZero lo`: a test on a written list: some member bears the main code number 0; some member
    has a mask row and bears the mask code number 0. `written_codes`: it says yes at the written
    lists of the 25 and of the 5 links; IT CAN SAY NO: at the list behind them (the last test's
    first stage: one member, no mask row) it does: all by the kernel.
  `exps_of_shapes`: `codesZero lo`, `LayFacts T G L`, `ShapesAre T G lo kb no`: the layout's two
    exponents are those of the statement's codes number 0.
  `lengths_of_shapes_full`, `lengths_of_shapes_small`: lo the l-th written list, l < 25 (l < 5);
    T.codes = `codesFull2` (`codesSmall2`); `LayFacts T G L`; `ShapesAre T G lo kb no`; gs a group
    in front: 2 ^ L.logEll = gs.main.ell and 2 ^ L.logEllZk = gs.mask.ell. NOTHING IS ASKED OF THE
    GROUP's OWN TWO CODE NUMBERS.
Limits. `ShapesAre` and "the statement's table of codes is the written one" are shown of no
verifier's state here. `LayFacts` comes of "the group is in order" (`layFacts`). The last group is
not treated: there no member has a mask row, and the layout's second exponent hangs on the group's
own mask code number. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LengthsAt
import Johnson.Desc.First.Close.Law.LayoutOfShapes
import Johnson.Desc.Means.Layout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.G

/-- The bits of places of a message with a known shape. -/
theorem placeBits_of_shape {T : Statement} {o : ℕ} {sh : OracleShape}
    (h : (T.oracles[o]?).map (fun x : Oracle => x.shape) = some sh) :
    (sh.mainRows ≠ 0 → T.placeBits o .main = (T.codes.base.getD sh.code default).logEll) ∧
      (sh.maskRows ≠ 0 → T.placeBits o .mask = (T.codes.mask.getD sh.maskCode default).logEll) := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Statement.placeBits
  rw [hx]
  constructor
  · intro h0
    have : (x.shape.rows .main == 0) = false := by simpa [OracleShape.rows] using h0
    simp [this]
  · intro h0
    have : (x.shape.rows .mask == 0) = false := by simpa [OracleShape.rows] using h0
    simp [this]

/-- The test on a written list: a member under the main code 0; a member with a mask row under the
mask code 0. -/
def codesZero (lo : List (OracleShape × ℕ)) : Bool :=
  ((membersOf lo).any fun i => (lo.get i).1.code == 0) &&
    (membersOf lo).any fun i => (lo.get i).1.maskRows != 0 && (lo.get i).1.maskCode == 0

set_option maxRecDepth 100000 in
/-- So it is at the written lists of the 25 and of the 5 links; AT THE LIST BEHIND THEM (the last
test's first stage: one member, no mask row) THE TEST SAYS NO: by the kernel. -/
theorem written_codes :
    ((List.range 25).all fun l => codesZero (linksFullLit.getD l [])) = true ∧
    ((List.range 5).all fun l => codesZero (linksSmallLit.getD l [])) = true ∧
    codesZero (linksFullLit.getD 25 []) = false ∧ codesZero (linksSmallLit.getD 5 []) = false := by
  decide +kernel

section
variable {T : Statement} {G : Group} {L : GroupLayout} {lo : List (OracleShape × ℕ)}
  {kb : Fin lo.length → Bool} {no : Fin lo.length → ℕ}

/-- The layout's two exponents are those of the statement's codes number 0. -/
theorem exps_of_shapes (hz : codesZero lo = true) (Y : LayFacts T G L)
    (H : ShapesAre T G lo kb no) :
    L.logEll = (T.codes.base.getD 0 default).logEll ∧
      L.logEllZk = (T.codes.mask.getD 0 default).logEll := by
  unfold codesZero at hz
  obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ ▸ hz
  obtain ⟨i, hi, ci⟩ := List.any_eq_true.1 h1
  obtain ⟨j, hj, cj⟩ := List.any_eq_true.1 h2
  have ci' : (lo.get i).1.code = 0 := by simpa using ci
  have cj' : (lo.get j).1.maskRows ≠ 0 ∧ (lo.get j).1.maskCode = 0 := by simpa using cj
  have mi : (lo.get i).1.mainRows ≠ 0 := by
    unfold membersOf at hi
    simpa using hi
  have ini : no i ∈ G.members.toList := by rw [H.members]; exact List.mem_map_of_mem hi
  have inj : no j ∈ G.members.toList := by rw [H.members]; exact List.mem_map_of_mem hj
  have hasi : T.has (no i) .main = true := by
    rw [(has_of_shape (H.shape i hi) .main).1]
    exact decide_eq_true (Nat.pos_of_ne_zero mi)
  have hasj : T.has (no j) .mask = true := by
    rw [(has_of_shape (H.shape j hj) .mask).1]
    exact decide_eq_true (Nat.pos_of_ne_zero cj'.1)
  constructor
  · rw [← Y.main_places _ ini hasi, (placeBits_of_shape (H.shape i hi)).1 mi, ci']
  · rw [← Y.mask_places _ inj hasj, (placeBits_of_shape (H.shape j hj)).2 cj'.1, cj'.2]

/-- **At the full size's 25 links.** -/
theorem lengths_of_shapes_full {l : ℕ} (hl : l < 25) (hlo : lo = linksFullLit.getD l [])
    (hc : T.codes = codesFull2) (Y : LayFacts T G L) (H : ShapesAre T G lo kb no)
    {gs : GroupSize} (hgs : gs ∈ frontFull) :
    2 ^ L.logEll = gs.main.ell ∧ 2 ^ L.logEllZk = gs.mask.ell := by
  obtain ⟨e1, e2⟩ := exps_of_shapes
    (hlo ▸ List.all_eq_true.1 written_codes.1 l (List.mem_range.2 hl)) Y H
  rw [e1, e2, hc]
  exact ⟨(front_lengths.1 gs hgs).1, (front_lengths.1 gs hgs).2.1⟩

/-- **At the small size's 5 links.** -/
theorem lengths_of_shapes_small {l : ℕ} (hl : l < 5) (hlo : lo = linksSmallLit.getD l [])
    (hc : T.codes = codesSmall2) (Y : LayFacts T G L) (H : ShapesAre T G lo kb no)
    {gs : GroupSize} (hgs : gs ∈ frontSmall) :
    2 ^ L.logEll = gs.main.ell ∧ 2 ^ L.logEllZk = gs.mask.ell := by
  obtain ⟨e1, e2⟩ := exps_of_shapes
    (hlo ▸ List.all_eq_true.1 written_codes.2.1 l (List.mem_range.2 hl)) Y H
  rw [e1, e2, hc]
  exact ⟨(front_lengths.2 gs hgs).1, (front_lengths.2 gs hgs).2.1⟩

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.written_codes
#print axioms VerifiableInference.Desc.First.Close.exps_of_shapes
#print axioms VerifiableInference.Desc.First.Close.lengths_of_shapes_full
#print axioms VerifiableInference.Desc.First.Close.lengths_of_shapes_small
