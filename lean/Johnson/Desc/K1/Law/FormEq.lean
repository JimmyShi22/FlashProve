-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/FormEq.lean: the kind's sample row is the row that the verifier program's own
function makes (OnBytes/Iop/Send.lean: Send.form), with the answer as its target: an equation of
rows, for every shape and every number of answers.

Main names: cube_hasMain, cube_hasMask, cube_mainBits, cube_maskBits, cube_bits (the program's cube
of a shape has the message's numbers); front_cube; ten_main, ten_mask; form_eq; FormLaw, formLaw,
emptyRow_fails_form (the equation's form, general in the function that makes the row; the kind's own
meets it; one that makes the empty row fails it, at a shape that has the three premises).
Pure functions of the verifier program are named: Send.cube, Send.pad, Send.front, Send.form.

What is not claimed. The premise that every code's message length is a power of two is used: the
kind's rows count a row's places by 2 ^ logEll, the program by the length itself. Nothing on the
program's routine that calls Send.form. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.PadTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable (codes : Codes) (s : OracleShape)

theorem cube_hasMain : (Send.cube codes s).hasMain = ((Msg.of codes s).K != 0) := by
  show decide (0 < s.mainRows) = (s.mainRows != 0)
  by_cases h : s.mainRows = 0 <;> simp [h, Nat.pos_iff_ne_zero]

theorem cube_hasMask : (Send.cube codes s).hasMask = ((Msg.of codes s).Kzk != 0) := by
  show decide (0 < s.maskRows) = (s.maskRows != 0)
  by_cases h : s.maskRows = 0 <;> simp [h, Nat.pos_iff_ne_zero]

theorem cube_mainBits : (Send.cube codes s).mainBits = (Msg.of codes s).mainBits := by
  by_cases h : s.mainRows = 0
  · simp [Send.cube, Msg.mainBits, Msg.of, h]
  · have hcl : ∀ n, clog n = ceilLog2 n := fun _ => rfl
    simp [Send.cube, Msg.mainBits, Msg.of, h, Nat.pos_iff_ne_zero, hcl]

theorem cube_maskBits : (Send.cube codes s).maskBits = (Msg.of codes s).maskBits := by
  by_cases h : s.maskRows = 0
  · simp [Send.cube, Msg.maskBits, Msg.of, h]
  · have hcl : ∀ n, clog n = ceilLog2 n := fun _ => rfl
    simp [Send.cube, Msg.maskBits, Msg.of, h, Nat.pos_iff_ne_zero, hcl]

theorem cube_bits : (Send.cube codes s).bits = (Msg.of codes s).v := by
  have a := cube_mainBits codes s
  have b := cube_maskBits codes s
  have c := cube_hasMain codes s
  have d := cube_hasMask codes s
  show (if (Send.cube codes s).hasMain && (Send.cube codes s).hasMask then
    max (Send.cube codes s).mainBits (Send.cube codes s).maskBits + 1
    else (Send.cube codes s).mainBits + (Send.cube codes s).maskBits) = _
  rw [a, b, c, d]
  rfl

/-- The program's front factor at the program's cube is the kind's. -/
theorem front_cube (z : List E) (tb : Nat) (mask : Bool) :
    Send.front z (Send.cube codes s) tb mask = (Msg.of codes s).front z tb mask := by
  rw [Msg.front_eq]
  unfold Send.front
  rw [cube_hasMain, cube_hasMask, cube_bits]
  rfl

theorem ten_main (z : List E) :
    Tensor.eq (z.take (Send.cube codes s).mainBits)
      (Send.front z (Send.cube codes s) (Send.cube codes s).mainBits false) =
        (Msg.of codes s).ten z .main := by
  rw [front_cube, cube_mainBits]
  rfl

theorem ten_mask (z : List E) :
    Tensor.eq (z.take (Send.cube codes s).maskBits)
      (Send.front z (Send.cube codes s) (Send.cube codes s).maskBits true) =
        (Msg.of codes s).ten z .mask := by
  rw [front_cube, cube_maskBits]
  rfl

/-- A place of a message's pads, in the program's record. -/
def placeOf (m : Msg) (x : Nat × Nat × Nat) : PadPlace :=
  { part := m.padPart, index := x.2.1, answer := x.1, basis := thetaE x.2.2 }

/-- **The kind's sample row is the program's row with the answer as its target.** -/
theorem form_eq (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) (hl : codes.lengthsOk = true)
    (hs : Blk.shapeOk codes s = true) (hp : (Msg.of codes s).padFits = true) :
    (Send.form codes s o ⟨z, β⟩ i).map (fun r => { r with target := y }) =
      some (sampleRow (Msg.of codes s) o z β i y) := by
  have hstep : ∀ (l : List (Nat × Nat × Nat)) (r : OnBytes.Row),
      (l.map (placeOf (Msg.of codes s))).foldl (fun (r : OnBytes.Row) p =>
          r.addUnit o p.part p.index
            (subE (if p.answer == i then mulE β p.basis else zeroE)
              ((if p.part == .main then (Msg.of codes s).ten z .main
                else (Msg.of codes s).ten z .mask).entry p.index))) r =
        l.foldl ((Msg.of codes s).padStep o z β i) r := by
    intro l r
    rw [List.foldl_map]
    congr 1
    funext r x
    unfold Msg.padStep placeOf
    cases hq : (Msg.of codes s).padPart <;> rfl
  unfold Send.form
  have hpad : Send.pad codes s = some ((Msg.of codes s).pads.map (placeOf (Msg.of codes s))) :=
    pad_places codes s hl hs hp
  simp only [hpad, ten_main, ten_mask, cube_hasMain, cube_hasMask, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_some, hstep]
  rw [sampleRow_eq]
  unfold Msg.row₀
  cases h1 : ((Msg.of codes s).K != 0) <;> cases h2 : ((Msg.of codes s).Kzk != 0) <;> rfl

/-- The equation's form, general in the function that makes the row. -/
def FormLaw (row : Msg → Nat → List E → E → Nat → E → OnBytes.Row) : Prop :=
  ∀ (codes : Codes) (s : OracleShape) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E),
    codes.lengthsOk = true → Blk.shapeOk codes s = true → (Msg.of codes s).padFits = true →
    (Send.form codes s o ⟨z, β⟩ i).map (fun r => { r with target := y }) =
      some (row (Msg.of codes s) o z β i y)

theorem formLaw : FormLaw sampleRow :=
  fun codes s o z β i y hl hs hp => form_eq codes s o z β i y hl hs hp

/-- A function that makes the empty row fails the equation: the program's row has the answer as its
target. -/
theorem emptyRow_fails_form : ¬ FormLaw fun _ _ _ _ _ _ => {} := by
  intro h
  have hs : Blk.shapeOk toyP.codes { code := 0, mainRows := 1, mainDeg := 3, answers := 1 } =
      true := by simp [toyP, Blk.shapeOk]
  have hp : (Msg.of toyP.codes
      { code := 0, mainRows := 1, mainDeg := 3, answers := 1 }).padFits = true := by
    simp only [Msg.padFits, Msg.of, Msg.e, toyP]
    simp
    exact Nat.one_le_two_pow
  have e := h toyP.codes { code := 0, mainRows := 1, mainDeg := 3, answers := 1 } 0 []
    (E.ofTriple (1, 0, 0)) 0 (E.ofTriple (5, 0, 0)) toy_len hs hp
  rw [form_eq _ _ _ _ _ _ _ toy_len hs hp] at e
  have e2 := congrArg OnBytes.Row.target (Option.some.inj e)
  exact absurd e2 (by decide)

end VerifiableInference.Desc.K1
