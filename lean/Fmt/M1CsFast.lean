-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1CsFast.lean: the code switch of Fmt/M1Cs.lean in a form that an evaluation can afford at long
rows, with proofs that it is the same function.

`csStep` lays lists into arrays by `layAt`, which looks each entry up in the list, so its cost grows
with the square of a row's length. `layAtA` makes the list an array first. Definitions with code,
and equations with proofs.
Main names:
  `layAtA`, `csTwoA`, `csStepA`: the texts of `layAt`, of `csRows` at no draw and of `csStep`, over
    the array. `layAtA_eq`, `csTwoA_eq`, `csStepA_eq`: each is that function.
  `blocksA`: the first toy's six functions (`blocks`, Fmt/M1All.lean) with `csStepA` as the code
    switch. `blocksA_eq`: they are `blocks`.
Limits: that this form is faster is no theorem. Nothing on soundness.


-/
import Fmt.M1All

set_option autoImplicit false

namespace Fmt.M1

/-- `layAt` with the list made an array first. -/
def layAtA (n o : Nat) (w : List E) : Array E :=
  let a := w.toArray
  Array.ofFn (n := n) fun i => if o ≤ i.val then a.getD (i.val - o) Fld.zeroE else Fld.zeroE

theorem layAtA_eq (n o : Nat) (w : List E) : layAtA n o w = layAt n o w := by
  have key : ∀ j : Nat, w.toArray.getD j Fld.zeroE = w.getD j Fld.zeroE := fun j => by simp
  show Array.ofFn (n := n)
      (fun i => if o ≤ i.val then w.toArray.getD (i.val - o) Fld.zeroE else Fld.zeroE) =
    Array.ofFn (n := n) fun i => if o ≤ i.val then w.getD (i.val - o) Fld.zeroE else Fld.zeroE
  refine congrArg _ (funext fun i => ?_)
  rw [key]

/-- The two rows that `csRows` makes where no position is drawn: the carried claim and the sample
row. -/
def csTwoA (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) : List GRow :=
  let nM := 2 ^ new.k * new.C.l
  let nD := 2 ^ new.h * new.Z.l
  let carried : GRow :=
    ⟨layAtA nM 0 (fitL Fld.zeroE old.C.l s.c.toList),
      addV f (layAtA nD 0 (fitL Fld.zeroE old.Z.l s.d0.toList))
        (layAtA nD old.Z.l (fitL Fld.zeroE old.Z.l s.d1.toList)),
      s.t⟩
  let smp : GRow := ⟨layAtA nM 0 sample.c.toList, layAtA nD 0 sample.d.toList, sample.t⟩
  [carried, smp]

theorem csTwoA_eq (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (col : Nat → Option Col) :
    csRows f old new s sample [] col = some (csTwoA f old new s sample) := by
  unfold csRows csTwoA
  simp only [layAtA_eq]
  rfl

/-- `csStep` over `csTwoA`. -/
def csStepA (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List Nat)
    (theta : E) (col : Nat → Option Col) : Option GRow :=
  let g0 := sumRows f theta (csTwoA f old new s sample)
  (xs.foldl (fun (acc : Option (List E × List E × E × E)) x =>
    match acc, col x with
    | some st, some cl => some (addDraw f old theta s x cl st)
    | _, _ => none) (some (g0.c.toList, g0.d.toList, g0.t, f.mulE theta theta))).map
      fun st => ⟨st.1.toArray, st.2.1.toArray, st.2.2.1⟩

/-- **It is `csStep`.** -/
theorem csStepA_eq (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List Nat)
    (theta : E) (col : Nat → Option Col) :
    csStepA f old new s sample xs theta col = csStep f old new s sample xs theta col := by
  unfold csStepA csStep
  rw [csTwoA_eq]
  rfl

/-- The first toy's six functions with `csStepA` as the code switch. -/
def blocksA : Blocks := { blocks with cs := csStepA }

theorem blocksA_eq : blocksA = blocks := by
  unfold blocksA
  have h : csStepA = blocks.cs := by
    funext f old new s sample xs theta col
    exact csStepA_eq f old new s sample xs theta col
  rw [h]

end Fmt.M1

#print axioms Fmt.M1.csStepA_eq
#print axioms Fmt.M1.blocksA_eq
