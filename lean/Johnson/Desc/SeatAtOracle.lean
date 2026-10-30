-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/SeatAtOracle.lean: the test on a seat (seatFaultAt, Johnson/Desc/SeatAt.lean)
finds no fault just where a test that reads THE DECLARED ORACLE ALONE accepts: of the IOP as written
in Lean it reads nothing but F.oracleAt j. A definition and one statement with its proof. A law
file; no running text imports it.
  fitsOrc codes s t orc?: the six comparisons of seatFaultAt, as a Bool, on what is declared of the
      tree
  none_of_six: six lists, each empty or of one, are empty together just where all six tests accept
  noFault_iff: (seatFaultAt F codes tag s j t).isNone = fitsOrc codes s t (F.oracleAt j)

Nothing on soundness.

-/
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The six comparisons, on what is declared of the tree. -/
def fitsOrc (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (t : Nat) : Option Oracle → Bool
  | none => false
  | some orc =>
    match orc.tenants[t]? with
    | none => false
    | some n =>
      (orc.logLength == longOf codes s) && (n.main == s.mainRows * s.mainDeg) &&
        (n.mask == s.maskRows * 3) &&
        (s.mainRows == 0 || (codes.base.getD s.code default).logN == longOf codes s) &&
        ((orc.tenants.map fun x => x.main + x.mask).sum == orc.words) &&
        (s.mainDeg == 1 || s.mainDeg == 3)

theorem none_of_six (c₁ c₂ c₃ c₄ c₅ c₆ : Bool) (x₁ x₂ x₃ x₄ x₅ x₆ : String)
    (f : List String → String) :
    (if (((if c₁ = true then [] else [x₁]) ++ (if c₂ = true then [] else [x₂]) ++
        (if c₃ = true then [] else [x₃]) ++ (if c₄ = true then [] else [x₄]) ++
        (if c₅ = true then [] else [x₅]) ++ (if c₆ = true then [] else [x₆])).isEmpty) = true
      then (none : Option String)
      else some (f ((if c₁ = true then [] else [x₁]) ++ (if c₂ = true then [] else [x₂]) ++
        (if c₃ = true then [] else [x₃]) ++ (if c₄ = true then [] else [x₄]) ++
        (if c₅ = true then [] else [x₅]) ++ (if c₆ = true then [] else [x₆])))).isNone =
      (c₁ && c₂ && c₃ && c₄ && c₅ && c₆) := by
  cases c₁ <;> cases c₂ <;> cases c₃ <;> cases c₄ <;> cases c₅ <;> cases c₆ <;> rfl

/-- **No fault, just where the declared oracle fits.** -/
theorem noFault_iff {Xi : Type} (F : FileDescription Xi) (codes : OnBytes.Codes) (tag : String)
    (s : OnBytes.OracleShape) (j t : Nat) :
    (seatFaultAt F codes tag s j t).isNone = fitsOrc codes s t (F.oracleAt j) := by
  unfold seatFaultAt
  cases F.oracleAt j with
  | none => rfl
  | some orc =>
    show (match orc.tenants[t]? with
      | none => _
      | some n => _ : Option String).isNone = (match orc.tenants[t]? with
      | none => false
      | some n => _)
    cases orc.tenants[t]? with
    | none => rfl
    | some n =>
      exact none_of_six (orc.logLength == longOf codes s) (n.main == s.mainRows * s.mainDeg)
        (n.mask == s.maskRows * 3)
        (s.mainRows == 0 || (codes.base.getD s.code default).logN == longOf codes s)
        ((orc.tenants.map fun x => x.main + x.mask).sum == orc.words)
        (s.mainDeg == 1 || s.mainDeg == 3) _ _ _ _ _ _
        (fun bad => s!"{tag}: tree {j} tenant {t} (answers {s.answers}): " ++
          "; ".intercalate bad)

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.noFault_iff
