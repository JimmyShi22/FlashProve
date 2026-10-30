-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/ShiftKLists.lean.
The rounds and the errors of the shift and the whole lookup behind it, as lists.

`shHead several x` is [x] if theta is drawn and [] if not.
 * `lkK_ri`, `lkK_el`: for any block b behind the shift: its entries, its errors, with the shift's
   entry `shiftN wk`, its count 2 ^ P.d, before them, or as they are.
 * `allK_shape`: the rounds of `P.allK A0 several V VC` are the entries `shHead several (shiftN wk)
   ++ entN wk A0.v' A0.d A0.w A0.n`, in the sense of `ShapeIs`: each round sends as many bytes and
   draws as many elements, and as many of them not 0, as its entry says. The entry's name and its
   other words are tied to the round by nothing.
 * `allK_eps`: the errors are `shHead several (2 ^ P.d) ++ epsN A0.v' A0.d A0.w A0.n (card E)`.
 Both under the premise that the closing binds its variables from the last to the first (A0.oE =
   Fin.revPerm); `allK_shapeG`, `allK_epsG` hold for any order.
 * `allK_len`: one round more if and only if theta is drawn.

-/
import OnBytes.Tie.Pv.Lookup.Shift.ShiftK
import OnBytes.Tie.Pv.Lookup.Lists.TwLetter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4

/-- one entry more if and only if θ is drawn -/
def shHead {α : Type} (several : Bool) (x : α) : List α := if several then [x] else []

section
variable {E St J : Type} [Field E] [Fintype E] {Ex : ExtSpec}

theorem bkK_ri (P : ShiftQ E St (J → E)) (wk : Nat) : RI E (P.bkK Ex) [shiftN wk] :=
  ri_draw1 Prod.mk (2 ^ P.d) wk "LKP shift"
theorem bkK_el (P : ShiftQ E St (J → E)) : EL (P.bkK Ex) [2 ^ P.d] := el_draw Prod.mk (2 ^ P.d)

theorem lkK_ri (P : ShiftQ E St (J → E)) {Xo : Type} (several : Bool) (b : BkK (St × E) Xo Ex)
    (wk : Nat) {ds : List Fmt.Entry} (h : RI E b ds) :
    RI E (P.lkK several b) (shHead several (shiftN wk) ++ ds) := by
  cases several with
  | true => exact ri_seq (bkK_ri P wk) h
  | false => exact ri_preM h _

theorem lkK_el (P : ShiftQ E St (J → E)) {Xo : Type} (several : Bool) (b : BkK (St × E) Xo Ex)
    {es : List Nat} (h : EL b es) : EL (P.lkK several b) (shHead several (2 ^ P.d) ++ es) := by
  cases several with
  | true => exact el_seq (bkK_el P) h
  | false => exact el_preM h _

end

section
variable {E St : Type} [Field E] [Fintype E]
variable (V : ∀ (Y : PscPar E) Ex, TWhole.ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, TWhole.ShortKC Y
    Ex)
  (Ex : ExtSpec) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E)) (several : Bool)

/-- The rounds, at any order of the closing's variables. -/
theorem allK_shapeG (wk : Nat) :
    ShapeIs E (P.allK A0 several V VC (Ex := Ex)).R.shape
      (shHead several (shiftN wk) ++
        entG wk A0.v' A0.d A0.w A0.n (List.ofFn (dgEnd A0.w A0.d A0.oE))) :=
  lkK_ri P several _ wk (asmV_shape V VC Ex (P.asmH A0) wk)

/-- The errors, at any order of the closing's variables. -/
theorem allK_epsG :
    TWhole.errList (P.allK A0 several V VC (Ex := Ex)).e =
      shHead several (2 ^ P.d) ++
        epsG A0.v' A0.d A0.w A0.n (Fintype.card E) (List.ofFn (dgEnd A0.w A0.d A0.oE)) :=
  lkK_el P several _ (asmV_eps V VC Ex (P.asmH A0))

/-- The rounds. -/
theorem allK_shape (wk : Nat) (ho : A0.oE = Fin.revPerm) :
    ShapeIs E (P.allK A0 several V VC (Ex := Ex)).R.shape
      (shHead several (shiftN wk) ++ entN wk A0.v' A0.d A0.w A0.n) :=
  lkK_ri P several _ wk (asmV_shape_port V VC Ex (P.asmH A0) wk ho)

/-- The errors. -/
theorem allK_eps (ho : A0.oE = Fin.revPerm) :
    TWhole.errList (P.allK A0 several V VC (Ex := Ex)).e =
      shHead several (2 ^ P.d) ++ epsN A0.v' A0.d A0.w A0.n (Fintype.card E) :=
  lkK_el P several _ (asmV_eps_port V VC Ex (P.asmH A0) ho)

/-- One round more if and only if θ is drawn. -/
theorem allK_len :
    (P.allK A0 several V VC (Ex := Ex)).R.shape.length =
      (if several then 1 else 0) + ((P.asmH A0).baseK V VC (Ex := Ex)).R.shape.length := by
  cases several with
  | true => exact (Nat.add_comm _ _)
  | false => exact (Nat.zero_add _).symm

end
end TwRound
