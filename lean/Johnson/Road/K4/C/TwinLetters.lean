-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TwinLetters.lean.

What is here. THE LETTERS THAT THE LAYERS' MAKERS ONLY STORE: the three constants of the
normalisations in the shape, the counts of padding keys in the lookup's numbers, the scales, the
rotary table, the layout of the weights but for its column bits. Three definitions lay them into a
shape, a layout and the public parameters (setH, setY, setP). On variables, nothing evaluated: where
the first maker's twin returns, it returns at other constants the same layout with these constants
stored (base_letters); the fifth maker stores the letters likewise (pub_letters); the plan of a
group is the same at the letters as without them, by unfolding alone (planG_set), so the sixth maker
does not read them (plans_letters). The makers are numbered as withPlans
(Johnson/Road/K4/RowHead/Twins.lean) calls them: baseNoStops, Forest.shapeNoAsk, Forest.planeCols,
wsLayOf, Pub.of, plansG.

  `setH`, `setY`, `setP`   the letters laid in.
  `planG_set`   the plan of a group: an equation by unfolding.
  `bind_go`, `refuse_go`, `onOk_inv`, `onOk_go`   steps.
  **`base_letters`**, **`pub_letters`**, `plansFrom_letters`, **`plans_letters`**   the makers.

Not shown here. That a maker returns at any shape. Anything on the listing front. That the second
and the third maker read none of the letters: no statement says so here; the caller passes them by
unfolding. Nothing on the fourth maker (at_weights, Johnson/Road/K4/RowHead/ClosedJoin.lean).
No property is claimed.
-/
import Johnson.Road.K4.RowHead.Twins
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road (ok_of_refuse ok_of_bind)
open OnBytes.Road.K4 (clOf onOk)

/-- The three constants of the normalisations laid into a shape. -/
def setH (h : Shape) (e1 e2 eF : Nat) : Shape := { h with eps1 := e1, eps2 := e2, epsF := eF }

/-- They and the counts of padding keys laid into a layout. -/
def setY (y : Lay) (e1 e2 eF : Nat) (pub : Array Nat) : Lay :=
  { y with h := setH y.h e1 e2 eF, fo := { y.fo with pub := pub } }

/-- These, the scales, the rotary table and the layout of the weights, but for its column bits, laid
into the public parameters. -/
def setP (P : Pub) (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat)
    (W : WsLay) : Pub :=
  { P with
    y := setY P.y e1 e2 eF pub, sc := sc, rope := rope, wsLay := { W with lk := P.wsLay.lk } }

/-- The plan of a group is the same at the letters. -/
theorem planG_set (P : Pub) (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat)
    (W : WsLay) (g : Nat) (O : Option HPlan2) :
    planG (setP P e1 e2 eF pub sc rope W) g O = planG P g O := rfl

/-- A step that returns, and what follows it. -/
theorem bind_go {α β : Type} {x : Except String α} {f : α → Except String β} {a : α} {y : β}
    (e : x = .ok a) (h : f a = .ok y) : (x >>= f) = .ok y := by
  subst e
  exact h

/-- A test that does not refuse, and what follows it. -/
theorem refuse_go {β : Type} {b : Bool} {n : String} {f : Unit → Except String β} {y : β}
    (hb : b = false) (h : f () = .ok y) : (refuseIf b n >>= f) = .ok y := by
  subst hb
  exact h

/-- What a test at a returned value says where it holds. -/
theorem onOk_inv {ε α : Type} {x : Except ε α} {f : α → Bool} (h : onOk x f = true) :
    ∃ a, x = .ok a ∧ f a = true := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A test that holds at the value that is returned holds at the return. -/
theorem onOk_go {ε α : Type} {x : Except ε α} {f : α → Bool} {a : α} (e : x = .ok a)
    (h : f a = true) : onOk x f = true := by
  subst e
  exact h

/-- **THE FIRST MAKER's TWIN STORES THE THREE CONSTANTS AND READS NONE OF THEM**: where it returns,
it returns at other constants the same layout with these stored. -/
theorem base_letters {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : baseNoStops h pc = .ok y) (e1 e2 eF : Nat) :
    baseNoStops (setH h e1 e2 eF) pc = .ok { y with h := setH y.h e1 e2 eF } := by
  delta baseNoStops at hy ⊢
  obtain ⟨c1, hy⟩ := ok_of_refuse hy
  refine refuse_go c1 ?_
  obtain ⟨c2, hy⟩ := ok_of_refuse hy
  refine refuse_go c2 ?_
  obtain ⟨c3, hy⟩ := ok_of_refuse hy
  refine refuse_go c3 ?_
  obtain ⟨c4, hy⟩ := ok_of_refuse hy
  refine refuse_go c4 ?_
  obtain ⟨a5, b5, hy⟩ := ok_of_bind hy
  refine bind_go b5 ?_
  obtain ⟨c6, hy⟩ := ok_of_refuse hy
  refine refuse_go c6 ?_
  obtain ⟨c7, hy⟩ := ok_of_refuse hy
  refine refuse_go c7 ?_
  obtain ⟨c8, hy⟩ := ok_of_refuse hy
  refine refuse_go c8 ?_
  obtain ⟨c9, hy⟩ := ok_of_refuse hy
  refine refuse_go c9 ?_
  obtain ⟨c10, hy⟩ := ok_of_refuse hy
  refine refuse_go c10 ?_
  obtain ⟨c11, hy⟩ := ok_of_refuse hy
  refine refuse_go c11 ?_
  obtain ⟨c12, hy⟩ := ok_of_refuse hy
  refine refuse_go c12 ?_
  obtain ⟨c13, hy⟩ := ok_of_refuse hy
  refine refuse_go c13 ?_
  obtain ⟨c14, hy⟩ := ok_of_refuse hy
  refine refuse_go c14 ?_
  obtain ⟨c15, hy⟩ := ok_of_refuse hy
  refine refuse_go c15 ?_
  obtain ⟨c16, hy⟩ := ok_of_refuse hy
  refine refuse_go c16 ?_
  obtain ⟨c17, hy⟩ := ok_of_refuse hy
  refine refuse_go c17 ?_
  obtain ⟨c18, hy⟩ := ok_of_refuse hy
  refine refuse_go c18 ?_
  obtain ⟨c19, hy⟩ := ok_of_refuse hy
  refine refuse_go c19 ?_
  obtain ⟨c20, hy⟩ := ok_of_refuse hy
  refine refuse_go c20 ?_
  obtain ⟨c21, hy⟩ := ok_of_refuse hy
  refine refuse_go c21 ?_
  obtain ⟨c22, hy⟩ := ok_of_refuse hy
  refine refuse_go c22 ?_
  obtain ⟨c23, hy⟩ := ok_of_refuse hy
  refine refuse_go c23 ?_
  obtain ⟨c24, hy⟩ := ok_of_refuse hy
  refine refuse_go c24 ?_
  obtain ⟨a25, b25, hy⟩ := ok_of_bind hy
  refine bind_go b25 ?_
  obtain ⟨c26, hy⟩ := ok_of_refuse hy
  refine refuse_go c26 ?_
  obtain ⟨c27, hy⟩ := ok_of_refuse hy
  refine refuse_go c27 ?_
  obtain ⟨c28, hy⟩ := ok_of_refuse hy
  refine refuse_go c28 ?_
  cases hgt : gateTables h.eg h.smax h.p3 h.gcl with
  | mk silu fs =>
    have hgt' : gateTables (setH h e1 e2 eF).eg (setH h e1 e2 eF).smax (setH h e1 e2 eF).p3
        (setH h e1 e2 eF).gcl = (silu, fs) := hgt
    rw [hgt] at hy
    rw [hgt']
    cases hy
    rfl

/-- **THE FIFTH MAKER STORES THE LETTERS.** -/
theorem pub_letters {y : Lay} {sc0 : Scales} {rope0 : Array Nat} {W0 : WsLay} {V : Nat}
    {tokv : Array Nat} {st : Settings} {L : Pub}
    (h : Pub.of y sc0 rope0 W0 V tokv st = .ok L) (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales)
    (rope : Array Nat) (W : WsLay) :
    Pub.of (setY y e1 e2 eF pub) sc rope { W with lk := W0.lk } V tokv st =
      .ok (setP L e1 e2 eF pub sc rope W) := by
  delta Pub.of at h ⊢
  obtain ⟨c1, h⟩ := ok_of_refuse h
  obtain ⟨rd, hrd, h⟩ := ok_of_bind h
  cases h
  exact refuse_go c1 (bind_go (a := rd) hrd rfl)

/-- The plans of some groups in a row do not read the letters. -/
theorem plansFrom_letters (P : Pub) (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales)
    (rope : Array Nat) (W : WsLay) : ∀ (n g : Nat) (O : Option HPlan2),
    plansFrom (setP P e1 e2 eF pub sc rope W) n g O = plansFrom P n g O := by
  intro n
  induction n with
  | zero =>
    intro g O
    rfl
  | succ n ih =>
    intro g O
    show (planG (setP P e1 e2 eF pub sc rope W) g O >>= fun p =>
        plansFrom (setP P e1 e2 eF pub sc rope W) n (g + 1) (some p) >>= fun l =>
          pure (p :: l)) =
      (planG P g O >>= fun p => plansFrom P n (g + 1) (some p) >>= fun l => pure (p :: l))
    rw [planG_set]
    exact congrArg _ (funext fun p => by rw [ih])

/-- **THE SIXTH MAKER DOES NOT READ THE LETTERS.** -/
theorem plans_letters (P : Pub) (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales)
    (rope : Array Nat) (W : WsLay) : plansG (setP P e1 e2 eF pub sc rope W) = plansG P := by
  delta plansG
  rw [plansFrom_letters]
  rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.planG_set
#print axioms OnBytes.Road.K4.C.bind_go
#print axioms OnBytes.Road.K4.C.refuse_go
#print axioms OnBytes.Road.K4.C.onOk_inv
#print axioms OnBytes.Road.K4.C.onOk_go
#print axioms OnBytes.Road.K4.C.base_letters
#print axioms OnBytes.Road.K4.C.pub_letters
#print axioms OnBytes.Road.K4.C.plansFrom_letters
#print axioms OnBytes.Road.K4.C.plans_letters
