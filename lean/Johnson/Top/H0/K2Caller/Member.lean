-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Member.lean: the letters of Row.lean's promise as one value; and that they
can be laid: at every record at which the test says yes one such value is written out, so the
promise speaks of something.

  Letters r H: a value for each letter of SwRow.Holds, in its order
  Letters.caller: the caller of Row.lean at them
  Letters.holds: the promise at them: Row.lean's k02Condition
  noExt, kqOf: no further oracle; the messages that stay open: the kept members
  Letters.plain: no draw at the stage, first rows 0, kqOf, no row in front of the fold, coefficients
      0, a carried joint that claims nothing, the reading and the witness 0
  plain_holds: the block's condition at its caller, and the plan's two rounds cover its two errors
Limits: Letters.plain is a poor member: it shows that the letters' types are inhabited together, no
more. It is not the place's caller in a description of the protocol: there the rows in front of the
fold, the carried joint and the reading are the link's. Those of Row.lean. Nothing on soundness. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch

/-- **The letters at a record.** -/
structure Letters (r : SwRow) (H : r.OK) : Type 1 where
  t₀ : ℕ
  oM : Fin r.lo.length → ℕ
  oZ : Fin r.lo.length → ℕ
  kq : Fin r.lo.length → Prop
  [dec : DecidablePred kq]
  B : Type
  Kc : Type
  St₀ : Type
  Wp : Type
  [fin : Fintype B]
  Sb : B → Type
  sl : ∀ b, Slf GE (Sb b) (rowsAt r H t₀ oM oZ).G.C.J
  Z : Evader GE ((rowsAt r H t₀ oM oZ).G.Row B)
  E₀ : ExtSpec
  A₀ : Rels Kc St₀ E₀ (((sigOf r.cs r.lo).sub kq).Msg × Wp)
  cutN : (sigOf r.cs r.l).Msg → ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).Cf.N.Wit
  w₀ : ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).tgt.W

attribute [instance] Letters.dec Letters.fin

/-- The caller at the letters. -/
noncomputable def Letters.caller {r : SwRow} {H : r.OK} (X : Letters r H) : Cb.Pv.SendLocRide.Size
    GE :=
  callerAt r H X.t₀ X.oM X.oZ X.kq X.Sb X.sl X.Z X.A₀ X.cutN X.w₀

/-- **The promise at the letters.** -/
theorem Letters.holds {r : SwRow} (h : r.ok = true) (X : Letters r (r.ok_says h)) :
    Cb.Pv.SendLocRide.OK X.caller ∧
      List.Forall₂ (Cb.Pv.Covered r.set .request)
        ((Err.toList (Cb.Pv.SendLocRide.eps X.caller)).zip (Shape.chalList (Cb.Pv.SendLocRide.R
            X.caller).shape)) r.specs :=
  k02Condition r h X.t₀ X.oM X.oZ X.kq X.dec X.B X.Kc X.St₀ X.Wp X.fin X.Sb X.sl X.Z X.E₀ X.A₀
      X.cutN X.w₀

/-- No further oracle. -/
def noExt : ExtSpec := ⟨Unit, Unit, Unit, fun _ _ => ()⟩

/-- The messages that stay open: the kept members. -/
def kqOf (r : SwRow) (i : Fin r.lo.length) : Prop := i.val ∈ r.kept

instance (r : SwRow) : DecidablePred (kqOf r) := fun i => inferInstanceAs (Decidable (i.val ∈
    r.kept))

/-- **A value for each letter.** -/
noncomputable def Letters.plain (r : SwRow) (H : r.OK) : Letters r H where
  t₀ := 0
  oM := fun _ => 0
  oZ := fun _ => 0
  kq := kqOf r
  B := Empty
  Kc := Unit
  St₀ := Unit
  Wp := Unit
  Sb := fun _ => Unit
  sl := fun b => b.elim
  Z := { D := Unit, ze := fun _ _ => 0, err := 0 }
  E₀ := noExt
  A₀ := { rel := fun _ _ _ => True, relR := fun _ _ => True, on := fun _ => True, core := fun _ =>
      () }
  cutN := fun _ => (fun _ => 0, fun _ => 0)
  w₀ := (fun _ => (fun _ => 0, fun _ => 0), ((fun _ => 0, fun _ => 0), ()))

/-- **The promise at it.** -/
theorem plain_holds (r : SwRow) (h : r.ok = true) :
    Cb.Pv.SendLocRide.OK (Letters.plain r (r.ok_says h)).caller ∧
      List.Forall₂ (Cb.Pv.Covered r.set .request)
        ((Err.toList (Cb.Pv.SendLocRide.eps (Letters.plain r (r.ok_says h)).caller)).zip
          (Shape.chalList (Cb.Pv.SendLocRide.R (Letters.plain r (r.ok_says h)).caller).shape))
              r.specs :=
  Letters.holds h _

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.Letters.holds
#print axioms VerifiableInference.Desc.First.K2Caller.plain_holds
