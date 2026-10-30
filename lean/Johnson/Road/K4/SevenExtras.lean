-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SevenExtras.lean: three small statements that the laying of seven_of_led
(Johnson/Road/K4/SevenOfLed.lean) into the row of K4's kind asks beside it.

  `side_mem`: the two side claims of a public record Pub34 whose slots and end of the batched
    sumcheck are the hearing's are members of the list that K4's run "back" returns.
  `front_tokv`: K4's run "front" does not read the tokens: laid over the public record or not, it
    returns the same.
  `rider_of_hot`: from the part hot of the ledger at yL: for each routed layer the extension over
    the positions of "the sum of the selector's entries less 1" vanishes at the letter zt.
Limits. rider_of_hot asks NormsOk (Johnson/Road/K4/LateNames.lean pays it from sizes). Nothing on a
draw, on soundness or on hiding.


-/
import Johnson.Road.K4.SevenOfLed
import Johnson.Road.K4.FrontLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (d10)
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Layer (Pub Own)

/-- The record's two side claims are members of the list of the run "back". -/
theorem side_mem {K : Type} [Field K] (X : Rows.Pub34 K) {o : Own} (XsA : X.sA0 = o.K.sA0)
    (XsB : X.sB0 = o.K.sB0) (Xfin : X.fin = o.K.fin) {F G : Fork} {fs : Array Aff}
    (h : Desc.First.K4.formsBack o F = some (fs, G)) : ∀ f ∈ X.sideClaims, f ∈ fs.toList := by
  intro f hf
  rw [back_library h]
  unfold Rows.Pub34.sideClaims at hf
  rw [XsA, XsB, Xfin] at hf
  rcases List.mem_cons.mp hf with rfl | hf
  · simp
  · rcases List.mem_cons.mp hf with rfl | hf
    · simp
    · exact absurd hf List.not_mem_nil

/-- K4's run "front" does not read the tokens. -/
theorem front_tokv (rows : Bool) (P : Pub) (tk : Array Nat) (g : ℕ) (o : Own) (F : Fork) :
    Desc.First.K4.formsFrontWith rows { P with tokv := tk } g o F =
      Desc.First.K4.formsFrontWith rows P g o F := rfl

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Y : LateLay Nm J₂} {ιN : NormsNm → Nm}
  {ιT : TermsNm → Nm} {ιG : GatedNm → Nm} {fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J}
  {zt : (tailF P).s7.Nx → ℕ → E} {b s B sG : ℕ}

/-- From the part hot at yL. -/
theorem rider_of_hot (O : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B)
    (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (e : (tailF P).s7.Nx) (m : M)
    (h : Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).hot (yL P Y fm e m)) :
    ∀ l, l < P.D.ne → Blocks.ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) (zt e) = 0 :=
  hot_last (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e)) P.D (P.rd (P.msg m))
    (yL P Y fm e m) (late_norms P O e m).sel ((ledOf_holds _ _).1 h)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.side_mem
#print axioms OnBytes.Road.K4.front_tokv
#print axioms OnBytes.Road.K4.rider_of_hot
