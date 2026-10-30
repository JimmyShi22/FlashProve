-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PartsOfClaims.lean: seven of the eight parts of the library's ledger of a layers'
sub-proof hold, where the claims of K4's run "front" (with or without the lookup's own claims) are
worth 0, the dictionary FrontDict holds at the library's own letters, and the claims that are not
ported here are worth 0.

Johnson/Road/K4/ValuesOfClaims.lean (values_of_front) goes from K4's claims to library-side forms at
free names and records. Johnson/Road/K4/PartsOfValues.lean goes from library-side forms, at the
names and records that the library's definitions put in, to the parts of the ledger clAt. Here the
two are joined: the free letters are set to the library's.

  `parts_of_claims`: the parts sq, bat, led, terms, gated, hot and stack of clF hold of the entries
    y.
What is asked beside FrontDict and the run's list worth 0: the five claims that the sumchecks
themselves leave (u1At, u2At, prodU twice, upForm of formU) are worth 0 at y; the two rows rowF of
the batched sumcheck's form parts are worth 0 at y (Johnson/Road/K4/StackPort.lean concludes them).
Limits. All of these are premises. The part merge is not spoken of. With routed experts and a second
product layer alone. Implications at given entries: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.ValuesOfClaims
import Johnson.Road.K4.PartsOfValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Model (Reading World Fork Level)
open OnBytes.Model.Layer (Pub Own)
open Inst.Model (Scl)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {M X : Type} (P : FullPar K M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂) (ιN : NormsNm → Nm)
  (ιT : TermsNm → Nm) (ιG : GatedNm → Nm) (R : (tailF P).s7.Nx → Rest3 K (P.J ⊕ J₂)) (sG : ℕ)
  (zt : (tailF P).s7.Nx → ℕ → K) (b B : ℕ) (e : (tailF P).s7.Nx) (y : P.J ⊕ J₂ → K)

/-- **Seven parts of the ledger, from K4's claims.** -/
theorem parts_of_claims {ρ : Reading K} {W : World K} {Pp : Pub} {o : Own}
    (Dc : FrontDict ρ W Pp o P.D (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e))
      (namesT P.tp (readsT Y ιT)) (termsEAt P.tp ((tailF P).b3 e).2)
      (gNamesAt P.fp (gReadsAt Y ιG)) (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2)
      b B sG y)
    {g : ℕ} {rows : Bool} {F G : Fork} {fs : Array OnBytes.Model.Aff} (hp : o.v.y.h.p3 = true)
    {o2 : Level} (h2 : o.hd2 = some o2)
    (h : Desc.First.K4.formsFrontWith rows Pp g o F = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value ρ W = 0)
    (u1 : Blocks.Form.val y (u1At P.nr ((tailF P).b1 e).2) = 0)
    (u2 : Blocks.Form.val y (u2At P.nr ((tailF P).b2 e).2) = 0)
    (u5 : Blocks.Form.val y (prodU P.fp.gp ((tailF P).b5 e).2) = 0)
    (u6 : Blocks.Form.val y (prodU P.fp.rt.L ((tailF P).b6 e).2) = 0)
    (u4 : Blocks.Form.val y (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par
      (fun _ b _ _ => PEmpty.elim b) ((tailF P).b4 e).2)) = 0)
    (rA : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailF P).b4 e).2 (.inl (.inl ()))) = 0)
    (rB : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailF P).b4 e).2 (.inr (.inl ()))) = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).sq y ∧
      Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).bat y ∧
      Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).led y ∧
      Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).terms y ∧
      Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).gated y ∧
      Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).hot y ∧
      Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).stack y :=
  have v := values_of_front Dc hp h2 h hz 0
  ⟨sq_holds P Y ιN ιT ιG R sG zt b B e y u1 v.1 v.2.1,
    bat_holds P Y ιN ιT ιG R sG zt b B e y v.2.2.1,
    led_holds P Y ιN ιT ιG R sG zt b B e y u2 0 v.2.2.2.1,
    terms_holds P Y ιN ιT ιG R sG zt b B e y v.2.2.2.2.1,
    gated_holds P Y ιN ιT ιG R sG zt b B e y u5 u6 v.2.2.2.2.2.1,
    hot_holds P Y ιN ιT ιG R sG zt b B e y v.2.2.2.2.2.2,
    stack_holds P Y ιN ιT ιG R sG zt b B e y u4 rA rB⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.parts_of_claims
