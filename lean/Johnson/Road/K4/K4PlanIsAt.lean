--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/K4PlanIsAt.lean: THE LETTERS OF Johnson/Road/K4/K4PlanAt.lean ARE THE FIELDS OF THE
COMPOSED MEANING's CLOSED CONSTANT (another house's Johnson/P5J/LettersAt.lean, Rad3Seat3At.lean:
the definitions that its `At.𝔇All` calls, a field a line). Seven equations, each by unfolding, and
the two closed laws of Johnson/Road/K4/K4PlanFast.lean restated at that house's own names. Nine
theorems. No draw, no count.

  `sentAt_is`, `arrAt_is`, `numAt_is`, `seatTAt_is`: our term is that house's.
  `ms_is`: its members are `P5T.msAtR` at its own radii.
  `N_sent`, `N_index`: its numbers have our numbers' sent and index.
  `k4PlanFit_const`, `k4PlanFitF_const`: `K4PlanFit`, `K4PlanFitF` AT `At.sentAt Zp`,
    `At.seat3At Zp`, `At.arr Zp`, `At.ms Zp lay`, `At.N Zp cF`, `At.num Zp`, from the tests that can
    run.

Limits. K04_law IS NOT PROVED BY THIS. The constant's own head (its named tests) is, by its house's
word, not yet shown to be meetable: nothing here rests on it: these are equations of terms. THIS
FILE STANDS OVER THAT HOUSE's HEAVY CLOSURE: it is kept apart so that the files beneath it need not.

-/
import Johnson.Road.K4.K4PlanFast
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First.Look (sigListCalls szOf pubAt stepOf)
open Meaning (seatBy fLay)
open Inst.Model.Layout (kRef hRef)

variable (Zp : ProofFile.Pub)

theorem sentAt_is : sentAt Zp = P5J.At.sentAt Zp := rfl

theorem arrAt_is : arrAt Zp = P5J.At.arr Zp := rfl

theorem numAt_is : numAt Zp = P5J.At.num Zp := rfl

theorem seatTAt_is (rad : OnBytes.OracleShape → ℕ) (l : ℕ)
    (j : Fin (sigListCalls (sentAt Zp) rad l).length) :
    seatTAt Zp rad l j = P5J.At.seat3At Zp l false j.val := rfl

theorem ms_is (lay : ByteArray) : P5J.At.ms Zp lay = P5T.msAtR Zp (P5J.At.rad Zp lay) := rfl

theorem N_sent (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) :
    (P5J.At.N Zp cF).sent = (numbersAt Zp).sent := rfl

theorem N_index (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) :
    (P5J.At.N Zp cF).index = (numbersAt Zp).index := rfl

variable {rows cols : ℕ}

/-- **`K4PlanFit` at the closed constant's own fields**, from the three tests that can run. -/
theorem k4PlanFit_const {pol KL : ByteArray} {tk : Array Nat} (lay : ByteArray)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) (p : Par) (hc : commonFastB Zp = true)
    (hf : firstFastB Zp p.g = true) (hm : seamFastB Zp p.g = true) (hg0 : 0 < p.g) (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Zp.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps pol KL Zp.p.X)
    (B : RefPub Zp.p.X p.g) (hP : p.P = { Zp.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Zp.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFit (X := Zp.p.X) (p := p) x (pubAt Zp.p.X (2 * p.g / stepOf Zp.p.X)) (P5J.At.sentAt Zp)
      rad (fun j => P5J.At.seat3At Zp x.link false j.val) posI oW enc wOf (P5J.At.arr Zp)
      (P5J.At.ms Zp lay) (P5J.At.N Zp cF) (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Zp.p.X)
      (seatBy (fLay (P5J.At.layout Zp) (P5J.At.num Zp)) Zp.p.X (Meaning.sizesOf Zp.p.X)) hd :=
  k4PlanFit_fast Zp (P5J.At.rad Zp lay) (N_sent Zp cF) (N_index Zp cF) p hc hf hm hg0 hg x hx hG rad
    posI oW enc wOf hd St B hP P0 hgr hhd

/-- **`K4PlanFitF` at the closed constant's own fields**, from the one test that can run. -/
theorem k4PlanFitF_const {pol KL : ByteArray} {tk : Array Nat} (lay : ByteArray)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) (p : Par) (hf : firstFastB Zp p.g = true)
    (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Zp.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps pol KL Zp.p.X)
    (B : RefPub Zp.p.X p.g) (hP : p.P = { Zp.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Zp.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFitF (X := Zp.p.X) (p := p) x (pubAt Zp.p.X (2 * p.g / stepOf Zp.p.X)) (P5J.At.sentAt Zp)
      rad (fun j => P5J.At.seat3At Zp x.link false j.val) posI oW enc wOf (P5J.At.arr Zp)
      (P5J.At.ms Zp lay) (P5J.At.N Zp cF) (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Zp.p.X)
      (seatBy (fLay (P5J.At.layout Zp) (P5J.At.num Zp)) Zp.p.X (Meaning.sizesOf Zp.p.X)) hd :=
  k4PlanFitF_fast Zp (P5J.At.rad Zp lay) (N_sent Zp cF) (N_index Zp cF) p hf hg x hx hG rad posI oW
    enc wOf hd St B hP P0 hgr hhd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sentAt_is
#print axioms OnBytes.Road.K4.arrAt_is
#print axioms OnBytes.Road.K4.numAt_is
#print axioms OnBytes.Road.K4.seatTAt_is
#print axioms OnBytes.Road.K4.ms_is
#print axioms OnBytes.Road.K4.N_sent
#print axioms OnBytes.Road.K4.N_index
#print axioms OnBytes.Road.K4.k4PlanFit_const
#print axioms OnBytes.Road.K4.k4PlanFitF_const
