-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotTiesAt.lean: the record SlotTies of Johnson/Road/K4/FrontDictOf.lean, filled:
its eleven fields on hidden values under slots from SlotsHeld (Johnson/Road/K4/SlotsOfLed.lean), its
two fields on the powers that batch from the hearing's calls (Led7,
Johnson/Road/K4/OwnLedgers.lean); the other five stay premises.

Main names:
  `gam_at`, `om_at`: the two batching elements in the library's record of the norms, at the chain's
    data read off a tape, are the elements that two rounds of the tape drew, read: by definition.
  `sqG_of_led`, `batW_of_led`: the fields sqG and batW, where the hearing has returned.
  `slotTies_of`: SlotTies from SlotsHeld and seven fields.
Limits. PREMISES OF slotTies_of: SlotsHeld; the three fields on the verifier's tables of weights
(sqW, g5W, g6W: Johnson/Road/K4/PointsOf.lean pays them from ties of points); the two constants of
each norm (eps, two); sqG and batW. Of the two lemmas on powers: Led7 and three equations on public
numbers. One direction: from a return. A group that is not the first. Nothing on soundness.


-/
import Johnson.Road.K4.SlotsOfLed
import Johnson.Road.K4.FrontDictOf
import OnBytes.Desc.First.K4.BatchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Level Tsc ledNS ledNP hiTab)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard epsOf twoM)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR tailT tapeEps)
open OnBytes.Desc.First.K4 (powers_val)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lF lFe npOf)
open Blocks (eqN)

section Powers

variable [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF Pf) R)

/-- The element that batches the limbs, in the library's record: what the tape's first round drew,
read. -/
theorem gam_at (k : Ks) (t : Tape) (nz : NzT (tailF Pf) k t) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (zt : ℕ → Cb.Gl.E) :
    (eAt Pf.toOwnPar Pf.wPart ((tailT W' k t nz a).z7 x) zt).γ = gl.val (tapeEps t) := rfl

/-- The element that batches the products: what the products' round drew, read. -/
theorem om_at (k : Ks) (t : Tape) (nz : NzT (tailF Pf) k t) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (zt : ℕ → Cb.Gl.E) :
    (eAt Pf.toOwnPar Pf.wPart ((tailT W' k t nz a).z7 x) zt).ω = gl.val (tapeEps (k.tcP t)) := rfl

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- SlotTies.sqG, where the hearing has returned. -/
theorem sqG_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (hNS : ledNS P.y.h.xl = 9) (zt : ℕ → Cb.Gl.E) :
    ∀ l, l < 5 → gl.val (o.H.gp.getD l zeroE) =
      (eAt Pf.toOwnPar Pf.wPart ((k4Tail W' P hp t0 nz a).z7 x) zt).γ ^ l :=
  fun l hl =>
    (congrArg (fun v : Array E => gl.val (v.getD l zeroE)) (Ld.kGp.trans Ld.gp)).trans
      ((powers_val gl (tapeEps (t0.drop 1)) (n := ledNS P.y.h.xl) (s := l)
        (by rw [hNS]; omega)).trans
        (congrArg (· ^ l) (gam_at Pf W' (ksOf P hp) (t0.drop 1) nz a x zt).symm))

/-- SlotTies.batW, where the hearing has returned. -/
theorem batW_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (hNP : ledNP P.y.h.xl = 7) (hNI : P.y.NI = Pf.D.nNu) (zt : ℕ → Cb.Gl.E) :
    ∀ n, n < 7 * Pf.D.nNu → gl.val (o.H.omV.getD n zeroE) =
      (eAt Pf.toOwnPar Pf.wPart ((k4Tail W' P hp t0 nz a).z7 x) zt).ω ^ n :=
  fun n hn =>
    (congrArg (fun v : Array E => gl.val (v.getD n zeroE)) (Ld.kOmV.trans Ld.omV)).trans
      ((powers_val gl (tapeEps ((ksOf P hp).tcP (t0.drop 1))) (n := ledNP P.y.h.xl * P.y.NI)
        (s := n) (by rw [hNP, hNI]; exact hn)).trans
        (congrArg (· ^ n) (om_at Pf W' (ksOf P hp) (t0.drop 1) nz a x zt).symm))

end Powers

/-- **SlotTies**, from the hidden values under the slots and seven fields. -/
theorem slotTies_of {K J : Type} [Field K] [scl : Scl] {ρ : Reading K} {W : World K} {P : Pub}
    {o : Own} {D : Dim} {NN : NormsNames J} {eN : NormsE K} {NT : TermsNames J} {eT : TermsE K}
    {NG : GatedNames J} {eG : GatedE K} {b B sG : ℕ} {y : J → K}
    (S : SlotsHeld W o D NN eN NT eT NG eG y)
    (sqW : ∀ e, (hiTab o.H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e →
      ∀ i kh, i < D.nNu → kh < B →
        ρ.val (e.getD (i * P.y.Pd / P.y.S2 + kh) zeroE) =
          eqN (D.lL + 1 + b) 0 eN.r1 (i * 2 ^ b + kh))
    (sqG : ∀ l, l < 5 → ρ.val (o.H.gp.getD l zeroE) = eN.γ ^ l)
    (batW : ∀ x, x < 7 * D.nNu → ρ.val (o.H.omV.getD x zeroE) = eN.ω ^ x)
    (eps : ∀ i, i < D.nNu → ρ.val (epsOf o.v.y i) = ((npOf D i).eps : K))
    (two : ∀ i, i < D.nNu → (twoM o.v i).value ρ W = 2 ^ ((npOf D i).M + 1))
    (g5W : ∀ e, (hiTab o.hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption = some e →
      ∀ x, x < 2 ^ D.lL * 2 ^ (lF D - sG) →
        ρ.val (e.getD (x / 2 ^ (lF D - sG) * (P.y.Pf / P.y.S2) + x % 2 ^ (lF D - sG)) zeroE) =
          eqN (D.lL + lF D - sG) 0 eG.r5 x)
    (g6W : ∀ o2 e, o.hd2 = some o2 →
      (hiTab o2.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption = some e →
      ∀ x, x < 2 ^ (D.lL - 1) * 2 ^ (lFe D - sG) →
        ρ.val (e.getD (x / 2 ^ (lFe D - sG) * 2 ^ (lFe D - sG) + x % 2 ^ (lFe D - sG)) zeroE) =
          eqN (D.lL - 1 + lFe D - sG) 0 eG.r6 x) :
    SlotTies ρ W P o D NN eN NT eT NG eG b B sG y where
  sqL := S.sqL
  sqR := S.sqR
  sqW := sqW
  sqG := sqG
  batCl := S.batCl
  batW := batW
  slot2 := S.slot2
  slotW := S.slotW
  slotP := S.slotP
  eps := eps
  two := two
  slotT := S.slotT
  g5L := S.g5L
  g5R := S.g5R
  g5W := g5W
  g6L := S.g6L
  g6R := S.g6R
  g6W := g6W

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.gam_at
#print axioms OnBytes.Road.K4.om_at
#print axioms OnBytes.Road.K4.sqG_of_led
#print axioms OnBytes.Road.K4.batW_of_led
#print axioms OnBytes.Road.K4.slotTies_of
