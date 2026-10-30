-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotTiesAtFirst.lean: THE FIRST GROUP's twin of the typed part of
Johnson/Road/K4/SlotTiesAt.lean: the two fields of the record SlotTies
(Johnson/Road/K4/FrontDictOf.lean) on the powers that batch, from the hearing's calls (LedG,
Johnson/Road/K4/OwnLedgersG.lean), at the norms' record of the first group's chain.

slotTies_of (SlotTiesAt.lean) is general in its letters and is imported. The statements and proofs
here are that file's, turned to the first group's letters by a program and compiled; each name bears
an F.

Main names:
  `gam_atF`, `om_atF`: the two batching elements in the library's record of the norms are the
    elements that two rounds of the tape drew, read: by definition.
  `sqG_of_ledF`, `batW_of_ledF`: the fields sqG and batW, where the hearing has returned.
Limits. PREMISES: LedG and three equations on public numbers. One direction: from a return. Nothing
on soundness.


-/
import Johnson.Road.K4.SlotsOfLedFirst
import Johnson.Road.K4.SlotTiesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Level Tsc ledNS ledNP)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR tailT tapeEps)
open OnBytes.Desc.First.K4 (k0 powers_val)
open Inst.Model (Scl)

section Powers

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)

/-- The element that batches the limbs, in the library's record: what the tape's first round drew,
read. -/
theorem gam_atF (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) (zt : ℕ → Cb.Gl.E) :
    (eAtF Pf.ofp Pf.wfPart ((tailT W' k t nz a).z7 x) zt).γ = gl.val (tapeEps t) := rfl

/-- The element that batches the products: what the products' round drew, read. -/
theorem om_atF (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) (zt : ℕ → Cb.Gl.E) :
    (eAtF Pf.ofp Pf.wfPart ((tailT W' k t nz a).z7 x) zt).ω = gl.val (tapeEps (k.tcP t)) := rfl

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork}
  {u5 : Tape}

/-- SlotTies.sqG, where the hearing has returned. -/
theorem sqG_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hNS : ledNS P.y.h.xl = 9) (zt : ℕ → Cb.Gl.E) :
    ∀ l, l < 5 → gl.val (o.H.gp.getD l zeroE) =
      (eAtF Pf.ofp Pf.wfPart ((k4TailG W' P hp g t0 nz a).z7 x) zt).γ ^ l :=
  fun l hl =>
    (congrArg (fun v : Array E => gl.val (v.getD l zeroE)) (Ld.kGp.trans Ld.gp)).trans
      ((powers_val gl (tapeEps (t0.drop (k0 g))) (n := ledNS P.y.h.xl) (s := l)
        (by rw [hNS]; omega)).trans
        (congrArg (· ^ l) (gam_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x zt).symm))

/-- SlotTies.batW, where the hearing has returned. -/
theorem batW_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hNP : ledNP P.y.h.xl = 7) (hNI : P.y.NI = Pf.D.nNu) (zt : ℕ → Cb.Gl.E) :
    ∀ n, n < 7 * Pf.D.nNu → gl.val (o.H.omV.getD n zeroE) =
      (eAtF Pf.ofp Pf.wfPart ((k4TailG W' P hp g t0 nz a).z7 x) zt).ω ^ n :=
  fun n hn =>
    (congrArg (fun v : Array E => gl.val (v.getD n zeroE)) (Ld.kOmV.trans Ld.omV)).trans
      ((powers_val gl (tapeEps ((ksOf P hp).tcP (t0.drop (k0 g)))) (n := ledNP P.y.h.xl * P.y.NI)
        (s := n) (by rw [hNP, hNI]; exact hn)).trans
        (congrArg (· ^ n) (om_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x zt).symm))

end Powers

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.gam_atF
#print axioms OnBytes.Road.K4.om_atF
#print axioms OnBytes.Road.K4.sqG_of_ledF
#print axioms OnBytes.Road.K4.batW_of_ledF
