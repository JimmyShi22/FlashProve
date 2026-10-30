-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Rider/Model/AttFreeAll.lean: the witness of Cb/G6/Rider/Model/AttFree.lean at the letters at
which the whole model takes an attention segment, and the honest cells at the all-zero index.

Definitions, statements and proofs. No protocol occurs here.

Main names:
  `att_free_at`: the witness against one segment's relation, at the letters at which the whole
    model takes the attention segment of group g, for valid scales, over every commutative ring in
    which 1 ≠ 0.
  `zero_v`: at zero weights the values of attention are 0. `off0 pp prompt g`: the honest cells of
    the attention segment of group g at the all-zero index with every denominator raised by 1;
    `adm0`, `vals0`: its inputs meet `Adm`, and the values are 0.

Limits: the relation with the cost ledger (Policy/Rel/LedgerRel.lean) is not spoken of. `off0` is
at one index, which is made up; of another index it says nothing. Of the two sentences that a use
of the rule for a second test should prove (`hollow_own`, Cb/G6/Rider/Both.lean) this is the core
of the first alone, on the library's relation, not at a joint of a protocol.
Terms: lean/GLOSSARY.md.

-/
import Cb.G6.Rider.Model.AttFree
import Cb.G6.Rider.Model.OneHotFreeRef

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Rider
open Finset Inst.Model Inst.Model.All Inst.Model.ScalesSanity
open Inst.Model.Layout (kRef hRef)

/-! ## 1. One segment's witness at the letters of the whole relation -/

/-- The witness against one segment's relation (att_free_not, Cb/G6/Rider/Model/AttFree.lean) at the
sizes, scales and table at which the whole model takes the attention segment of group g, for valid
scales, over every commutative ring in which 1 ≠ 0. -/
theorem att_free_at {κ : ℕ → LayerScale} {nf : NormPar} {tbG : ℕ → Tables}
    (hL : LawfulK κ nf tbG) {g : ℕ} (hg : g < nGr) (F : Type) [CommRing F] [Nontrivial F] :
    ∃ t : AttSeg.Raw → ℤ, ¬ AttSeg.RFraw (scl := SFK κ nf g) (DAK κ g) (tbG g) F t ∧
      (∀ c : AttSeg.Raw, c.Valid (DAK κ g) → |t c| < 2 ^ 18) ∧
      (∀ (c : Fin 4) (X : ℕ), X < (DAK κ g).used c →
        AttSeg.keyVec (scl := SFK κ nf g) (DAK κ g) (tbG g) (AttSeg.castT t : AttSeg.Raw → F) c X ∈
          AttSeg.lutSet (AttSeg.lut (scl := SFK κ nf g) (DAK κ g) (tbG g) c)) ∧
      ∀ j : AttSeg.Idn, j.Valid (DAK κ g) → (∀ b g' i, j ≠ .at3 b g' i) →
        AttSeg.idnVal (DAK κ g) (AttSeg.castT t : AttSeg.Raw → F) j = 0 :=
  att_free_not (scl := SFK κ nf g) (sizeOKK hL hg) (expTabK hL hg)
    (by decide : 0 < AttSeg.Dim.ref.nb) F

/-! ## 2. At the all-zero index -/

/-- At zero weights the values of attention are 0. -/
theorem zero_v (P : Params) (hv : 1 ≤ P.kv) (x : ℕ → Vec) (i c : ℕ) :
    Att.v P zeroLayer x i c = 0 := by
  simp [Att.v, Att.vw, Att.Av, zeroLayer, dot_zero, rhu_zero hv, clamp]

section Zero
variable (pp : ScalesAndPolicy) (prompt : Fin ppref.T → Fin ppref.V) (g : ℕ)

/-- The program's queries, keys, values and outputs of the attention segment of group g at the
all-zero index. -/
noncomputable abbrev attQ0 : ℕ → ℕ → ℕ → ℕ → ℤ :=
  AttSeg.Hon.QpK (DAK pp.kap g) (fun lam => PG pp.kap g lam) (fun _ => tbRef)
    (wOf (Layout.matrixRef iZero) g) (4 * g)
    fun lam => xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g (2 * lam)
@[inherit_doc attQ0] noncomputable abbrev attK0 : ℕ → ℕ → ℕ → ℕ → ℤ :=
  AttSeg.Hon.KpK (DAK pp.kap g) (fun lam => PG pp.kap g lam) (fun _ => tbRef)
    (wOf (Layout.matrixRef iZero) g) (4 * g)
    fun lam => xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g (2 * lam)
@[inherit_doc attQ0] noncomputable abbrev attV0 : ℕ → ℕ → ℕ → ℕ → ℤ :=
  AttSeg.Hon.VpK (DAK pp.kap g) (fun lam => PG pp.kap g lam) (wOf (Layout.matrixRef iZero) g)
    fun lam => xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g (2 * lam)
@[inherit_doc attQ0] noncomputable abbrev attO0 : ℕ → ℕ → ℕ → ℕ → ℤ :=
  AttSeg.Hon.OpK (DAK pp.kap g) (fun lam => PG pp.kap g lam) (fun _ => tbRef)
    (wOf (Layout.matrixRef iZero) g) (4 * g)
    fun lam => xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g (2 * lam)

/-- The honest cells of the attention segment of group g at the all-zero index, with every
denominator raised by 1. -/
noncomputable def off0 : AttSeg.Raw → ℤ :=
  offDen (scl := SFK pp.kap pp.nf g) (DAK pp.kap g) tbRef (attQ0 pp prompt g) (attK0 pp prompt g)
    (attV0 pp prompt g) (attO0 pp prompt g)

variable {pp} (hpp : Lawful pp) {g} (hg : g < 12)

include hpp hg in
/-- These inputs meet the conditions of Inst/Model/Att/HonestGen.lean. -/
theorem adm0 : AttSeg.Hon.Adm (scl := SFK pp.kap pp.nf g) (DAK pp.kap g) tbRef (attQ0 pp prompt g)
    (attK0 pp prompt g) (attV0 pp prompt g) (attO0 pp prompt g) :=
  AttSeg.Hon.admK (scl := SFK pp.kap pp.nf g) (D := DAK pp.kap g)
    (Ps := fun lam => PG pp.kap g lam) (tbs := fun _ => tbRef) (tb := tbRef)
    (wOf (Layout.matrixRef iZero) g) (4 * g)
    (fun lam => xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g (2 * lam))
    (fitHK (lawfulK_of hpp) hg) (fun _ => rfl) (sizeOKK (lawfulK_of hpp) hg)
    (expTabK (lawfulK_of hpp) hg)

include hpp hg in
/-- The values of the segment's layers are 0. -/
theorem vals0 : ∀ b < (DAK pp.kap g).nb, ∀ g' j n,
    attV0 pp prompt g ((DAK pp.kap g).lamOf b) g' j n = 0 := fun b hb g' j n => by
  have hl : (DAK pp.kap g).lamOf b < 4 := AttSeg.NW2.lamOf_lt hb
  show Att.v (PG pp.kap g _) (wOf (Layout.matrixRef iZero) g _) _ j _ = 0
  rw [show wOf (Layout.matrixRef iZero) g ((DAK pp.kap g).lamOf b) = zeroLayer from
    zero_layer (by omega)]
  refine zero_v _ ?_ _ _ _
  show 1 ≤ (ppref.at (kapG pp.kap g ((DAK pp.kap g).lamOf b))).kv
  rw [kapG_lt pp.kap g hl]
  exact (shifts1 hpp (by omega)).2.2.1

end Zero

end Cb.Rider

#print axioms Cb.Rider.att_free_at
