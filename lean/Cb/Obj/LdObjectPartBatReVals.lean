-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartBatReVals.lean: bookkeeping for the fifth part over any "on" with the standard
plan (Cb/Obj/LdObjectPartBatO.lean): the fixed values that it takes exist, and its shapes are
countable, under the hypotheses named below.


The object is one record with a configuration and, over it, the sub-protocols of the proof system,
as five terms. The test for linear constraints is the proximity test with claims that follows a
preamble. At N instances it is the fifth term. Countability is bookkeeping for the passage to one
random oracle (the head of Cb/Obj/LdObjectCtb.lean).
Statements are the theorems' own texts. A guard: a theorem "for all fixed values" says nothing if
one of their types is empty.

Main names:
  `ldORE_claim`: the end of a request (Cb/Obj/LdObjectReqEnd.lean): from a state of each open row
    and one state of the rest of the explicit part, a claim of the test that follows (`R.O.Cl`: the
    final batching's last claim) exists.
  `stdPO_vals`: the fifth part over any "on" with the standard plan (Cb/Obj/LdObjectPartBatO.lean),
    for non-empty `Fin Cf.C₀.n` and P: from one claim, its five fixed values (x₀, y₀, d, d₀, ya) and
    the assembled object's two (encoding randomness, messages) exist.
  `stdPO_ctbB`: its clause on countability (`Bt.CtbB`, Cb/Obj/LdObjectCtbSplit.lean), for the same
    non-empty types, from: the symbols of the three families are countable; a native symbol of each
    oracle message has finitely many coordinates.







Limits: on a protocol this file has two kinds of conclusion: that a type of values is non-empty
(as in `ldORE_claim`, `stdPO_vals`) and countability (as in `stdPO_ctbB`);
beyond these kinds no statement of the file concludes anything of a protocol.



Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartBatRe
import Cb.Obj.LdObjectCtbBat
import Cb.Obj.LdObjectCtbToy

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem pPt_ne {E : Type} [Field E] : ∀ l : List (PFmt E), Nonempty (PPt l)
  | [] => ⟨()⟩
  | _ :: l => ⟨((0 : E), Classical.choice (pPt_ne l))⟩

/-- A claim of the test that follows the end of a request. -/
theorem ldORE_claim {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (R : LdORE F E Kc) (sb : ∀ b, R.Sb b) (st : R.St) : Nonempty R.O.Cl :=
  ⟨⟨(((fun _ => 0, sb), st), Classical.choice R.Z.ne), 0, Classical.choice (pPt_ne _), 0⟩⟩

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  [Nonempty (Fin Cf.C₀.n)] {on : LdOLd Cf} {P : Type} [Fintype P] [Nonempty P] (D : StdPO on.ol P)

/-- For non-empty `Fin Cf.C₀.n` and P, the fixed values exist, as soon as there is one claim. -/
theorem stdPO_vals (cl : on.Cl) :
    Nonempty ((D.T.St₁ × on.ol.toC.S.Smp) × (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str ×
        on.ol.toC.P.W0 × on.ol.P.W0 × on.ol.toC.P.Ea.Str × on.S.Rnd × on.ol.left.AMsg) := by
  let rec0 : on.ol.toC.D.X.Rec := (Classical.choice on.ol.toC.D.X.Z.ne, fun _ => 0)
  let st6 : on.ol.toC.St6 :=
    ((((cl, rec0), (fun _ => 0, fun _ => 0)), (fun _ => Classical.arbitrary _, fun _ => 0)),
      fun _ => 0)
  exact ⟨((((fun _ => 0, fun _ => st6), D.T.fa cl),
      fun o => (Classical.choice (on.ol.toC.S.om o).Z.ne, fun _ => 0)),
    ((), fun o p => (on.ol.toC.S.om o).sy0 p),
    (fun _ _ => 0, (fun _ => (fun _ => 0, fun _ => 0), ())),
    (fun _ _ => 0, fun _ => (fun _ => 0, fun _ => 0)),
    ((), fun a p => (on.S.om a).sy0 p),
    fun _ _ => 0, fun _ _ => 0)⟩

omit [Fintype F] in
/-- Countability. -/
theorem stdPO_ctbB (N : ℕ) (SnB : on.ol.toC.P.Snd) (ba : on.ol.toC.Sa.O → ℕ)
    (x₀ : D.T.St₁ × on.ol.toC.S.Smp) (y₀ : (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str)
    (d : on.ol.toC.P.W0) (d₀ : on.ol.P.W0) (ya : on.ol.toC.P.Ea.Str) (hW : on.NW.CtbSy)
    (hU : on.NU.CtbSy) (hO : on.NO.CtbSy) (h : ∀ o, (on.ol.toC.S.om o).C.FinNS) :
    (D.partB N SnB ba x₀ y₀ d d₀ ya).CtbB :=
  ⟨hW, hU, hO,
    ctb_base _ _ _ _ _ _ (finNS_grp D.pl.G₁ h),
    ctb_base _ _ _ _ _ _ (finNS_grp D.pl.G₂ fun a => h a.1),
    ctbA_consLo D.X.run _ _ _
      (ctb_base _ _ _ _ _ _ (finNS_grp D.G₃ fun a => h a.1.1)) (ctbA_tcNil _ _ _ _)⟩

end

open LdToy LdToy7 LdToy74 ReToy

end Cb
