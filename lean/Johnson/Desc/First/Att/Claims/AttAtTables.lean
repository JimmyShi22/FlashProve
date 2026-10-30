-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/AttAtTables.lean: kind K5: AttAt (Johnson/Road/Rows/AttRead.lean: "the
setting of a claim", whose last field says that every table of the heard list is true of the
matrices) at the record made of the kind's own (oldOf, Johnson/Desc/First/Att/Claims/Any.lean) and
at the entries chosen in Johnson/Desc/First/Att/Claims/TabsByChoice.lean: from the return of
tablesP and two facts on public data, whatever the matrices, the ledger and the mask are.

Main name:
  `attAt_tablesP`: tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t →
    shapeHid lid cf = .ok (S, fs) → MatsFit S tl → for all Kc, M, G, mask:
    AttAt Reading.gl (G.worldOf Reading.gl mask (entryOf Reading.gl tl Kc M
    (oldOf S gL i).t.funs.toList)) tl Kc M (oldOf S gL i) lid cf fs.
By attAt_entryOf_gl (Claims/AttAtByChoice.lean) and apart_tablesP (Claims/ReadsApart.lean).
For whom: the letters are those of two conjuncts of GatheredAllJ
(Johnson/Desc/First/Att/K05GatheredJ.lean). In BillsAllJ (Johnson/Desc/First/Att/K05KeepsAny.lean)
the entries are bound in front of tl, Kc, M and i, which entryOf takes: a payer must fix these
first.
Premises that stay: the return of tablesP; the return of shapeHid; MatsFit.
Limits: THE READS' TRUTH IS NOT SHOWN AND NOT TOUCHED: nothing here says that the array which the
prover commits holds these entries. Nothing is said on whether the forms are worth 0 at them.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.AttAtByChoice
import Johnson.Desc.First.Att.Claims.ReadsApart

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (LookIn)

/-- **AttAt at the kind's own record and the chosen entries.** -/
theorem attAt_tablesP {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {tl : HTailF2} {nW : ℕ}
    {lk : LookIn} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t)
    (hs : Attention.shapeHid lid cf = .ok (S, fs)) (hm : MatsFit S tl) (Kc : ℕ) (M : Mats Cb.Gl.E)
    (G : Fork) (mask : ℕ → Cb.Gl.E) :
    AttAt Reading.gl (G.worldOf Reading.gl mask (entryOf Reading.gl tl Kc M (oldOf S gL i).t.funs.toList))
      tl Kc M (oldOf S gL i) lid cf fs :=
  attAt_entryOf_gl tl Kc M (oldOf S gL i) lid cf fs hs hm (by
    show Apart tl (i.t.funs.map funBack).toList
    rw [Array.toList_map]
    exact apart_tablesP ht) G mask

end K5Law
