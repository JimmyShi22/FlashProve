-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/AttAtByChoice.lean: kind K5: `AttAt` (Johnson/Road/Rows/AttRead.lean:
"the setting of a claim", whose last field says that every table of the heard list is true of the
matrices) at the entries chosen in Johnson/Desc/First/Att/Claims/TabsByChoice.lean: from three
facts, whatever the matrices, the ledger and the mask are: two on public data; the third, `Apart`,
speaks of the heard list: it holds wherever no two tables of the list share a position, which their
matrices, lengths and starts decide.

Main names:
  `attAt_entryOf`: Numerals ρ, the return of shapeHid, MatsFit and `Apart` of the heard list give
    AttAt ρ (F.worldOf ρ mask (entryOf …)) tl K3 M h lid cf fs.
  `attAt_entryOf_gl`: the same at Reading.gl, where Numerals is the library's `gl_numerals`
    (Johnson/Road/FormsKeysKit.lean).
For whom: kind K5's law asks of the relation behind the kind that there are entries and matrices
with AttAt and with the gathered forms worth 0 (GatheredAllJ,
Johnson/Desc/First/Att/K05GatheredJ.lean). A payer whose sentence reads each entry as the stated
function of the cells can take these entries: then AttAt costs it the three facts. In BillsAllJ
(Johnson/Desc/First/Att/K05KeepsAny.lean) the entries are bound in front of GatheredAllJ's inner
letters tl, Kc, M and i, which `entryOf` takes: so the payer must fix these first, as functions of
the record.
Limits: `Apart`, MatsFit and the return of shapeHid are shown of no record in this file. THE READS'
TRUTH IS NOT SHOWN AND NOT TOUCHED: nothing here says that the array which the prover commits holds
these entries. Nothing is said on whether the forms are worth 0 at them.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttRead
import Johnson.Desc.First.Att.Claims.TabsByChoice

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows

/-- **AttAt at the chosen entries.** -/
theorem attAt_entryOf {K : Type} [Field K] (ρ : Reading K) (hρ : Numerals ρ) (tl : HTailF2) (K3 : ℕ)
    (M : Mats K) (h : Attention.Heard) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (hs : Attention.shapeHid lid cf = .ok (h.S, fs)) (hm : MatsFit h.S tl)
    (hA : Apart tl h.t.funs.toList) (F : Fork) (mask : ℕ → K) :
    AttAt ρ (F.worldOf ρ mask (entryOf ρ tl K3 M h.t.funs.toList)) tl K3 M h lid cf fs :=
  ⟨hρ, hs, hm, holds_entryOf ρ tl h.iU3 K3 M _ hA F mask⟩

/-- The same at the reading of the verifier's elements in the field. -/
theorem attAt_entryOf_gl (tl : HTailF2) (K3 : ℕ) (M : Mats Cb.Gl.E) (h : Attention.Heard) (lid : ℕ)
    (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (hs : Attention.shapeHid lid cf = .ok (h.S, fs)) (hm : MatsFit h.S tl)
    (hA : Apart tl h.t.funs.toList) (F : Fork) (mask : ℕ → Cb.Gl.E) :
    AttAt Reading.gl (F.worldOf Reading.gl mask (entryOf Reading.gl tl K3 M h.t.funs.toList)) tl K3 M
      h lid cf fs :=
  attAt_entryOf Reading.gl gl_numerals tl K3 M h lid cf fs hs hm hA F mask

end K5Law

#print axioms K5Law.attAt_entryOf
#print axioms K5Law.attAt_entryOf_gl
