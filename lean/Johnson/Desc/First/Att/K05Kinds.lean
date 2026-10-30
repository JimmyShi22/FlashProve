-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Kinds.lean: K05_below (Att/K05Below.lean) with the Boolean on a public
list: the kind's ROUNDS with the format's own
kinds of their names (Fmt.kindOf, Decl/Declared.lean).

Main names:
  `kindFmt`: the format's kind of the entry's name ("nothing" where the format has no such name).
  `kinds_fmt`: where each written round's kind is the format's kind of its entry's name, and the
    entries are the kind's ROUNDS: the
    written rounds' own entries and kinds are that public list.
  `K05_below_fmt`: so a yes of k5Held on the public list gives Err.Below (bearErr …) (2⁻¹ ^ k).

kindAt (Att/K05Held.lean: "elems wherever an entry draws") is not the format's kind at the rounds
named "PSC epsilon": there the format
says "join".
Premise left on the written rounds: each round's kind is Fmt.kindOf of its entry's name. The test is
evaluated in no file of this tree.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb OnBytes OnBytes.Model Cb.Pv.Att Inst.Model OnBytes.Maker
open OnBytes.Tie.Pv.Att (recOf)
open scoped ENNReal

/-- The format's own kind of the entry's name; "nothing" where the format has no such name. -/
def kindFmt (e : Fmt.Entry) : Fmt.Kind := (Fmt.kindOf e.name).getD .nothing

theorem kinds_fmt (p : Par) (ds : List RDT) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) :
    (ds.map fun d => (d.entry, d.kind)) = (rounds p).map fun r => (r.entry, kindFmt r.entry) := by
  have e1 : (ds.map fun d => (d.entry, d.kind)) = (ds.map (·.entry)).map fun e => (e, kindFmt e) := by
    rw [List.map_map]
    refine List.map_congr_left fun d hd => ?_
    show (d.entry, d.kind) = (d.entry, (Fmt.kindOf d.entry.name).getD .nothing)
    rw [hkind d hd]
    rfl
  rw [e1, he, List.map_map]
  rfl

theorem K05_below_fmt {M X : Type} (P : OwnPar Cb.Gl.E M X) (hk4 : P.kap = 4) (rows : ℕ) (p : Par)
    (hrec : p.own = recOf P rows) (Ex : ExtSpec) (k : ℕ) (ds : List RDT)
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind)
    (hc : k5Held k (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true) :
    Err.Below (bearErr ds _ ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps Ex)) ((2 : ℝ≥0∞)⁻¹ ^ k) :=
  K05_below P hk4 rows p hrec Ex k ds he (by rw [kinds_fmt p ds he hkind]; exact hc)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_below_fmt
