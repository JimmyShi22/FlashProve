-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/Covered.lean: reads_covered_K04: EVERY ENTRY THAT A CLAIM OF K4's NAMES
LIES IN THE ARRAY OF READS, INSIDE ONE OF THE FAMILIES OF TABLES OF THE PLAN (`InTab`,
Johnson/Road/K4/Reads/TermsEnts.lean): for K4's own two lists of claims, `formsFront` and
`formsBack` (OnBytes/Desc/First/K4/Plain.lean). Statements and proofs.

`front_covered`: all forms of the run "front". `back_covered`: all forms of the run "back". They
join the ties of K4's lists to the library's (`front_library`, `back_library`,
Johnson/Road/K4/FrontLaw.lean) with the walks of this folder, group by group.

WHAT IS A PREMISE, AND STILL OWED. A sumcheck's own claim names what its START FORM names
(`entsIn_rowForm`), and which form a sumcheck was begun with is a fact on what HEAR returned, not on
the lists. So `front_covered` and `back_covered` take ten premises, each by name: in front: `hK3`
(the lookup's own claims, group 1: K3's files'), `hw` (the squares' layer's claim), `htV` (the
start form of the row products' token sumcheck), `hhd`, `hhd2` (the two gated layers' claims), `hlv`
(the start form of the lookup's leaves' sumcheck); behind: `hS` (the batched sumcheck's claim, in
whose start form the second token sumcheck's claim stands), `hA`, `hB` (the two end forms), `hm`
(the merge's start form). `front_covered_heard` and `back_covered_heard`: WHERE o IS WHAT `hearFl`
RETURNED, FIVE OF THE TEN ARE PAID (`hear_starts`, Johnson/Road/K4/Reads/HearStarts.lean: hw,
htV, hhd, hhd2, hm). LEFT: hK3 and hlv (K3's files'), hS, hA, hB (a walk of the batched sumcheck's
start form and end forms: not begun).

Limits. NOT SAID: that the families of v.tab fill, or lie in, the part of the array that the reads'
test covers: other files' to show. An index that strays to another tensor, layer or limb of the same
family is not caught. o.v.y.h.p3 = true is `front_library`'s premise (K4's `covers` asks it of the
plan). Nothing on soundness.
-/
import Johnson.Road.K4.Reads.NormsEnts
import Johnson.Road.K4.Reads.GatedEnts
import Johnson.Road.K4.Reads.RowsEnts
import Johnson.Road.K4.Reads.NormRowEnts
import Johnson.Road.K4.Reads.HearStarts
import Johnson.Road.K4.FrontLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own HPlan2)

/-- **The run "front".** -/
theorem front_covered {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (hp : o.v.y.h.p3 = true) (h : formsFront P g o F = some (fs, G))
    (hK3 : ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hw : InTab o.v o.H.wpl.row)
    (htV : InTab o.v o.H.tV.p.start)
    (hhd : InTab o.v o.hd.row)
    (hhd2 : ∀ x, o.hd2 = some x → InTab o.v x.row)
    (hlv : InTab o.v o.H.fo.leaves.start) :
    ∀ f ∈ fs.toList, InTab o.v f := by
  obtain ⟨sh, pp, tT, l2, g46, l7, l89, l10, l12, _, hpp, _, h2, h46, h7, h89, h10, h12, e⟩ :=
    OnBytes.Road.K4.front_library hp h
  obtain ⟨hp1, hp2⟩ := planesParts_in hpp
  intro f hf
  rw [e] at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · rcases List.mem_append.mp hf with hf | hf
          · rcases List.mem_append.mp hf with hf | hf
            · rcases List.mem_append.mp hf with hf | hf
              · rcases List.mem_append.mp hf with hf | hf
                · exact hK3 f hf
                · exact entsIn_normsL h2 hw f hf
              · rcases List.mem_cons.mp hf with rfl | hf
                · exact entsIn_rowBatch _ _
                rcases List.mem_cons.mp hf with rfl | hf
                · exact entsIn_rowForm _ _ htV entsIn_empty
                cases hf
            · exact rowsForms_in h46 f hf
          · exact termsL_rows h7 f hf
        · exact entsIn_gatedL h89 hhd hhd2 f hf
      · exact entsIn_oneHotL h10 f hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact entsIn_rowForm _ _ hlv hp1
      · exact hp2 f hf
  · split at h12
    · exact entsIn_embL h12 f hf
    · cases h12
      cases hf

/-- **The run "back".** -/
theorem back_covered {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsBack o F = some (fs, G))
    (hS : InTab o.v o.K.rowS)
    (hA : InTab o.v o.K.fin.Alin)
    (hB : InTab o.v o.K.fin.Blin)
    (hm : InTab o.v o.wo.toWsMerged.p.start) :
    ∀ f ∈ fs.toList, InTab o.v f := by
  intro f hf
  rw [OnBytes.Road.K4.back_library h] at hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hS
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_slot _) hA
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_slot _) hB
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_rowForm _ _ hm entsIn_empty
  cases hf

/-! ### With what HEAR returned -/

/-- **The run "front", behind HEAR**: two premises are left, both on the lookup's own record. -/
theorem front_covered_heard {P : Pub} {hpl : HPlan2} {g : Nat} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : OnBytes.K.Kc.Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u))
    (hp : o.v.y.h.p3 = true) (h : formsFront P g o F = some (fs, G))
    (hK3 : ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hlv : InTab o.v o.H.fo.leaves.start) :
    ∀ f ∈ fs.toList, InTab o.v f := by
  obtain ⟨a1, a2, a3, a4, _⟩ := hear_starts hh (inTab o.v)
  exact front_covered hp h hK3 a1 a2 a3 a4 hlv

/-- **The run "back", behind HEAR**: three premises are left, on the batched sumcheck. -/
theorem back_covered_heard {P : Pub} {hpl : HPlan2} {g : Nat} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : OnBytes.K.Kc.Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u))
    (h : formsBack o F = some (fs, G))
    (hS : InTab o.v o.K.rowS)
    (hA : InTab o.v o.K.fin.Alin)
    (hB : InTab o.v o.K.fin.Blin) :
    ∀ f ∈ fs.toList, InTab o.v f :=
  back_covered h hS hA hB (hear_starts hh (inTab o.v)).2.2.2.2

end OnBytes.Desc.First.K4.Reads
