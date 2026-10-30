-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsLayers.lean: THE MAKE OF THE LAYERS' TWO RUNS "front" AND "back" IN
THE LETTERS OF THE K9 LIST's OWN CLAUSES (`K4Values.frontForms`, `K4Values.backForms`): WITH NO
RUN's RETURN IN HAND; AND SO THE TWO CLAUSES "entsFront" AND "entsBack". Statements and proofs.

K4's files have the make at a run's return: `front_row0`, `back_row0`
(Johnson/Road/K4/Reads/RowZero.lean) ask `formsFrontWith rows P g o F = some (fs, G)` and `formsBack
o F = some (fs, G)`. The K9 list's clauses speak of `frontForms rows P g o U = some l` and of
`backForms o`, where no run has returned. HERE THOSE TWO PROOFS ARE CUT ANEW ONE STEP LOWER:
  at `front … = some l` (`front_some`, OnBytes/Desc/First/K4/ClaimsLaws.lean) and at the
  list `back o r`: every lemma that is called is K4's files'.

  `frontForms_library`: the list that `frontForms` gives, in the library's lists (after
    `front_libraryWith`, Reads/CoveredWith.lean).
  `frontForms_covered`, `backForms_covered`: every form of it names entries inside a family of
    tables alone (`InTab`), under K4's files' own premises (after `front_coveredWith`,
    `back_covered`).
  `frontForms_heard`, `backForms_heard`: behind a hearing: three premises are left, on what the
    lookup on the calls returned.
  `make_front`, `make_back`: **hh (o is a hearing's return); hK (the plan's length of the third
    vector is at most the width that the hearing stored); N : PadNames o.H.fo F' ⊢ `EntsMake o.v.iU3
    l`** (EntsAtBatch.lean) of what frontForms gives, and of backForms o.
  `entsFront_of`, `entsBack_of`: **so the two clauses' bodies**, from the static clause, hU and h0
    (`ents_of_static`).
THE HEARING's PUBLIC PARAMETERS AND GROUP NEED NOT BE THOSE AT WHICH frontForms IS READ (the seat
hears at its parameters with the request's tokens laid in): the two are apart in `frontForms_heard`,
`make_front` and `entsFront_of`.
Limits. hh, hK and N are shown of no state here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntsAtBatch
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Road.K4.Reads.RowZeroNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own)
open VerifiableInference.Desc.K4Values (frontForms)

/-- The list that `frontForms` gives, in the library's lists. -/
theorem frontForms_library {rows : Bool} {P : Pub} {g : Nat} {o : Own} {U : Fork}
    {l : List Aff} (hp : o.v.y.h.p3 = true) (h : frontForms rows P g o U = some l) :
    ∃ sh pp tT l2 g46 l7 l89 l10 l12,
      Desc.First.K4.planesParts o.v o.H.fo = some pp ∧ o.H.tT = some tT ∧
      Road.normsL P o.v o.H = some l2 ∧ Desc.First.K4.rowsForms o.v o.H = some g46 ∧
      Rows.termsL o.v tT.sEnd = some l7 ∧ Rows.gatedL P o.v o.hd o.hd2 = some l89 ∧
      Road.oneHotL o.v = some l10 ∧
      (if g == 0 then Road.embL o.v o.H o.sVE else some []) = some l12 ∧
      l = (if rows then o.H.fo.rows.toList else []) ++ l2 ++
        [Road.rowBatchForm P.y o.H,
          o.H.tV.p.rowForm (Desc.First.K4.rowsSummand P.y o.H sh) {}] ++ g46 ++ l7 ++ l89 ++ l10 ++
        o.H.fo.leaves.rowForm oneE pp.1 :: pp.2 ++ l12 := by
  unfold frontForms at h
  obtain ⟨sh, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨pp, a2, a3⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, b1, b2, b3, b4, b5, b6, b7, e⟩ :=
    Desc.First.K4.front_some a3
  obtain ⟨tT, hT⟩ := termsForms_tT b3
  rw [a2] at b6
  cases b6
  rw [embeddingForm_embL] at b7
  rw [oneHotForms_oneHotL o.v hp] at b5
  refine ⟨sh, pp, tT, g2, g46, g7, g89, g10, g12, a2, hT, normsForms_normsL b1, b2,
    termsForms_termsL hT hp b3, gatedForms_gatedL b4, b5, b7, ?_⟩
  rw [e, ← rowBatchForm_eq]

end OnBytes.Road.K4

namespace OnBytes.Desc.First.K4.Reads
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own HPlan2)
open VerifiableInference.Desc.K4Values (frontForms backForms)

/-- **What `frontForms` gives**, at either form. -/
theorem frontForms_covered {rows : Bool} {P : Pub} {g : Nat} {o : Own} {U : Fork}
    {l : List Aff} (hp : o.v.y.h.p3 = true) (h : frontForms rows P g o U = some l)
    (hK3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hw : InTab o.v o.H.wpl.row)
    (htV : InTab o.v o.H.tV.p.start)
    (hhd : InTab o.v o.hd.row)
    (hhd2 : ∀ x, o.hd2 = some x → InTab o.v x.row)
    (hlv : InTab o.v o.H.fo.leaves.start) :
    ∀ f ∈ l, InTab o.v f := by
  obtain ⟨sh, pp, tT, l2, g46, l7, l89, l10, l12, hpp, _, h2, h46, h7, h89, h10, h12, e⟩ :=
    OnBytes.Road.K4.frontForms_library hp h
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
                · cases rows with
                  | true => exact hK3 rfl f hf
                  | false => cases hf
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

/-- **`backForms o`.** -/
theorem backForms_covered {o : Own} (hS : InTab o.v o.K.rowS) (hA : InTab o.v o.K.fin.Alin)
    (hB : InTab o.v o.K.fin.Blin) (hm : InTab o.v o.wo.toWsMerged.p.start) :
    ∀ f ∈ backForms o, InTab o.v f := by
  intro f hf
  unfold backForms back at hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hS
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_slot _) hA
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_sub (entsIn_slot _) hB
  rcases List.mem_cons.mp hf with rfl | hf
  · exact entsIn_rowForm _ _ hm entsIn_empty
  cases hf

variable {P : Pub} {hpl : HPlan2} {g : Nat} {fo : Forest.Heard} {F0 G0 : Fork}
  {t u : OnBytes.K.Kc.Tape} {o : Own}

/-- Behind a hearing. -/
theorem frontForms_heard {rows : Bool} {U : Fork} {l : List Aff} {P' : Pub} {g' : Nat}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (h : frontForms rows P' g' o U = some l)
    (hK3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hlv : InTab o.v o.H.fo.leaves.start) : ∀ f ∈ l, InTab o.v f := by
  obtain ⟨a1, a2, a3, a4, _⟩ := hear_starts hh (inTab o.v)
  exact frontForms_covered (p3_of_hear hh) h hK3 a1 a2 a3 a4 hlv

/-- Behind a hearing. -/
theorem backForms_heard (hh : hearFl P hpl g fo F0 t = some (o, G0, u))
    (he : o.H.fo.cEnd.ents = #[]) : ∀ f ∈ backForms o, InTab o.v f := by
  obtain ⟨a, b, c⟩ := stack_covered_bare hh he
  exact backForms_covered a b c (hear_starts hh (inTab o.v)).2.2.2.2

end OnBytes.Desc.First.K4.Reads

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own HPlan2)
open OnBytes.Desc.First.K4 (hearFl)
open OnBytes.Desc.First.K4.Reads
open VerifiableInference.Desc.K4Values (frontForms backForms)
open VerifiableInference.Desc.K9L
open _root_.Fo.Tp (PadNames bare_ents)

variable {P : Pub} {hpl : HPlan2} {g : ℕ} {fo : Forest.Heard} {F0 G0 F' : Fork}
  {t u : OnBytes.K.Kc.Tape} {o : Own}

/-- **THE MAKE OF WHAT `frontForms` GIVES.** -/
theorem make_front {rows : Bool} {U : Fork} {l : List Aff} {P' : Pub} {g' : ℕ}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F') (h : frontForms rows P' g' o U = some l) : EntsMake o.v.iU3 l := by
  intro f hf x hx
  obtain ⟨a, b, _⟩ := row_zero (hear_tab hh) hK
    (frontForms_heard hh h (fun _ f hf => inTab_bare o.v (N.rows f hf).1)
      (inTab_bare o.v N.start.1) f hf x hx)
  exact ⟨b, a⟩

/-- **THE MAKE OF `backForms o`.** -/
theorem make_back (hh : hearFl P hpl g fo F0 t = some (o, G0, u))
    (hK : hpl.nU.getD 2 0 ≤ o.v.K3) (N : PadNames o.H.fo F') :
    EntsMake o.v.iU3 (backForms o) := by
  intro f hf x hx
  obtain ⟨a, b, _⟩ := row_zero (hear_tab hh) hK
    (backForms_heard hh (bare_ents N.cEnd.1) f hf x hx)
  exact ⟨b, a⟩

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **THE BODY OF THE CLAUSE entsFront.** -/
theorem entsFront_of {nU : Array ℕ} {q : α × Option Pub9} {rows : Bool} {U : Fork} {P' : Pub}
    {g' : ℕ}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F')
    (hs : ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π q.1).1 = some tlb → tlb.ix.U.getD 2 none = some o.v.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ l, frontForms rows P' g' o U = some l → EntsAt π nU q l :=
  fun _ e => ents_of_static π hs hU h0 (make_front hh hK N e)

/-- **THE BODY OF THE CLAUSE entsBack.** -/
theorem entsBack_of {nU : Array ℕ} {q : α × Option Pub9}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F')
    (hs : ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π q.1).1 = some tlb → tlb.ix.U.getD 2 none = some o.v.iU3)
    (h0 : 0 < nU.getD 2 0) : EntsAt π nU q (backForms o) :=
  ents_of_static π hs hU h0 (make_back hh hK N)

end VerifiableInference.Desc.LinkJoin

#print axioms OnBytes.Road.K4.frontForms_library
#print axioms OnBytes.Desc.First.K4.Reads.frontForms_covered
#print axioms OnBytes.Desc.First.K4.Reads.backForms_covered
#print axioms OnBytes.Desc.First.K4.Reads.frontForms_heard
#print axioms OnBytes.Desc.First.K4.Reads.backForms_heard
#print axioms VerifiableInference.Desc.LinkJoin.make_front
#print axioms VerifiableInference.Desc.LinkJoin.make_back
#print axioms VerifiableInference.Desc.LinkJoin.entsFront_of
#print axioms VerifiableInference.Desc.LinkJoin.entsBack_of
