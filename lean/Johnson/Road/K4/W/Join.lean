-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Join.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: every equation on a slot, every identity, every own
claim and the lookup's three claims are hypotheses. That the hypotheses can hold together: no
example is known. THE COUNT OF THE FOURTEEN FIELDS OF FrontWorth AND BackWorth, AS THEY ARE FILLED
HERE. Bare hypotheses: five fields (rowV, rowL, planes, stack, merge) and three members of lists
(the first of norms, the first and the fourth of gated). The claim restated as a hypothesis: five
fields (batch, terms, hot, sideA, sideB) and one member (the second of norms). By a law from the
library's terms at the cells: rows (21 forms for each norm), emb, the third member of norms and the
four end claims of gated. Nothing on soundness, on completeness or on any other property.

The fourteen worths of the two runs of the layers' own rounds (sub-protocol K4), `FrontWorth` and
`BackWorth` (Johnson/Road/K4/WorthGroups.lean), from a list of equations "a slot holds this term",
the norms' identities at the cells, the selector's identity at the lookup's token point, the own
claims of six sumchecks, the lookup's three claims, "every table holds what it says of Mm" (a
hypothesis in the free world; in the ledger's world it holds by the make of the entries entryTrue,
which nothing ties to what is committed: holds_item, W/Ground.lean), and public hypotheses: first in
a free world, then in the world of a ledger with the entries entryTrue. The statements on the groups
that are called here lie in this folder's other files.

  `OwnFront ρ W P o sh`   the own claims of four sumchecks that the run "front" lists.
  `OwnBack ρ W o`   the own claims of two sumchecks that the run "back" lists. ITS FIELD stack IS
      THE DEAREST OF THE SIX: see its docstring.
  `LookThree ρ W o pp`   the lookup's own claim on its leaves, and its two claims on its planes.
  `rowBatch_zero`   the row products' batch.
  `gated_parts`, `terms_part`   what a returned list of a group says of the public parts.
  `front_of_opened`   FrontWorth in a free world.
  `back_of_opened`   BackWorth in a free world.
  `front_item`, `back_item`   the two at the world of a ledger, a mask row and the entries
      entryTrue.
No property is claimed.
-/
import Johnson.Road.K4.W.Ends
import Johnson.Road.K4.W.JoinNorms
import Johnson.Road.K4.W.ByMake
import Johnson.Road.K4.W.HotEmb
import Johnson.Road.K4.W.Gated
import Johnson.Road.K4.WorthGroups
import Johnson.Road.K4.ListsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Reads Heard Pub Own TableAsk TableAt Ten)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell)
open OnBytes.Desc.First.K4 (termsForms gatedForms rowsSummand)

variable {K : Type} [Field K]

/-- **The own claims of four sumchecks, as "front" lists them.** This defines a hypothesis; the
definition claims nothing. -/
structure OwnFront (ρ : Reading K) (W : World K) (P : Pub) (o : Own) (sh : Array E) : Prop where
  squares : o.H.wpl.row.value ρ W = 0
  rowV : (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {}).value ρ W = 0
  gated1 : o.hd.row.value ρ W = 0
  gated2 : ∀ o2, o.hd2 = some o2 → o2.row.value ρ W = 0

/-- **The own claims of two sumchecks, as "back" lists them.** This defines a hypothesis; the
definition claims nothing. -/
structure OwnBack (ρ : Reading K) (W : World K) (o : Own) : Prop where
  /-- the batched sumcheck's own claim. The lookup's join and the second token sumcheck's own claim
  stand inside its start form (OnBytes/Desc/First/K4/Claims.lean, the head): so this field asks
  these two besides, and a law on the start form; the library's laws that set the start form against
  the sumcheck's sum (`whole_holds`, Johnson/Road/Rows/LayerEnds34.lean, and those that it rests on,
  Johnson/Road/FormsKeysCaller.lean) ask the library's eight calls, the fourth profile and a bound
  on each call's columns (hN, h4, hfl): by the two files' heads hfl fails at the small example's
  numbers; and, beneath these, `start_stack` (Johnson/Road/FormsKeysWhole.lean), which asks the
  calls' ties as a record in hfl's place -/
  stack : o.K.rowS.value ρ W = 0
  /-- the merge's own claim -/
  merge : (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}).value ρ W = 0

/-- **The lookup's three claims in "front".** This defines a hypothesis; the definition claims
nothing. -/
structure LookThree (ρ : Reading K) (W : World K) (o : Own) (pp : Aff × List Aff) : Prop where
  /-- the lookup's own claim on its leaves -/
  rowL : (o.H.fo.leaves.rowForm oneE pp.1).value ρ W = 0
  /-- its two claims on its planes: they read the world's entries of the tables on the planes'
  matrix -/
  planes : ∀ f ∈ pp.2, f.value ρ W = 0

/-- **The row products' batch** (group 3, first claim). -/
theorem rowBatch_zero {ρ : Reading K} {W : World K} (hρ : Numerals ρ) (y : Lay) (H : Heard)
    (hCl : W.slot H.tV.sCl = ∑ i ∈ range (ledNP y.h.xl * y.NI),
      ρ.val (H.omV.getD i zeroE) * W.slot (H.sPv + i)) :
    (Desc.First.K4.rowBatchForm y H).value ρ W = 0 := by
  rw [Road.K4.rowBatchForm_eq, rowBatch_value ρ W hρ, hCl, sub_self]

/-- Where the gated products' list returns, its public parts are there. -/
theorem gated_parts {P : Pub} {v : Env} {hd : Level} {hd2 : Option Level} {l : List Aff}
    (h : gatedForms P v hd hd2 = some l) :
    ∃ o2 ts tu tbA tbB, hd2 = some o2 ∧ v.y.T_ "s" = some ts ∧ v.y.T_ "u" = some tu ∧
      v.tabAt "af@Z_a" = some tbA ∧ v.tabAt "af@Z_b" = some tbB := by
  unfold gatedForms at h
  obtain ⟨e, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tA, c2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, c3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, c4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB, c6, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ts, tu, _, _, d1, d2, _, _, _⟩ := endsForms_open c3
  exact ⟨o, ts, tu, tA, tB, c4, d1, d2, c2, c6⟩

/-- Where the list of the second token sumcheck's values returns, that sumcheck was heard. -/
theorem terms_part {v : Env} {H : Heard} {l : List Aff} (h : termsForms v H = some l) :
    ∃ tT, H.tT = some tT := by
  unfold termsForms at h
  obtain ⟨tT, c1, _⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨tT, c1⟩

section Free
variable {ρ : Reading K} {W : World K} {h : Layer.Shape} {pc : List (List String)} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
  {pts : List (String × Array E)} {D : Dim} {P : Pub} {g : ℕ} {sh : Array E} {pp : Aff × List Aff}

/-- **THE TEN WORTHS OF "front", IN A FREE WORLD.** CONDITIONAL: on every hypothesis named. -/
theorem front_of_opened (G : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D)
    (Z : K4Sizes P o.v o.H o.hd o.hd2 D) (hρ : Numerals ρ) (Mm : Mats K)
    (hR : ∀ Fn ∈ o.funs, Holds ρ W tl o.v.iU3 o.v.K3 Mm Fn) (hg : o.v.g = g)
    (O : Opened (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) ρ W P o D (cellsOf D (cellsAt o.v.y Mm)))
    (I : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm)))
    (hH : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt ρ o.H.ztF))
    (R : OwnFront ρ W P o sh) (L : LookThree ρ W o pp) : FrontWorth ρ W P g o sh pp := by
  letI : Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
  obtain ⟨Z1, _, F, T3⟩ := ground_point G Z hρ Mm hR
  have N := ground_words G F
  refine
    { norms := norms_field F T3 Z O R.squares
      batch := ?_
      rowV := R.rowV
      rows := rows_field F T3 N Z O I
      terms := ?_
      gated := ?_
      hot := hot_zero' F hH
      rowL := L.rowL
      planes := L.planes
      emb := ?_ }
  · rw [Z.y]
    exact rowBatch_zero hρ o.v.y o.H O.cl8
  · intro x hx
    obtain ⟨tT, hT⟩ := terms_part hx
    exact terms_zero' hT (O.rt tT hT) (O.sc tT hT) (O.sel tT hT) x hx
  · intro x hx
    obtain ⟨o2, ts, tu, tbA, tbB, h2, hts, htu, hA, hB⟩ := gated_parts hx
    obtain ⟨GA, GB⟩ := ground_ends G Z hρ Mm hR h2 hts htu hA hB
    exact gated_zero Z.y h2 hts htu hA hB GA GB Z.la Z.lsF Z.lsFe Z.Lam Z.f Z.Pf Z.LamM Z.fe Z.Dfe
      R.gated1 (R.gated2 o2 h2) O.lv1L O.lv1R (O.lv2L o2 h2) (O.lv2R o2 h2) x hx
  · intro h0
    have e0 : o.v.g = 0 := by
      rw [hg]
      exact beq_iff_eq.mp h0
    exact embedding_zero F T3 e0 (O.emb e0)

/-- **THE FOUR WORTHS OF "back", IN A FREE WORLD.** CONDITIONAL: on both hypotheses. -/
theorem back_of_opened (O : OpenedBack ρ W o) (R : OwnBack ρ W o) : BackWorth ρ W o :=
  { stack := R.stack
    sideA := sideA_zero O.sideA
    sideB := sideB_zero O.sideB
    merge := R.merge }

end Free

section Item
variable {h : Layer.Shape} {pc : List (List String)} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
  {pts : List (String × Array E)} {D : Dim} {P : Pub} {g : ℕ} {sh : Array E} {pp : Aff × List Aff}

/-- **THE TEN WORTHS OF "front" AT THE ITEM's OWN WORLD.** "Every table holds" is proved there, by
the make of the entries; all else is a hypothesis. CONDITIONAL. -/
theorem front_item (G : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D)
    (Z : K4Sizes P o.v o.H o.hd o.hd2 D) (Mm : Mats Cb.Gl.E) (F₁ : Fork) (mask : ℕ → Cb.Gl.E)
    (hg : o.v.g = g)
    (O : Opened (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) Reading.gl
      (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P o D (cellsOf D (cellsAt o.v.y Mm)))
    (I : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm)))
    (hH : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF))
    (R : OwnFront Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P o sh)
    (L : LookThree Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) o pp) :
    FrontWorth Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P g o sh pp :=
  front_of_opened G Z gl_numerals Mm (holds_item G Mm F₁ mask) hg O I hH R L

/-- **THE FOUR WORTHS OF "back" AT THE ITEM's OWN WORLD.** CONDITIONAL. -/
theorem back_item (Mm : Mats Cb.Gl.E) (F₂ : Fork) (mask : ℕ → Cb.Gl.E)
    (O : OpenedBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o)
    (R : OwnBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o) :
    BackWorth Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o :=
  back_of_opened O R

end Item

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.rowBatch_zero
#print axioms OnBytes.Road.K4.W.gated_parts
#print axioms OnBytes.Road.K4.W.terms_part
#print axioms OnBytes.Road.K4.W.front_of_opened
#print axioms OnBytes.Road.K4.W.back_of_opened
#print axioms OnBytes.Road.K4.W.front_item
#print axioms OnBytes.Road.K4.W.back_item
