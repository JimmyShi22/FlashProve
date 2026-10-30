-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/QkOfPlan.lean: CONDITIONAL.

What is here. What the library's law on the panel of queries and keys asks of the sizes and of the
shifts of queries and keys (the hypothesis hQK of Law/JoinMade.lean's `joinWorth_made`; the field qk
of Law/W/FootB1.lean's `FootB1`), from public facts on the plan of the feed-forward layers' own
rounds (sub-protocol K4). Its second half, on the shifts, follows from the verifier's own test on
the file of scales: the library's `hk_of_scalesHeld` (Johnson/Road/FormsKeysRef.lean), as in the
library's `qkOk_of` (Johnson/Road/Rows/LayerEnds34Ref.lean). Its first half, `Dim.ChOK`, stays a
hypothesis (C) but at the library's reference sizes, where it is the library's `ref_chOK`.

  `qk_of_plan`   at the plan's own scales, group and layout: the second half from `K4Plan`; the
     first is C, handed on.
  `qk_of_ground`   **the same at an environment v's own scales, group and layout, from `K4Ground` at
     v and C.**
  `qk_of_hear`   the same at what a hearing returned, from the hearing's return, `K4Plan`, C.
  `qk_ref`   `qk_of_ground` at the library's reference sizes: C is no hypothesis there.

Limits. NOTHING NEW IS SHOWN: four calls. `K4Plan` and `K4Ground` are hypotheses here: public facts
on the layout, on the file of scales and on the group (Johnson/Road/K4/W/GroundOfHear.lean and
Johnson/Road/K4/W/Ground.lean say where they hold); of each, four fields alone are spent (lay, sw,
scales, grp), and of sw the switch p3 alone. THE FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE
LIBRARY's ELEVEN SWITCHES, routed experts among them: AT EVERY OTHER SHAPE THESE STATEMENTS SAY
NOTHING; D is a variable, no more. C is a hypothesis in the first three statements. The bound l <
D.nl of the second half is not spent: the library's statement holds at every l.

No property is claimed.
-/
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.NormWordsOfHear
import Johnson.Road.FormsKeysRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open OnBytes.Model (Fork HTailF2)
open OnBytes.Model.Layer (Own TableAsk TableAt)
open OnBytes.Road (sclOf hk_of_scalesHeld admitted_of_layout)
open OnBytes.Road.K4 (env_of_hear)
open OnBytes.Road.K4.W (K4Plan K4Ground)
open OnBytes.Desc.First.K4 (engFl hear)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim ref_chOK)

/-- **At the plan's own scales, group and layout**: the second half; the first is the hypothesis C,
handed on. CONDITIONAL: on A and C. -/
theorem qk_of_plan {h : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    {P : OnBytes.Model.Layer.Pub} {g : ℕ} {tl : HTailF2} {D : Dim}
    (A : K4Plan h pc P g tl D) (C : D.ChOK) :
    letI : Inst.Model.Scl := sclOf h P.sc g P.y.Lam
    D.ChOK ∧ ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk) :=
  And.intro C fun l _ =>
    hk_of_scalesHeld (admitted_of_layout A.lay A.sw.p3) A.scales A.grp D l

/-- **AT AN ENVIRONMENT's OWN SCALES, GROUP AND LAYOUT**: the second half; the first is the
hypothesis C, handed on. CONDITIONAL: on Gr and C. -/
theorem qk_of_ground {h : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    {v : OnBytes.Model.Layer.Env} {rd : OnBytes.Model.Layer.Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    {tl : HTailF2} {H : OnBytes.Model.Layer.Heard} {hd : OnBytes.Model.Level}
    {hd2 : Option OnBytes.Model.Level} {pts : List (String × Array E)}
    {funs : Array OnBytes.Model.HFun} {D : Dim} (Gr : K4Ground h pc v rd r tl H hd hd2 pts funs D)
    (C : D.ChOK) :
    letI : Inst.Model.Scl := sclOf h v.sc v.g v.y.Lam
    D.ChOK ∧ ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk) :=
  And.intro C fun l _ =>
    hk_of_scalesHeld (admitted_of_layout Gr.lay Gr.sw.p3) Gr.scales Gr.grp D l

/-- **At what a hearing returned**: the second half; the first is the hypothesis C, handed on.
CONDITIONAL: on the hearing's return, A and C. -/
theorem qk_of_hear {P : OnBytes.Model.Layer.Pub} {hp : OnBytes.Model.Layer.HPlan2} {g : ℕ}
    {fo : OnBytes.Model.Forest.Heard} {F G : Fork} {t u : OnBytes.K.Kc.Tape} {o : Own}
    (hH : hear engFl P hp g fo F t = some (o, G, u)) {h : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan h pc P g tl D) (C : D.ChOK) :
    letI : Inst.Model.Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
    D.ChOK ∧ ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk) := by
  obtain ⟨vy, vs, vg, _⟩ := env_of_hear hH
  rw [vy, vs, vg]
  exact qk_of_plan A C

/-- **At the library's reference sizes.** CONDITIONAL: on Gr. -/
theorem qk_ref {h : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    {v : OnBytes.Model.Layer.Env} {rd : OnBytes.Model.Layer.Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    {tl : HTailF2} {H : OnBytes.Model.Layer.Heard} {hd : OnBytes.Model.Level}
    {hd2 : Option OnBytes.Model.Level} {pts : List (String × Array E)}
    {funs : Array OnBytes.Model.HFun} (Gr : K4Ground h pc v rd r tl H hd hd2 pts funs DF) :
    letI : Inst.Model.Scl := sclOf h v.sc v.g v.y.Lam
    DF.ChOK ∧ ∀ l, l < DF.nl →
      (DF.Pl l).kq = (DF.Pl l).kk ∨ (16 ≤ (DF.Pl l).kq ∧ 16 ≤ (DF.Pl l).kk) :=
  qk_of_ground Gr ref_chOK

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.qk_of_plan
#print axioms ProofFile.Honest.K4.qk_of_ground
#print axioms ProofFile.Honest.K4.qk_of_hear
#print axioms ProofFile.Honest.K4.qk_ref
