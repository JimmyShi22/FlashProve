-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Forms.lean: the shapes of the output head's 35 forms, as code on shapes, and
the law that ties that code to the forms' own text.

What it is not. No law on a value, a coefficient or a constant. It says nothing of where the letters
come from: what was heard and where the reads lie are letters here, and of each only the shape is
asked (LeavesAre, a premise). Nothing on any property of the protocol. It stands on
Johnson/Desc/First/Shape/Parts.lean.

The 35 forms (Johnson/Desc/Kinds/Head.lean: claims; HeadNorm.lean, Norm.lean, HeadCells.lean and
OnBytes/Desc/First/P6/NormRow.lean beneath it) are made by the forms' arithmetic of a few leaves:
variables of hidden scalars that were heard, the four sumchecks' own forms, and entries of reads.
The arithmetic lays terms one behind the other (Arith.lean). So a form's shape is a function of
the leaves' shapes and of the sizes.

  `LeafSh`      one field a leaf: its shape
  `LeavesAre L`  the letters' leaves have the shapes that L holds: one equation a field
  `digSh`, `row6Sh`, `carriesSh`, `rootSh`, `reciprocalSh`   the norm's row; `RowIs`, `dig_sh`,
                `row_is`, `carries_sh`, `lines_sh`: its laws, general in the digits
  `normSh` (29), `policySh` (4), `logitSh` (2), `formsSh`   THE CODE: a line a form, in the order
                of the text
  `formsSh_norm`, `formsSh_policy`, `formsSh_logits`   the code's list looked up under each name
  `norm_sh`, `atCosts_sh`, `summed_sh`, `policy_sh`, `logit_sh`   the law, run by run
  `claims_sh`   **under LeavesAre L the shapes of the forms of `claims`, run by run, are formsSh L**
THE CODE IS A SECOND TEXT BESIDE THE FORMS' OWN. It cannot drift unseen: claims_sh compares the two
at all letters.

-/
import Johnson.Desc.K6.Shape.Arith
import Johnson.Desc.Kinds.Law.FormsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open OnBytes (E)
open OnBytes.Model (Aff)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_add affSh_sub)

local infixl:65 " ⋆ " => AffSh.append

/-! ## The leaves -/

/-- The shapes of the leaves of which the head's forms and keys are made. W, P: the nine sums of
limb products and the seven row products, by number. sq, pr, nm, lg: the sumchecks "squares",
"products", "normed", "logits": the form that each leaves; its claimed sum, where it sends one; its
end values, by number. entryN, wide, entryH: an entry of a read, by number. -/
structure LeafSh where
  W : Nat → AffSh
  P : Nat → AffSh
  sqLeft : AffSh
  sqEnd : Nat → AffSh
  prLeft : AffSh
  prClaimed : AffSh
  prEnd : Nat → AffSh
  nmLeft : AffSh
  nmClaimed : AffSh
  nmEnd : Nat → AffSh
  lgLeft : AffSh
  lgClaimed : AffSh
  lgEnd : Nat → AffSh
  entryN : FinalNorm.Read → Nat → AffSh
  wide : Nat → AffSh
  entryH : Read → Nat → AffSh

/-- The letters' leaves have the shapes that L holds. A sumcheck's own form has one shape whatever
the summand on the shown end values is. -/
structure LeavesAre [Norm.Heard] [FinalNorm.Heard] [Heard] [FinalNorm.Reads] [Reads]
    (L : LeafSh) : Prop where
  W : ∀ s, affSh (Norm.W.getD s {}).var = L.W s
  P : ∀ n, affSh (Norm.P.getD n {}).var = L.P n
  sqLeft : ∀ S0, affSh (Norm.squares.left S0) = L.sqLeft
  sqEnd : ∀ j, affSh (Norm.squares.end_ j).var = L.sqEnd j
  prLeft : ∀ S0, affSh (Norm.products.left S0) = L.prLeft
  prClaimed : affSh Norm.products.claimed.var = L.prClaimed
  prEnd : ∀ j, affSh (Norm.products.end_ j).var = L.prEnd j
  nmLeft : ∀ S0, affSh (FinalNorm.normed.left S0) = L.nmLeft
  nmClaimed : affSh FinalNorm.normed.claimed.var = L.nmClaimed
  nmEnd : ∀ j, affSh (FinalNorm.normed.end_ j).var = L.nmEnd j
  lgLeft : ∀ S0, affSh (logits.left S0) = L.lgLeft
  lgClaimed : affSh logits.claimed.var = L.lgClaimed
  lgEnd : ∀ j, affSh (logits.end_ j).var = L.lgEnd j
  entryN : ∀ r i, affSh (FinalNorm.entry r i) = L.entryN r i
  wide : ∀ i, affSh (FinalNorm.wide i) = L.wide i
  entryH : ∀ r i, affSh (entry r i) = L.entryH r i

/-! ## The norm's row -/

/-- n digits from digit j on. -/
def digSh (D : Nat → AffSh) (j n : Nat) : AffSh := sumSh n fun i => D (j + i)

/-- The shapes of the fields of a position's row (P6.Row). -/
structure Row6Sh where
  (Vlo Vhi a b s0 sig l1 h1 Blo Bhi kap Rlo Rhi R q1 rr rq : AffSh)
  c : Nat → AffSh

/-- The fields' shapes, of the 99 digits' shapes: after P6.Row.ofDigits, line by line. -/
def row6Sh (D : Nat → AffSh) : Row6Sh :=
  let a := D 58 ⋆ D 59 ⋆ D 60 ⋆ D 61
  let b := D 62 ⋆ D 63
  let Rlo := digSh D 80 3
  let Rhi := digSh D 83 3
  { Vlo := digSh D 0 6, Vhi := digSh D 6 4, a, b, s0 := D 59, sig := a ⋆ b,
    l1 := digSh D 64 5, h1 := digSh D 69 5, Blo := digSh D 74 3, Bhi := digSh D 77 2, kap := D 79,
    Rlo, Rhi, R := Rlo ⋆ Rhi, q1 := digSh D 86 3, rr := digSh D 89 5, rq := digSh D 94 5,
    c := fun s => if s == 0 then noTerm else if s == 9 then D 9
      else digSh D (10 + 6 * (s - 1)) 6 }

/-- Field by field: the shape of the row made of digits is the row of shapes made of the digits'
shapes. -/
structure RowIs (r : P6.Row) (ρ : Row6Sh) : Prop where
  Vlo : affSh r.Vlo = ρ.Vlo
  Vhi : affSh r.Vhi = ρ.Vhi
  a : affSh r.a = ρ.a
  b : affSh r.b = ρ.b
  s0 : affSh r.s0 = ρ.s0
  sig : affSh r.sig = ρ.sig
  l1 : affSh r.l1 = ρ.l1
  h1 : affSh r.h1 = ρ.h1
  Blo : affSh r.Blo = ρ.Blo
  Bhi : affSh r.Bhi = ρ.Bhi
  kap : affSh r.kap = ρ.kap
  Rlo : affSh r.Rlo = ρ.Rlo
  Rhi : affSh r.Rhi = ρ.Rhi
  R : affSh r.R = ρ.R
  q1 : affSh r.q1 = ρ.q1
  rr : affSh r.rr = ρ.rr
  rq : affSh r.rq = ρ.rq
  c : ∀ s, affSh (r.c s) = ρ.c s

theorem dig_sh (D : Nat → Form) (Ds : Nat → AffSh) (hD : ∀ j, affSh (D j) = Ds j) (j n : Nat) :
    affSh (OnBytes.Desc.First.P6.dig D j n) = digSh Ds j n := by
  unfold OnBytes.Desc.First.P6.dig digSh
  rw [affSh_sumTo6]
  simp only [affSh_sm, hD]

open OnBytes.Desc.First.P6 (sm nat dig) in
theorem row_is (D : Nat → Form) (Ds : Nat → AffSh) (hD : ∀ j, affSh (D j) = Ds j) :
    RowIs (P6.Row.ofDigits D) (row6Sh Ds) := by
  have dg := dig_sh D Ds hD
  have ha : affSh (P6.Row.ofDigits D).a = (row6Sh Ds).a := by
    show affSh (sm 2 (D 58) + D 59 + sm (2 ^ 8) (D 60) + sm (2 ^ 16) (D 61)) =
      Ds 58 ⋆ Ds 59 ⋆ Ds 60 ⋆ Ds 61
    simp only [affSh_add, affSh_sm, hD]
  have hb : affSh (P6.Row.ofDigits D).b = (row6Sh Ds).b := by
    show affSh (D 62 + sm (2 ^ 8) (D 63)) = Ds 62 ⋆ Ds 63
    simp only [affSh_add, affSh_sm, hD]
  have hlo : affSh (P6.Row.ofDigits D).Rlo = (row6Sh Ds).Rlo := dg 80 3
  have hhi : affSh (P6.Row.ofDigits D).Rhi = (row6Sh Ds).Rhi := dg 83 3
  constructor
  · exact dg 0 6
  · exact dg 6 4
  · exact ha
  · exact hb
  · exact hD 59
  · show affSh ((P6.Row.ofDigits D).a + sm (2 ^ 24) (P6.Row.ofDigits D).b) =
      (row6Sh Ds).a ⋆ (row6Sh Ds).b
    rw [affSh_add, affSh_sm, ha, hb]
  · exact dg 64 5
  · exact dg 69 5
  · exact dg 74 3
  · exact dg 77 2
  · show affSh (D 79 - nat 4) = Ds 79
    rw [affSh_sub, affSh_nat, append_noTerm, hD]
  · exact hlo
  · exact hhi
  · show affSh ((P6.Row.ofDigits D).Rlo + sm (2 ^ 24) (P6.Row.ofDigits D).Rhi) =
      (row6Sh Ds).Rlo ⋆ (row6Sh Ds).Rhi
    rw [affSh_add, affSh_sm, hlo, hhi]
  · exact dg 86 3
  · exact dg 89 5
  · exact dg 94 5
  · intro s
    show affSh (if s == 0 then nat 0 else if s == 9 then D 9
        else dig D (10 + 6 * (s - 1)) 6 - nat (2 ^ 47)) =
      (if s == 0 then noTerm else if s == 9 then Ds 9 else digSh Ds (10 + 6 * (s - 1)) 6)
    by_cases h0 : (s == 0) = true
    · rw [if_pos h0, if_pos h0]
      rfl
    · rw [if_neg h0, if_neg h0]
      by_cases h9 : (s == 9) = true
      · rw [if_pos h9, if_pos h9]
        exact hD 9
      · rw [if_neg h9, if_neg h9, affSh_sub, dg, affSh_nat, append_noTerm]

/-- The nine carries. -/
def carriesSh (ρ : Row6Sh) (D W : Nat → AffSh) : List AffSh :=
  (List.range 9).map fun s => W s ⋆ ρ.c s ⋆ D s ⋆ ρ.c (s + 1)

/-- The root's four lines. -/
def rootSh (ρ : Row6Sh) (P : Nat → AffSh) : List AffSh :=
  [P 1 ⋆ ρ.Blo ⋆ ρ.Bhi, ρ.Vlo ⋆ P 0 ⋆ ρ.Blo ⋆ ρ.l1 ⋆ ρ.kap, ρ.Vhi ⋆ ρ.Bhi ⋆ P 2 ⋆ ρ.kap,
   ρ.l1 ⋆ ρ.h1 ⋆ ρ.sig]

/-- The reciprocal's four lines, where the letter "two" is a constant. -/
def reciprocalSh (ρ : Row6Sh) (P : Nat → AffSh) : List AffSh :=
  [P 4 ⋆ P 5 ⋆ ρ.q1, P 6, ρ.sig ⋆ ρ.s0 ⋆ P 3 ⋆ ρ.q1 ⋆ ρ.rr, ρ.rr ⋆ ρ.rq ⋆ ρ.sig]

theorem carries_sh (r : P6.Row) (ρ : Row6Sh) (hr : RowIs r ρ) (D Wf : Nat → Form)
    (Ds Ws : Nat → AffSh) (hD : ∀ j, affSh (D j) = Ds j) (hW : ∀ s, affSh (Wf s) = Ws s) :
    (OnBytes.Desc.First.P6.carries r D Wf).map affSh = carriesSh ρ Ds Ws := by
  rw [OnBytes.Desc.First.P6.carries_eq]
  unfold carriesSh
  rw [List.map_map]
  refine List.map_congr_left fun s _ => ?_
  show affSh (Wf s + r.c s - D s - OnBytes.Desc.First.P6.sm 256 (r.c (s + 1))) = _
  simp only [affSh_sub, affSh_add, affSh_sm, hW, hD, hr.c]

theorem lines_sh (r : P6.Row) (ρ : Row6Sh) (hr : RowIs r ρ) (Pf : Nat → Form) (Ps : Nat → AffSh)
    (hP : ∀ n, affSh (Pf n) = Ps n) (eps : E) (two : Form) (h2 : affSh two = noTerm) :
    (OnBytes.Desc.First.P6.lines r Pf eps two).map affSh = rootSh ρ Ps ++ reciprocalSh ρ Ps := by
  rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
    OnBytes.Desc.First.P6.reciprocal_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, rootSh, reciprocalSh, affSh_sub,
    affSh_add, affSh_sm, affSh_nat, affSh_const, hP, h2, hr.Vlo, hr.Vhi, hr.s0, hr.sig, hr.l1,
    hr.h1, hr.Blo, hr.Bhi, hr.kap, hr.q1, hr.rr, hr.rq, append_noTerm, noTerm_append]

/-! ## The code: the 35 forms' shapes -/

section Code
variable [Sizes] (L : LeafSh)

/-- Norm.squareForms at the head's one norm: three. -/
def squareSh : List AffSh :=
  [L.sqLeft, L.sqEnd 0 ⋆ L.sqEnd 1,
   L.sqEnd 0 ⋆ sumSh 1 fun _ => sumSh (d / S2) fun k => sumSh 5 fun l =>
     L.entryN .streamAtSquares (l * d / S2 + k)]

/-- Norm.productForms at the head's one norm: six. -/
def productSh : List AffSh :=
  let f := row6Sh (L.entryN .rowAtProducts)
  [L.prClaimed ⋆ sumSh 7 L.P, L.prLeft, L.prEnd 0 ⋆ f.a, L.prEnd 1 ⋆ f.b, L.prEnd 2 ⋆ f.Rlo,
   L.prEnd 3 ⋆ f.Rhi]

/-- Norm.rowForms at the head's one norm: seventeen. -/
def rowsSh : List AffSh :=
  let D := L.entryN .rowAtPV
  carriesSh (row6Sh D) D L.W ++ (rootSh (row6Sh D) L.P ++ reciprocalSh (row6Sh D) L.P)

/-- FinalNorm.normedForms: three. -/
def normedSh : List AffSh :=
  [L.nmLeft, L.nmEnd 0 ⋆ (row6Sh (L.entryN .rowAtNormed)).R,
   L.nmEnd 1 ⋆ sumSh (d / S2) fun i => sumSh 5 fun l =>
     L.entryN .streamAtNormed (l * d / S2 + i)]

/-- FinalNorm.forms: the run "norm". -/
def normSh : List AffSh := squareSh L ++ productSh L ++ rowsSh L ++ normedSh L

/-- atCosts. -/
def atCostsSh (n : Number) : AffSh :=
  sumSh n.digits.2 fun l => L.entryH .rowAtCosts (NR + n.digits.1 + l)

/-- summed. -/
def summedSh (n : Number) : AffSh :=
  sumSh n.digits.2 fun l => L.entryH .rowCount (NR + n.digits.1 + l)

/-- tableValuesAtCosts. -/
def tableCostsSh : AffSh :=
  sumSh 3 fun l => sumSh (JV / S2) fun i =>
    L.entryH .wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i)

/-- policy: mean, count, clip, table: the run "policy". -/
def policySh : List AffSh :=
  [summedSh L .paid ⋆ summedSh L .over ⋆ summedSh L .slackMean,
   summedSh L .over ⋆ summedSh L .slackCap,
   atCostsSh L .paid ⋆ atCostsSh L .slackClip,
   atCostsSh L .slackTable ⋆ tableCostsSh L]

/-- FinalNorm.actAt. -/
def actAtSh (x : Nat → AffSh) (k : Nat) : AffSh := x k ⋆ x (d + k)

/-- logitForms: the run "logits". -/
def logitSh : List AffSh :=
  [L.lgLeft, L.lgEnd 0 ⋆ sumSh d fun k => actAtSh (L.entryH .actAtLogits) k]

/-- **THE 35 FORMS' SHAPES, in the three named runs.** -/
def formsSh : List (String × List AffSh) :=
  [("norm", normSh L), ("policy", policySh L), ("logits", logitSh L)]

theorem formsSh_norm : (formsSh L).lookup "norm" = some (normSh L) := by
  simp [formsSh]

theorem formsSh_policy : (formsSh L).lookup "policy" = some (policySh L) := by
  simp [formsSh, List.lookup]

theorem formsSh_logits : (formsSh L).lookup "logits" = some (logitSh L) := by
  simp [formsSh, List.lookup]

end Code

/-! ## The law -/

section Law
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard] [FinalNorm.Reads] [Reads] (L : LeafSh) (h : LeavesAre L)
include h

theorem norm_sh : FinalNorm.forms.map affSh = normSh L := by
  have dPV : ∀ j, affSh (Norm.digit .rowsAtPV 0 j) = L.entryN .rowAtPV j := fun j =>
    (affSh_addN (FinalNorm.entry .rowAtPV j) off1).trans (h.entryN _ _)
  have dPr : ∀ j, affSh (Norm.digit .rowsAtProducts 0 j) = L.entryN .rowAtProducts j := fun j =>
    (affSh_addN (FinalNorm.entry .rowAtProducts j) off1).trans (h.entryN _ _)
  have dNm : ∀ j, affSh (FinalNorm.entry .rowAtNormed j + ((off1 : Nat) : Form)) =
      L.entryN .rowAtNormed j := fun j => by
    rw [affSh_add, affSh_natCast, append_noTerm]
    exact h.entryN _ _
  have rPV := row_is (Norm.digit .rowsAtPV 0) (L.entryN .rowAtPV) dPV
  have rPr := row_is (Norm.digit .rowsAtProducts 0) (L.entryN .rowAtProducts) dPr
  have rNm := row_is (fun j => FinalNorm.entry .rowAtNormed j + ((off1 : Nat) : Form))
    (L.entryN .rowAtNormed) dNm
  have hl : ∀ i l k, affSh (Norm.limb i l k) = L.entryN .streamAtSquares (l * d / S2 + k) :=
    fun _ _ _ => h.entryN _ _
  have e1 : Norm.squareForms.map affSh = squareSh L := by
    rw [Law.squareForms_eq]
    simp only [List.map_cons, List.map_nil, squareSh, affSh_sub, affSh_sumTo, affSh_smulE,
      h.sqLeft, h.sqEnd, hl]
  have e2 : Norm.productForms.map affSh = productSh L := by
    rw [Law.productForms_eq]
    simp only [List.map_cons, List.map_nil, productSh, affSh_sub, affSh_sumTo, affSh_smulE,
      h.prClaimed, h.P, h.prLeft, h.prEnd, rPr.a, rPr.b, rPr.Rlo, rPr.Rhi]
  have e3 : Norm.rowForms.map affSh = rowsSh L := by
    rw [Law.rowForms_eq, List.map_append,
      carries_sh _ _ rPV _ _ (L.entryN .rowAtPV) L.W dPV (fun s => by
        show affSh (Norm.W.getD (9 * 0 + s) {}).var = L.W s
        rw [Nat.mul_zero, Nat.zero_add]
        exact h.W s),
      lines_sh _ _ rPV _ L.P (fun n => by
        show affSh (Norm.P.getD (7 * 0 + n) {}).var = L.P n
        rw [Nat.mul_zero, Nat.zero_add]
        exact h.P n) _ _ (affSh_natCast _)]
    rfl
  have e4 : FinalNorm.normedForms.map affSh = normedSh L := by
    simp only [FinalNorm.normedForms, List.map_cons, List.map_nil, normedSh, affSh_sub,
      affSh_sumTo, affSh_smulE, h.nmLeft, h.nmEnd, h.entryN, rNm.R]
  show (Norm.squareForms ++ Norm.productForms ++ Norm.rowForms ++
    FinalNorm.normedForms).map affSh = _
  rw [List.map_append, List.map_append, List.map_append, e1, e2, e3, e4]
  rfl

theorem atCosts_sh (n : Number) : affSh (atCosts n) = atCostsSh L n := by
  unfold atCosts atCostsSh
  rw [affSh_sumTo]
  simp only [affSh_smulN, affSh_addE, h.entryH]

theorem summed_sh (n : Number) : affSh (summed n) = summedSh L n := by
  unfold summed summedSh
  rw [affSh_sumTo]
  simp only [affSh_smulN, affSh_addN, h.entryH]

theorem policy_sh : policy.map affSh = policySh L := by
  simp only [policy, mean, count, clip, table, tableValuesAtCosts, policySh, tableCostsSh,
    List.map_cons, List.map_nil, affSh_subN, affSh_sub, affSh_subE, affSh_add, affSh_Eadd,
    affSh_smulN, affSh_natCast, affSh_sumTo, summed_sh L h, atCosts_sh L h, h.entryH,
    append_noTerm]

theorem logit_sh : logitForms.map affSh = logitSh L := by
  simp only [logitForms, logitSh, actAtSh, FinalNorm.actAt, List.map_cons, List.map_nil,
    affSh_sub, affSh_sumTo, affSh_smulE, affSh_smulN, affSh_add, h.lgLeft, h.lgEnd, h.entryH]

/-- **Under LeavesAre L the shapes of the 35 forms, run by run, are formsSh L.** -/
theorem claims_sh : claims.map (fun c => (c.1, c.2.map affSh)) = formsSh L := by
  show [("norm", FinalNorm.forms.map affSh), ("policy", policy.map affSh),
    ("logits", logitForms.map affSh)] = _
  rw [norm_sh L h, policy_sh L h, logit_sh L h]
  rfl

end Law

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.dig_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.row_is
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.carries_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.lines_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.formsSh_norm
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.formsSh_policy
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.formsSh_logits
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.norm_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.atCosts_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.summed_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.policy_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.logit_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.claims_sh
