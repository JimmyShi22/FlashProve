-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPLangs.lean: the integer model, its conditions formed modulo the characteristic of the
field, as the model's side of a configuration; "the two languages agree" at it;
a value over p = 2^64 - 2^32 + 1.

This file puts a relation and its relaxation into a configuration, with the
constraints formed modulo the field's own characteristic; the index's side of the configuration is
Cm/TargetLangs.lean.
Definitions and statements (`Cm.Spec.target_p_langs` and the like); the proofs are in
Cm/TargetPLangsProofs.lean.
Why: a request's preamble over F shows conditions modulo the characteristic of F.
Cm/TargetPRel.lean has the pair at a variable prime (`Cm.TP.Ryes p s`, `Cm.TP.Rno p s`). Here that
pair stands in the configuration, at the characteristic p of F: the pair that a request's preamble
over F can show.

Main names:
  `targetCfP Cf₀ pl p s`: the configuration's data: the code's side of any Cf₀; index set,
    instances, cells and honest trace of the model; body and heldB (Cm/TargetLangs.lean); the
    relation pair (`Cm.TP.Ryes p s`, `Cm.TP.Rno p s`).
  `targetGlP s`: the value over p = 2^64 - 2^32 + 1: `targetCfP` at the code's side with room and
    the placing of Cm/TargetLangsGl.lean and that p.
Stated for all finite fields F of characteristic p with 2^61 - 1 ≤ p, all E (`target_p_props`: E
finite), every lawful table s, all Cf₀ and pl:
  `Spec.target_p_langs`: in the fields of `(targetCfP Cf₀ pl p s).conf`: (1) the two languages
    agree: whatever has a witness in `Rno` has one in `Ryes` (the clause "langs" of
    `Cb.LdModelDuty`); (2) if there is a witness in `Rno`, the honest trace is
    one (the clause says that the model's own program returns a relaxed witness whenever there
    is one);
    (3) if there is a witness in
    `Rno`, the honest trace is a witness in `Ryes`.
  `Spec.target_p_true`: the one language: the true requests (Cm/RelBase.lean: `TrueAt`).
  `Spec.target_p_model`: `Cb.LdCf.ModelOK`, if different entries of the index stand at different
    places.
  `Spec.target_p_props`: `ConfigurationWithOutOfDomainSample.Props b ((L choose 2) · err)` from `Cf₀.CodeOK L`, `Cf₀.PadBij`, b
    at most what the code hides, and that condition on places.
Stated at `targetGlP`:
  `Spec.target_p_guards`: in the fields of `(targetGlP s).conf`, five guards, (a) by `lawful_sRef`,
    the others from the facts of Cm/RelTrue.lean by `TP.lang_yes`, `lang_no`, `trace_iff`. (a) some
    table is lawful; (b) not empty: for all r < e ≤ 1,024, at the all-zero weights and the prompt of
    zeros, where the program computes nothing; (c) not everything: again at the all-zero weights (in
    (b), (c) the statement has "at every lawful table there is an index", in (b) "and a request":
    weights and prompt are those of the proof in Cm/TargetPLangsProofs.lean); (d) the index matters:
    at the reference scales (`sRef`) two indices and one request, a witness in `Ryes` at the one,
    none in `Rno` at the other; (e) the instance matters, at the reference scales. The weight lies
    on (d) and (e).

Limits: the clause "langs" and the five clauses on the configuration hold, under the hypotheses of
`Spec.target_p_langs` and `Spec.target_p_props`, at a model that computes, at a pair that stands at
the field's own prime: so the prime does not shut this pair out of a model's other duties. Another
obstacle stands, the request's and not the pair's: in the reference request as it is typed,
keys, summands and maps of a segment's front read the open oracle messages
alone (Cb/Req1/LdSegFront.lean: `frPscS`, `frPscT`; Cb/Req1/LdSegFrontRef.lean;
Cb/Req1/LdSegRefLkpPre.lean), never the encoded index; so no model whose conditions multiply
weights with cells, this one among them, can meet the duty on the steps between blocks there. (A
reading of types; no theorem.)

Of the other duties nothing is shown but the one equivalence with the segments' conditions, stated
and proved at `Gl.p`: Cm/TargetSegAll.lean with its proofs (`Spec.equiv_of`, `Spec.equiv_to`, for
all segments with `SegsOK`), Cm/TargetSegModel.lean with its proofs (`Cm.Seg.TS.segs_ok`: such
segments exist). Degrees, and all that ties blocks and segments, are not shown.
Of the further duties this head says nothing.
What the heads of Cm/TargetPRel.lean (which list of conditions this is; the threshold on p),
Cm/TargetLangs.lean (the index set is a type; pl is any placing; nothing on weights-formedness) and
Cm/TargetLangsGl.lean (the code's side of the value is a toy: 2^40 rows of one entry; no object, no
request; all indices in the guards are made up) list as not said is not said here either.
Terms: lean/GLOSSARY.md.
The notions follow the worked example named in lean/CREDITS.md; the text is this library's.
-/
import Cm.TargetLangsGl
import Cm.TargetPRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Iop Prob Hiop Cb
open Inst.Model.Layout (kRef hRef)

/-- The data of the configuration at the model, the conditions modulo p. -/
def targetCfP {F E : Type} [Field F] [Field E] [Algebra F E] (Cf₀ : LdCf F E)
    (pl : TargetEnt → Cf₀.Row × Cf₀.Lay) (p : ℕ) (s : Scales) : LdCf F E where
  C₀ := Cf₀.C₀
  hp := Cf₀.hp
  v := Cf₀.v
  J₀ := Cf₀.J₀
  Pd := Cf₀.Pd
  Lay := Cf₀.Lay
  lay := Cf₀.lay
  plE := Cf₀.plE
  Z := Cf₀.Z
  eM := Cf₀.eM
  rank := Cf₀.rank
  I := Idx
  Xm := Instance ppref
  Cells := Trace
  Ryes := TP.Ryes p s
  Rno := TP.Rno p s
  trace := trace2 s
  cells0 := cells0
  body := targetBody Cf₀ pl
  heldB := targetHeld Cf₀ pl

/-- The value over p = 2^64 - 2^32 + 1. -/
def targetGlP (s : Scales) : LdCf Gl.F Gl.E :=
  targetCfP targetGlRoom targetGlPl Gl.p s

namespace Spec

/-- Under the hypotheses of its statement, the two languages agree (whatever has a witness in `Rno`
has one in `Ryes`), the conditions formed modulo the characteristic of F. -/
def target_p_langs : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (p : ℕ) [CharP F p], 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay),
        (∀ i x w,
          (targetCfP Cf₀ pl p s).conf.Rno i x w → ∃ w', (targetCfP Cf₀ pl p s).conf.Ryes i x w') ∧
        (∀ i x w, (targetCfP Cf₀ pl p s).conf.Rno i x w →
          (targetCfP Cf₀ pl p s).conf.Rno i x ((targetCfP Cf₀ pl p s).conf.trace i x)) ∧
        (∀ i x w, (targetCfP Cf₀ pl p s).conf.Rno i x w →
          (targetCfP Cf₀ pl p s).conf.Ryes i x ((targetCfP Cf₀ pl p s).conf.trace i x))

/-- The one language: the true requests. -/
def target_p_true : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (p : ℕ) [CharP F p], 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay) (i : Idx) (x : Instance ppref),
        ((∃ w, (targetCfP Cf₀ pl p s).conf.Rno i x w) ↔ TrueAt s.kap s.nf i x) ∧
        ((∃ w, (targetCfP Cf₀ pl p s).conf.Ryes i x w) ↔ TrueAt s.kap s.nf i x)

/-- The model's conditions on the configuration's data. -/
def target_p_model : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (p : ℕ) [CharP F p], 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay),
        Function.Injective (targetAt Cf₀ pl) → (targetCfP Cf₀ pl p s).ModelOK

/-- Under the hypotheses of its statement: the configuration has its properties. -/
def target_p_props : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (p : ℕ) [CharP F p],
    2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay) (L b : ℕ),
        Function.Injective (targetAt Cf₀ pl) → Cf₀.CodeOK L → Cf₀.PadBij → b ≤ Cf₀.C₀.b →
        (targetCfP Cf₀ pl p s).conf.Props b (L.choose 2 * Cf₀.Z.err)

/-- Guards, in the fields of `(targetGlP s).conf`. -/
def target_p_guards : Prop :=
  sRef.Lawful ∧
  (∀ s : Scales, s.Lawful →
    ∀ rF eF : Fin (ppref.T + 1), rF.val < eF.val →
      ∃ (i : Idx) (x : Instance ppref),
        x.rF = rF ∧ x.eF = eF ∧ (targetGlP s).conf.Ryes i x ((targetGlP s).conf.trace i x)) ∧
  (∀ s : Scales, s.Lawful →
    ∃ i : Idx, ∀ (x : Instance ppref) (t : ℕ),
      x.r ≤ t → t < x.e → x.w t ≠ 0 → ¬ ∃ w, (targetGlP s).conf.Rno i x w) ∧
  (∃ (i i' : Idx) (x : Instance ppref),
    (∃ w, (targetGlP sRef).conf.Ryes i x w) ∧ ¬ ∃ w, (targetGlP sRef).conf.Rno i' x w) ∧
  (∃ (i : Idx) (q q' : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V),
    q targetLast = q' targetLast ∧
    (∃ w, (targetGlP sRef).conf.Ryes i (Instance.nextOf q y) w) ∧
    ¬ ∃ w, (targetGlP sRef).conf.Rno i (Instance.nextOf q' y) w)

end Spec

end Cm
