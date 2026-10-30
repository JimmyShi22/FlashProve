-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5Holes.lean

The meaning's half of a proof file's first chain as named hypotheses on a relation, by group, and
the step "language" proved from them: whatever witness meets the relation, the request is true under
its policy.

The file is written for ANY relation "Rno i x w" between an index, a request and a witness of any
type W, and ANY reading "mx i x w" of 25 families of integer matrices off them. Rno stands for what
the out-claims of a protocol's blocks, chained, give; mx for what the arrays of each link hold. The
file says nothing on either: they are letters. So whether a hypothesis is true cannot be asked here:
it can be asked only where Rno and mx are closed terms, named by whoever takes "MeanHoles" as a
premise.

Main definitions and theorems:
* "HoleR Rno": a request with a witness has r < e.
* "HoleG s pol Rno mx g", "HoleA s pol Rno mx g", "HoleH s pol Rno mx": whatever witness meets the
  relation, the matrices read off it meet "MeanG" at group g, "MeanA" at group g, "MeanH"
  (Lane5Mean.lean), at the index's matrix of weights: the link's own cells are below 2^18 in
  absolute value, every identity of its segment is 0, every key of its segment is an entry of its
  table, and at every place that its segment may read it holds what the owner's link holds there.
  So each of these 25 is a bundle of four clauses, not one equation of the model.
* "MeanHoles s pol Rno mx": these, gathered: fields "range", "layers", "attention", "head": 26
  named hypotheses.
* "language_of_holes": at a lawful table and a policy with "Policy.PolCond": under "MeanHoles" every
  request with a witness is true under its policy.
* "holes_met": a case in which all of them hold: the library's own relaxed relation with the cost
  ledger, with the honest trace's matrices for every link. That reading does not look at the
  witness, and the proof goes through "the request is true": it shows that the hypotheses can hold
  together. With the witness's own matrices, each clause out of the relation itself:
  "holes_met_read" (Lane5HolesMet.lean).
* "holes_iff_language": WHAT THEY WEIGH. For some reading mx the 26 say what "language" says, no
  more and no less. So they split that one statement into 26 named parts; they are smaller than it
  only at a reading that is fixed beforehand; none is given in these files. What
  "language_of_holes" proves beyond unpacking: that 25 families of matrices glue along the places
  that segments read, and the library's step from conditions modulo the prime with small cells to
  the integer statement; both on the library's own 25 segments. A lawful table of scales is asked
  beside the 26.
* "holes_bite": they are not empty words: under a policy that no counted position can meet,
  "MeanHoles" leaves no witness to any request that has a counted position.

Not claimed: that "MeanHoles" holds of any relation but the one of "holes_met"; that any protocol's
out-claims give a relation of which it holds; the step from "true under its policy" to a statement
on output tokens (it is taken in Lane5Sound.lean). All that Lane5.lean, Lane5Ledger.lean and
Lane5Mean.lean do not claim.

-/
import Johnson.Road.Lane5Mean

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

section Holes
variable {W : Type} (s : Cm.Scales) (pol : AcceptancePolicy) (Rno : Cm.Idx → Instance ppref → W → Prop)
  (mx : Cm.Idx → Instance ppref → W → ℕ → Mx)

/-! ## 1. The named hypotheses -/

/-- **The request's range.** -/
def HoleR : Prop := ∀ i x w, Rno i x w → x.r < x.e

/-- **Group g of layers.** -/
def HoleG (g : ℕ) : Prop := ∀ i x w, Rno i x w → MeanG s pol i.mat x (mx i x w) g

/-- **Attention of group g.** -/
def HoleA (g : ℕ) : Prop := ∀ i x w, Rno i x w → MeanA s pol i.mat x (mx i x w) g

/-- **The head with the cost ledger.** -/
def HoleH : Prop := ∀ i x w, Rno i x w → MeanH s pol i.mat x (mx i x w)

/-- **All of them, gathered.** -/
structure MeanHoles : Prop where
  range : HoleR Rno
  layers : ∀ g < 12, HoleG s pol Rno mx g
  attention : ∀ g < 12, HoleA s pol Rno mx g
  head : HoleH s pol Rno mx

/-! ## 2. Language -/

variable {s pol Rno mx}

/-- **Language**: whatever witness meets the relation, the request is true under its policy. -/
theorem language_of_holes (hs : s.Lawful) (hpol : Policy.PolCond pol)
    (H : MeanHoles s pol Rno mx) : ∀ i x w, Rno i x w → Policy.IsTrueUnder s pol i x :=
  fun i x w h => back_of_meaning hs hpol (H.range i x w h)
    ⟨fun g hg => H.layers g hg i x w h, fun g hg => H.attention g hg i x w h, H.head i x w h⟩

/-- **They bite**: under a policy that no counted position can meet, no request with a counted
position has a witness. -/
theorem holes_bite (hs : s.Lawful) (hpol : Policy.PolCond pol) (h1 : pol.theta < 256)
    (h2 : 256 ≤ pol.C) (H : MeanHoles s pol Rno mx) (i : Cm.Idx) (x : Instance ppref) (w : W)
    (hN : 0 < x.NB) : ¬ Rno i x w :=
  fun h => Policy.TrueGuards.none_true s pol h1 h2 i x hN (language_of_holes hs hpol H i x w h)

end Holes

/-! ## 3. A case in which they hold -/

/-- **They can be met**: at the library's own relaxed relation with the cost ledger, with the honest
trace's matrices for every link. -/
theorem holes_met {s : Cm.Scales} {pol : AcceptancePolicy} (hs : s.Lawful) (hpol : Policy.PolCond pol) :
    MeanHoles s pol (fun i x w => Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s pol) i x w)
      (fun i x _ _ => Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x)) := by
  have key : ∀ i x w, Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s pol) i x w →
      x.r < x.e ∧ Meaning s pol i.mat x
        (fun _ => Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x)) := by
    intro i x w h
    have ht : Policy.IsTrueUnder s pol i x :=
      Policy.ledger_forces Cb.Gl.p Code.pGold_prime Policy.ledger_gl_big (Policy.ppOf s pol)
        (Policy.tableOK_ppOf hs hpol) i x w h
    exact ⟨(premiseL_of_under hs hpol ht).1, meaning_of_premise (premiseL_of_under hs hpol ht).2⟩
  exact ⟨fun i x w h => (key i x w h).1, fun g hg i x w h => (key i x w h).2.layers g hg,
    fun g hg i x w h => (key i x w h).2.attention g hg, fun i x w h => (key i x w h).2.head⟩

/-! ## 4. What the named hypotheses weigh -/

/-- **For some reading they say what "language" says, no more and no less.** -/
theorem holes_iff_language {W : Type} {s : Cm.Scales} {pol : AcceptancePolicy} (hs : s.Lawful)
    (hpol : Policy.PolCond pol) (Rno : Cm.Idx → Instance ppref → W → Prop) :
    (∃ mx, MeanHoles s pol Rno mx) ↔ ∀ i x w, Rno i x w → Policy.IsTrueUnder s pol i x := by
  refine ⟨fun ⟨_, H⟩ => language_of_holes hs hpol H, fun T =>
    ⟨fun i x _ _ => Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x), ?_⟩⟩
  have key : ∀ i x w, Rno i x w → x.r < x.e ∧ Meaning s pol i.mat x
      (fun _ => Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x)) :=
    fun i x w h => ⟨(premiseL_of_under hs hpol (T i x w h)).1,
      meaning_of_premise (premiseL_of_under hs hpol (T i x w h)).2⟩
  exact ⟨fun i x w h => (key i x w h).1, fun g hg i x w h => (key i x w h).2.layers g hg,
    fun g hg i x w h => (key i x w h).2.attention g hg, fun i x w h => (key i x w h).2.head⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.holes_iff_language
#print axioms OnBytes.Road.L5.language_of_holes
#print axioms OnBytes.Road.L5.holes_bite
#print axioms OnBytes.Road.L5.holes_met
