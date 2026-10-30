-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5HolesMet.lean

A second case in which the named hypotheses of Lane5Holes.lean hold, with a reading that looks at
the witness: the relation is the library's own relaxed relation with the cost ledger, a witness is a
trace, and every link holds the matrices of THAT trace. Each clause comes out of the relation
itself: the range is its first part, the bound on the cells its second, the identities and keys of
each segment its third. No step goes through "the request is true under its policy".

Why: "holes_met" (Lane5Holes.lean) reads the honest trace, whatever the witness is, and gets the
clauses from the truth of the request. That shows that the hypotheses can hold together. Here they
are shown from the parts of that relation, which are these clauses in other letters: a restating,
no protocol's block. It shows that they are not empty, and no more.

Main theorems:
* "small_read": a trace below 2^18 in absolute value has matrices that are below 2^18 in absolute
  value at the place of every own cell.
* "premise_read", "meaning_read": a witness of the relaxed relation with the cost ledger gives
  "Premise" (Lane5.lean) and "Meaning" (Lane5Mean.lean) at the index's matrix, with the witness's
  own matrices for every link.
* "holes_met_read": "MeanHoles" holds of that relation and that reading, at every table of scales
  and every policy: neither a lawful table nor a condition on the policy is used.

Not claimed: that "MeanHoles" holds of any other relation or reading; that any protocol's
out-claims give this relation. All 25 links hold one and the same family of matrices here, so every
seam holds by definition: the case says nothing on how cells are handed from link to link. All that
Lane5.lean, Lane5Ledger.lean, Lane5Mean.lean and Lane5Holes.lean do not claim.

-/
import Johnson.Road.Lane5Holes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

section Read
variable {s : Cm.Scales} {pol : AcceptancePolicy} {i : Cm.Idx} {x : Instance ppref} {w : Inst.Model.All.Trace}

/-- The bound on a trace is the bound on its matrices at the places of own cells. -/
theorem small_read (hB : Cm.Below (2 ^ 18) w) (n : Cm.Seg.Name) (hn : n.Valid Cm.Seg.Hd.main) :
    |Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.main w) n.place| < 2 ^ 18 := by
  rw [Cm.lay_toMat_place Cm.Seg.Hd.main Policy.mainOK w n hn]
  exact (Policy.lay_below_main (2 ^ 18) w).1 hB n hn

/-- **A witness's own matrices meet the premise.** -/
theorem premise_read (h : Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s pol) i x w) :
    Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x
      fun _ => Cm.Seg.toMat Cm.Seg.Hd.main w :=
  ⟨fun k hk =>
      linkOK_of_holds (fun n hn _ => small_read h.2.1 n hn)
        (((Policy.segPol_equiv s pol i.mat x).2 w).1 h.2.2 k hk),
    fun _ _ _ _ => rfl⟩

/-- The same as the 25 named clauses. -/
theorem meaning_read (h : Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s pol) i x w) :
    Meaning s pol i.mat x fun _ => Cm.Seg.toMat Cm.Seg.Hd.main w :=
  meaning_of_premise (premise_read h)

end Read

/-- **They can be met by a reading of the witness**: at the library's own relaxed relation with the
cost ledger, with the witness's own matrices for every link. -/
theorem holes_met_read (s : Cm.Scales) (pol : AcceptancePolicy) :
    MeanHoles s pol (fun i x w => Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s pol) i x w)
      (fun _ _ w _ => Cm.Seg.toMat Cm.Seg.Hd.main w) :=
  ⟨fun _ _ _ h => h.1, fun g hg _ _ _ h => (meaning_read h).layers g hg,
    fun g hg _ _ _ h => (meaning_read h).attention g hg, fun _ _ _ h => (meaning_read h).head⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.premise_read
#print axioms OnBytes.Road.L5.holes_met_read
