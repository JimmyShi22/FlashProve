-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5Ledger.lean

The premise of Lane5.lean at the head with the cost ledger: the request is true under its policy.

The family of segments is "Policy.segPol s pol" (Policy/Seg/All.lean): the library's own first 24
segments, and as the last the head with the cost ledger at the policy pol. This is the head that the
programs run. The first 24 clauses of the premise and its seam are those of the use at the plain
head but for the shape of the head; the 25th differs.

The road is the plain use's: the premise gives all 25 segments' conditions at one family of matrices
(Lane5.lean); these give a witness of the relaxed relation with the ledger; at a lawful table and a
policy with "Policy.PolCond" every such witness shows that the request is true under the policy.

What this use gives: EVERY request with r < e, judged by its policy on the costs of its tokens; the
next token is the case r = 1,023, e = 1,024.

Main theorems:
* "laws_main": the family is as Lane5.lean asks ("Policy.segsPol_ok").
* "rnoL_of_premise": a witness of "Policy.LedgerRel.Rno" at the protocol's prime
  ("Policy.segPol_equiv"; the proof is that of "Policy.segPol_force", which uses the bound at the
  places of cells alone).
* "under_of_premise": the request is true under the policy ("Policy.ledger_forces").
* "rinfR_of_premise": the same in the letters of the integer program's relation.
* "premiseL_iff": at a lawful table and such a policy: r < e and some matrices meet the premise, if
  and only if the request is true under the policy.

Not claimed: all that Lane5.lean does not claim; that a table of scales or a policy read from a file
is lawful; that a stored table of weights is a well-formed index.

-/
import Policy.Seg.All
import Policy.Rel.LedgerRelLaws
import Johnson.Road.Lane5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-- The family of segments with the ledger's head is as Lane5.lean asks. -/
theorem laws_main (s : Cm.Scales) (pol : AcceptancePolicy) : SegLaws Cm.Seg.Hd.main (Policy.segPol s pol) :=
  ⟨Policy.mainOK, (Policy.segsPol_ok s pol).wf, (Policy.segsPol_ok s pol).places⟩

section Ledger
variable {s : Cm.Scales} {pol : AcceptancePolicy} {i : Cm.Idx} {x : Instance ppref} {A : ℕ → Mx}

/-- **The premise gives a witness of the relaxed relation with the cost ledger.** -/
theorem rnoL_of_premise (hre : x.r < x.e)
    (P : Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A) :
    Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s pol) i x
      (Cm.Seg.ofMat Cm.Seg.Hd.main (one A)) := by
  refine ⟨hre, (Policy.lay_below_main (2 ^ 18) _).2 fun n hn => ?_,
    ((Policy.segPol_equiv s pol i.mat x).1 (one A)).2
      fun _ hk => holds_one (laws_main s pol) P hk⟩
  show |Cm.Seg.get (Cm.Seg.ofMat Cm.Seg.Hd.main (one A)) n| < 2 ^ 18
  rw [Cm.lay_ofMat_get]
  unfold Cm.Seg.rd
  rw [if_pos hn]
  exact small_one (laws_main s pol) P n hn

/-- **At a lawful table and a policy within its bounds the request is true under the policy.** -/
theorem under_of_premise (hs : s.Lawful) (hpol : Policy.PolCond pol) (hre : x.r < x.e)
    (P : Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A) :
    Policy.IsTrueUnder s pol i x :=
  Policy.ledger_forces Cb.Gl.p Code.pGold_prime Policy.ledger_gl_big (Policy.ppOf s pol)
    (Policy.tableOK_ppOf hs hpol) i x _ (rnoL_of_premise hre P)

/-- The same in the letters of the integer program's relation. -/
theorem rinfR_of_premise (hs : s.Lawful) (hpol : Policy.PolCond pol) (hre : x.r < x.e)
    (P : Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A) :
    RinfR ppref s.kap s.nf (fun _ => tbRef) pol i.index x :=
  under_of_premise hs hpol hre P

/-- The matrices of the honest trace, the same for every link, meet the premise of a request that is
true under the policy; and such a request has r < e. -/
theorem premiseL_of_under (hs : s.Lawful) (hpol : Policy.PolCond pol)
    (ht : Policy.IsTrueUnder s pol i x) :
    x.r < x.e ∧ Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x
      fun _ => Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x) :=
  have H := Policy.segPol_admit s pol i x _
    ((Policy.ledger_trace_iff Cb.Gl.p Code.pGold_prime Policy.ledger_gl_big (Policy.ppOf s pol)
      (Policy.tableOK_ppOf hs hpol) i x).2 ht)
  ⟨H.1,
    fun k hk =>
      linkOK_of_holds
        (fun n hn _ =>
          lt_trans (H.2.1 n.place (Cm.lay_inShape _ Policy.mainOK n hn)) (by norm_num))
        (H.2.2 k hk),
    fun _ _ _ _ => rfl⟩

/-- **The premise asks neither too much nor too little.** -/
theorem premiseL_iff (hs : s.Lawful) (hpol : Policy.PolCond pol) :
    (x.r < x.e ∧ ∃ A, Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A) ↔
      Policy.IsTrueUnder s pol i x :=
  ⟨fun ⟨hre, _, P⟩ => under_of_premise hs hpol hre P,
    fun ht => ⟨(premiseL_of_under hs hpol ht).1, _, (premiseL_of_under hs hpol ht).2⟩⟩

end Ledger

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.rnoL_of_premise
#print axioms OnBytes.Road.L5.under_of_premise
#print axioms OnBytes.Road.L5.rinfR_of_premise
#print axioms OnBytes.Road.L5.premiseL_iff
