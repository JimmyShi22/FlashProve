-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5Plain.lean

The premise of Lane5.lean at the plain head: the reply is the model's first choice at the last
position. The plain head is the library's; the programs run the head with the cost ledger
(Lane5Ledger.lean), not this one.

The family of segments is the library's own, "Cm.Seg.TS.segM s", whose last segment is the plain
head. The road: the premise gives all 25 segments' conditions at one family of matrices
(Lane5.lean); these give a witness of the model's relaxed relation; at a lawful table every such
witness shows that the request is true.

What this use gives and does not give. It gives the next token (a request with r = 1,023 and
e = 1,024, under every policy) and exact match on every stretch ("Cm.TrueAt"). It has no form for a
request that is judged by a policy on the costs of its tokens: for that see Lane5Ledger.lean.

Main theorems:
* "rno_of_premise": a witness of "Cm.TP.Rno" at the protocol's prime. The library's one equivalence
  "Cm.Seg.TS.model_equiv"; the proof is that of "Cm.Seg.TS.model_force", which uses the bound at the
  places of cells alone, though its statement asks it at all places.
* "true_of_premise": at a lawful table, for every request with r < e ("Cm.TP.forces").
* "reply_first": the reply is the first choice ("Hd.Top.next_token_of_rno").
* "premise_iff": at a lawful table a request with r < e has matrices that meet the premise if and
  only if it is true. So the premise asks neither too much nor too little.
* "premise_met": at every lawful table the premise is met by some index and some request with
  r = 1,023 and e = 1,024 (all weights and tokens 0: the premise is not empty, and no more).
* "no_premise_zero": a guard the other way: at the index with all weights 0, a request that checks a
  token other than 0 has no matrices that meet the premise.

Not claimed: that a table of scales read from a file is lawful; that a stored table of weights is a
well-formed index; and all that Lane5.lean does not claim. Steps 2 and 3 retell the library.
-/
import Cm.TargetSegModelProofs
import Cm.SegLayoutPlainProofs
import Johnson.Road.HeadTop
import Johnson.Road.Lane5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-- The library's own family of segments, with the plain head, is as Lane5.lean asks. -/
theorem laws_plain (s : Cm.Scales) : SegLaws Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) :=
  ⟨Cm.lay_figures.2.2.2.2.2, (Cm.Seg.TS.segs_ok s).wf, (Cm.Seg.TS.segs_ok s).places⟩

section Plain
variable {s : Cm.Scales} {i : Cm.Idx} {x : Instance ppref} {A : ℕ → Mx}

/-- **The premise gives a witness of the model's relaxed relation.** -/
theorem rno_of_premise (hre : x.r < x.e)
    (P : Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) i.mat x A) :
    Cm.TP.Rno Cb.Gl.p s i x (Cm.Seg.ofMat Cm.Seg.Hd.plain (one A)) := by
  refine ⟨hre, (Cm.lay_below_plain (2 ^ 18) _).2 fun n hn => ?_,
    ((Cm.Seg.TS.model_equiv s i.mat x).1 (one A)).2 fun _ hk => holds_one (laws_plain s) P hk⟩
  show |Cm.Seg.get (Cm.Seg.ofMat Cm.Seg.Hd.plain (one A)) n| < 2 ^ 18
  rw [Cm.lay_ofMat_get]
  unfold Cm.Seg.rd
  rw [if_pos hn]
  exact small_one (laws_plain s) P n hn

/-- **At a lawful table the request is true**, for every request with r < e. -/
theorem true_of_premise (hs : s.Lawful) (hre : x.r < x.e)
    (P : Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) i.mat x A) : Cm.TrueAt s.kap s.nf i x :=
  Cm.TP.forces Cb.Gl.p Code.pGold_prime Hd.Down.gl_big s hs i x _ (rno_of_premise hre P)

/-- **The reply is the first choice of the integer model's logits at the last position.** -/
theorem reply_first (hs : s.Lawful) (hr : x.r = 1023) (he : x.e = 1024)
    (P : Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) i.mat x A) (pol : AcceptancePolicy) :
    RinfR ppref s.kap s.nf (fun _ => tbRef) pol i.index x :=
  Hd.Top.next_token_of_rno hs i x _ hr he (rno_of_premise (by omega) P) pol

/-- The matrices of the honest trace, the same for every link, meet the premise of a true
request. -/
theorem premise_of_true (hs : s.Lawful) (ht : Cm.TrueAt s.kap s.nf i x) :
    Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) i.mat x
      fun _ => Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 s i x) :=
  have H := (Cm.Seg.TS.model_true s hs i x).2 ht
  ⟨fun k hk =>
      linkOK_of_holds
        (fun n hn _ =>
          lt_trans (H.1 n.place (Cm.lay_inShape _ (laws_plain s).ok n hn)) (by norm_num))
        (H.2 k hk),
    fun _ _ _ _ => rfl⟩

/-- **At a lawful table a request with r < e has matrices that meet the premise if and only if it is
true.** -/
theorem premise_iff (hs : s.Lawful) (hre : x.r < x.e) :
    (∃ A, Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) i.mat x A) ↔ Cm.TrueAt s.kap s.nf i x :=
  ⟨fun ⟨_, P⟩ => true_of_premise hs hre P, fun ht => ⟨_, premise_of_true hs ht⟩⟩

end Plain

/-- **The premise is not empty**: at every lawful table some index and some request with r = 1,023
and e = 1,024 have matrices that meet it. -/
theorem premise_met {s : Cm.Scales} (hs : s.Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (A : ℕ → Mx),
      x.r = 1023 ∧ x.e = 1024 ∧ Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) i.mat x A := by
  obtain ⟨i, x, hr, he, ht⟩ := Hd.Top.next_true_exists hs
  exact ⟨i, x, _, hr, he, premise_of_true hs ht⟩

/-- **A false request has no matrices that meet the premise**: at the index with all weights 0, if a
checked token is not 0. -/
theorem no_premise_zero {s : Cm.Scales} (hs : s.Lawful) (x : Instance ppref) {t : ℕ}
    (hr : x.r ≤ t) (he : t < x.e) (hw : x.w t ≠ 0) (A : ℕ → Mx) :
    ¬ Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) (Cm.Idx.ofIndex ScalesSanity.iZero).mat x A :=
  fun P => Cm.false_zero s.kap s.nf x hr he hw (true_of_premise hs (by omega) P)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.rno_of_premise
#print axioms OnBytes.Road.L5.true_of_premise
#print axioms OnBytes.Road.L5.reply_first
#print axioms OnBytes.Road.L5.premise_iff
#print axioms OnBytes.Road.L5.premise_met
#print axioms OnBytes.Road.L5.no_premise_zero
