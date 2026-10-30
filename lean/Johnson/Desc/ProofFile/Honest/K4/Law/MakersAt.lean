-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/MakersAt.lean: CONDITIONAL: on `InSkel`, `LookSkel`, `PtsFull`.

What is here. A CONGRUENCE: THE ANSWER OF THE CLAUSE ON THE MAKERS OF THE PUBLIC TEST ON THE PARTS
OF THE FEED-FORWARD LAYERS' OWN ROUNDS (`k4MakersFit`, Honest/K4/Part.lean), ASKED AT ONE PUBLIC
DATA, AT ANY INPUT AND ANY SAMPLED VALUES, HANGS, OF THESE TWO, ON LENGTHS AND PUBLIC NUMBERS ALONE,
AND, IN THE FIRST GROUP, ON HOW MANY TOKENS THE REQUEST HAS AND WHETHER ONE OF THEM REACHES THE
VOCABULARY's SIZE. Three definitions, statements with their proofs, and three examples.

  `PtsFull`, `InSkel`, `inSkel_of_tokens`   two lists of sampled values of the same lengths; two
      inputs whose tokens, in the first group, are as many and pass the verifier's test together;
      the test's own clause on the tokens gives that against the zero input.
  `k4MakersAt`, `k4MakersFit_at`   the clause on the makers, asked at any input, sampled values and
      shown values; the test's own clause is that at the zero input and zero challenges.
  **`k4MakersAt_skel`**   one answer at two inputs in `InSkel` and at lists of one skeleton.
  **`k4Makers_everywhere`**   a yes of the test's clause is a yes at every such input and list.
  The examples at the end: a member of each of the two relations; two lists that are not in
      `PtsFull`.

Debts and ends. `InSkel` AND `PtsFull` ARE DEBTS, AND SO IS `LookSkel` (Law/LookSkel.lean): THE
THREE ARE ALL THE HYPOTHESES OF `k4MakersAt_skel`. THE TWO INPUTS w AND w₀ ARE FREE LETTERS: NOTHING
IS ASKED OF A CELL OR OF AN ENTRY OF THE COMMITTED MATRIX; the two lists of shown values are any two
arrays. WHAT EACH READS: `InSkel`: in the first group of layers the tokens' number, and whether a
token reaches the vocabulary's size; in a later group nothing; the tokens are the public instance's
(`k4Wit`, `k4Tokens`: Honest/K4/Part.lean) · `LookSkel`: the lookup's public numbers and six lengths
· `PtsFull`: `LookSkel` and fifteen lengths of the sub-protocol's own sampled values. THEIR PAYERS,
ALL THAT ITS WRITERS KNOW OF: `InSkel`: `inSkel_of_tokens`, here, from the test's clause on the
tokens AT THE INPUT's OWN TOKENS · `PtsFull`: `ptsOf_zero` and `ptsOf_full` (Law/PtsFullOf.lean),
from the shapes of the sub-protocol's own challenges (`DrawnSkel`; paid by `drawnSkel_of_ownFits`,
Law/SumAtRun.lean, from `OwnFits` and two counts: how many of the sub-protocol's own challenges have
been heard, and that the table has as many rounds; `OwnFits` by `k4_own_fits`, Law/OwnFits.lean,
where a thread stands) and `LookSkel`; `ptsFull_refl` (Law/SumAtRun.lean) · `LookSkel`: at one and
the same front alone; on which road it stays owed: the head of Law/MakersSkel.lean. The relations in
which the laws beneath end (`JobSkel`, `SidesSkel`, `DataSkel`, `HasSame`, `EnvLook`, `SameW` and
others) ARE NO HYPOTHESES OF THE LAWS HERE.

Not shown here. THE CLAUSE IS SHOWN TRUE NOWHERE IN THIS FILE: each statement compares two calls, or
carries a yes from one to the other. THE THREE DEBTS ARE PAID NOWHERE HERE, but `InSkel` against the
zero input. `k4MakersAt` TYPES THE CLAUSE's FIFTEEN CONJUNCTS A SECOND TIME: what holds the two
together is `k4MakersFit_at`, an equation that Lean checks by unfolding. WHAT THE CLAUSE DOES NOT
ASK: a job's functions at a run's own challenges (`atEnds`, `ends`: the test on a job's shape counts
end values at challenges 0 and never calls `atEnds`); the embedding's value at the round in whose
message it goes: Honest/K4/Part.lean's comments say so; laws on the first stand in
Law/SkelTerms.lean and Law/SkelStack.lean, and in Law/AtEnds.lean; for the second none was sought.
Nothing on what a maker's tables, sums or end values are worth.

Kin. No twin is known to its writers. `k4MakersFit_skel` (Law/MakersSkel.lean) is the narrower law:
the zero input and zero challenges on both sides. `k4Makers_run` (Law/PtsFullOf.lean) carries
`k4Makers_everywhere` to a run's own challenges. The library has another definition of the short
name PtsFull, on another thing (Johnson/LinkSim/AtText/ShortTail.lean: how many distinct points the
opened positions give).
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MakersSkel
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelGen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Forest.Heard ledNS ledNP)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-! ## The clause on the makers, at any input and sampled values -/

/-- Two lists of sampled values of the same lengths, the lookup's in LookSkel. -/
structure PtsFull (p p₀ : Pts) : Prop where
  skel : PtsSkel p p₀
  tkh : p.tkh.size = p₀.tkh.size
  gp : p.gp.size = p₀.gp.size
  rhoI : p.rhoI.size = p₀.rhoI.size
  omV : p.omV.size = p₀.omV.size
  om : p.om.size = p₀.om.size
  rs : p.rs.size = p₀.rs.size
  rhoM : p.rhoM.size = p₀.rhoM.size
  rhoW : p.rhoW.size = p₀.rhoW.size

/-- Two inputs whose tokens are as many, and of which both or neither have a token from the size of
the vocabulary on: IN THE FIRST GROUP OF LAYERS, where alone the tokens are read; in another group
nothing is asked. NOT in it: any cell or weight. -/
structure InSkel (Q : K4Pub) (w w₀ : K4In) : Prop where
  size : (Q.g == 0) = true → w.tokv.size = w₀.tokv.size
  any : (Q.g == 0) = true → w.tokv.any (· ≥ Q.P.V) = w₀.tokv.any (· ≥ Q.P.V)

/-- **The test's own clause on the tokens gives it**, against the zero input. -/
theorem inSkel_of_tokens {Q : K4Pub} {w : K4In} (fo : Forest.Heard)
    (h : k4TokensFit Q w.tokv = true) : InSkel Q w (k4ZeroIn Q fo) := by
  have key : (Q.g == 0) = true →
      w.tokv.size = Q.P.y.T ∧ ∀ t ∈ w.tokv.toList, t < Q.P.V := by
    intro hg
    unfold k4TokensFit at h
    have e : (Q.g != 0) = false := by
      rw [bne, hg]
      rfl
    rw [e, Bool.false_or, Bool.and_eq_true, ← Array.all_toList, List.all_eq_true] at h
    exact ⟨beq_iff_eq.mp h.1, fun t ht => of_decide_eq_true (h.2 t ht)⟩
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · show w.tokv.size = (Array.replicate Q.P.y.T 0).size
    rw [Array.size_replicate]
    exact (key hg).1
  · obtain ⟨h1, h2⟩ := key hg
    have hL : w.tokv.any (· ≥ Q.P.V) = false := by
      rw [← Array.any_toList, List.any_eq_false]
      intro t ht
      have := h2 t ht
      simp only [ge_iff_le, decide_eq_true_eq]
      omega
    have hR : (Array.replicate Q.P.y.T 0).any (· ≥ Q.P.V) = false := by
      rw [← Array.any_toList, Array.toList_replicate, List.any_eq_false]
      intro t ht
      have h0 : t = 0 := List.eq_of_mem_replicate ht
      have hT : 0 < Q.P.y.T := by
        have := List.length_pos_of_mem ht
        rwa [List.length_replicate] at this
      have hpos : 0 < w.tokv.size := h1 ▸ hT
      have := h2 _ (Array.getElem_mem_toList hpos)
      simp only [ge_iff_le, decide_eq_true_eq]
      omega
    exact hL.trans hR.symm

/-- **The clause on the makers, asked at an input w, at sampled values and at shown values sh.**
b k: the sampled values in front of the round number k that batches rows; s k: those in front of
sumcheck number k of the seven. The body is handed the whole input, and the makers that it calls
read cells and weights: that its answer does not hang on them is `k4MakersAt_skel`'s, under its
three hypotheses. b and s are free functions: nothing here ties them to w or to a run. -/
def k4MakersAt (Q : K4Pub) (w : K4In) (b s : Nat → Pts) (sh : Array E) : Bool :=
  (wSums Q w (b 0)).length == ledNS Q.P.y.h.xl * Q.P.y.NI &&
    (rowProducts Q w (b 1)).length == ledNP Q.P.y.h.xl * Q.P.y.NI &&
    (jobSquares Q w (s 0)).any (k4JobFits ((k4Shapes Q).getD 0 ⟨0, [], none⟩)) &&
    (jobRows Q w (s 1)).any (k4JobFits ((k4Shapes Q).getD 1 ⟨0, [], none⟩)) &&
    (jobTerms Q w (s 2)).any (k4JobFits ((k4Shapes Q).getD 2 ⟨0, [], none⟩)) &&
    (jobStack Q w (s 3) sh).any (k4JobFits ((k4Shapes Q).getD 3 ⟨0, [], none⟩)) &&
    (jobGated Q w (s 4)).any (k4JobFits ((k4Shapes Q).getD 4 ⟨0, [], none⟩)) &&
    (jobGated2 Q w (s 5)).any (k4JobFits ((k4Shapes Q).getD 5 ⟨0, [], none⟩)) &&
    (jobMerge Q w (s 6)).any (k4JobFits ((k4Shapes Q).getD 6 ⟨0, [], none⟩)) &&
    ((mergeClaimsAt Q w (s 6)).any fun l => l.length == Q.hp.NCL) &&
    (s 0).gp.size == ledNS Q.P.y.h.xl && (s 1).omV.size == ledNP Q.P.y.h.xl * Q.P.y.NI &&
    (s 3).om.size == 2 && (s 6).rhoW.size == Q.hp.NCL &&
    ((mergeClaimsAt Q w (s 6)).any fun l =>
      l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)

/-- The test's own clause is that at the zero input, the zero challenges in front of each part and
shown values 0. -/
theorem k4MakersFit_at (Q : K4Pub) (fo : Forest.Heard) :
    k4MakersFit Q fo =
      k4MakersAt Q (k4ZeroIn Q fo) (k4AtBat Q fo) (k4AtSum Q fo)
        (Array.replicate (nEndT Q.P.y) zeroE) := rfl

/-- **One answer at two inputs in `InSkel` (of their cells and weights nothing is asked), at sampled
values in `PtsFull` part by part (of b nothing but `LookSkel` at b 1), and at any two lists of shown
values.** -/
theorem k4MakersAt_skel (Q : K4Pub) {w w₀ : K4In} {b b₀ s s₀ : Nat → Pts} (I : InSkel Q w w₀)
    (B : LookSkel (b 1).fo (b₀ 1).fo) (P : ∀ k, PtsFull (s k) (s₀ k)) (sh sh₀ : Array E) :
    k4MakersAt Q w b s sh = k4MakersAt Q w₀ b₀ s₀ sh₀ := by
  have L := fun k => (P k).skel.fo
  have hM := mergeClaimsAt_gen Q w w₀ (L 6) (P 6).rs (P 6).skel.ZE (P 6).tkh I.size I.any
  unfold k4MakersAt
  rw [wSums_len Q w w₀ (p := b 0) (p₀ := b₀ 0), rowProducts_len Q w w₀ B,
    fitsAny_rel (jobSquares_skel Q w w₀ (P 0).rhoI (P 0).skel.PV),
    fitsAny_rel (jobRows_gen Q w w₀ (L 1) (P 1).skel.PV),
    fitsAny_rel (jobTerms_skel Q w w₀ (L 2)),
    fitsAny_rel (jobStack_skel Q w w₀ (P 3).skel (P 3).om sh sh₀),
    fitsAny_rel (jobGated_gen Q w w₀ (L 4) (P 4).rs),
    fitsAny_rel (jobGated2_skel Q w w₀ (P 5).rhoM (P 5).rs (P 5).skel.rt),
    fitsAny_rel (jobMerge_gen Q w w₀ (L 6) (P 6).rs (P 6).skel.ZE (P 6).tkh I.size I.any),
    any_rel hM (f := fun l => l.length == Q.hp.NCL) (f₀ := fun l => l.length == Q.hp.NCL)
      fun a b h => congrArg (· == Q.hp.NCL) h.length,
    (P 0).gp, (P 1).omV, (P 3).om, (P 6).rhoW,
    any_rel hM
      (f := fun l => l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)
      (f₀ := fun l => l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)
      fun a b h => OnBytes.Flat.all_alike
        (fun c c₀ k => congrArg Except.isOk (OnBytes.Flat.shape_alike Q.P.wsLay k)) h]

/-- **A yes of the test's clause on the makers is a yes at every input whose tokens fit as the zero
input's do (I), at sampled values that stand, part by part, in `PtsFull` to those at the zero
challenges in front of that part (P; of b nothing but `LookSkel` at b 1: B), and at every list of
shown values.** -/
theorem k4Makers_everywhere {Q : K4Pub} {fo₀ : Forest.Heard} (h : k4MakersFit Q fo₀ = true)
    {w : K4In} {b s : Nat → Pts} (I : InSkel Q w (k4ZeroIn Q fo₀))
    (B : LookSkel (b 1).fo fo₀) (P : ∀ k, PtsFull (s k) (k4AtSum Q fo₀ k)) (sh : Array E) :
    k4MakersAt Q w b s sh = true :=
  (k4MakersAt_skel Q I (b₀ := k4AtBat Q fo₀) B P sh _).trans ((k4MakersFit_at Q fo₀).symm.trans h)

/-! ## Members of the premises; two lists that are not in the relation -/

/-- Any two inputs with one list of tokens: whatever their cells and weights. -/
example (Q : K4Pub) (w : K4In) (c : Nat → Nat → Nat → OnBytes.F) (a : Nat → Nat → OnBytes.F) :
    InSkel Q { w with cell := c, w := a } w := ⟨fun _ => rfl, fun _ => rfl⟩

/-- The sub-protocol's own sampled values with other elements in every place, lengths kept. -/
example (p : Pts) (f : E → E) :
    PtsFull
      { p with
        PV := p.PV.map f, ZE := p.ZE.map f, tkh := p.tkh.map f, gp := p.gp.map f
        rhoI := p.rhoI.map f, r6 := p.r6.map f, omV := p.omV.map f, rtV := p.rtV.map f
        rt := p.rt.map f, om := p.om.map f, rs := p.rs.map f, r12 := p.r12.map f
        rhoM := p.rhoM.map f, r14 := p.r14.map f, rhoW := p.rhoW.map f } p :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, Array.size_map .., Array.size_map ..,
    Array.size_map .., Array.size_map .., Array.size_map .., Array.size_map ..,
    Array.size_map ..⟩, Array.size_map .., Array.size_map .., Array.size_map ..,
    Array.size_map .., Array.size_map .., Array.size_map .., Array.size_map ..,
    Array.size_map ..⟩

/-- Negative test: the batched sumcheck's challenges with one more are not in the relation. -/
example (p : Pts) : ¬ PtsFull { p with rs := p.rs.push zeroE } p := fun P => by
  have e := P.rs
  rw [Array.size_push] at e
  omega

end ProofFile.Honest.K4




#print axioms ProofFile.Honest.K4.PtsFull
#print axioms ProofFile.Honest.K4.InSkel
#print axioms ProofFile.Honest.K4.inSkel_of_tokens
#print axioms ProofFile.Honest.K4.k4MakersAt
#print axioms ProofFile.Honest.K4.k4MakersFit_at
#print axioms ProofFile.Honest.K4.k4MakersAt_skel
#print axioms ProofFile.Honest.K4.k4Makers_everywhere
