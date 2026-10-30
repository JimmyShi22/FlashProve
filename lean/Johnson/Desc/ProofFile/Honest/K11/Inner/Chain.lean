-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/Chain.lean: the proofs of three statements of
Honest/K11/Inner/Statement.lean, to the letter: `HeadMergeCall`, `HeadMergeSummand`,
`HeadMergeSumsTo`.

  `headMergeCall`      the shape has no variable that is summed at a point: nothing is laid in
  `headMergeSummand`   `summand_ends` (Johnson/Desc/K11/Honest/Law/Ends.lean)
  `headMergeChain`     round by round: from the product sum of the tables bound at the challenges
                       passed, to the end value plus beta times the coin: by `roundAt_read` and
                       `endAt_read` (Johnson/Desc/K11/Honest/Law/Tables.lean)
  `headMergeSumsTo`    the chain from no challenge on, with its two ends read by `summand_ends`

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Inner.Statement
import Johnson.Desc.K11.Honest.Law.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E addE mulE zeroE oneE)
open OnBytes.Model (Reading WsLay WsClaim)
open VerifiableInference.Desc.Part.MaskedSum (Var Call valueAt total total_read)
open Johnson.Desc.First.ForkMerge.Honest (Term termsOf roundAt endAt claimedSum bindAll termsDot
  roundAt_read endAt_read claimedSum_read bindAll_length onColumns_length rowsSummed_length
  summand_ends)
open ProofFile.Honest.SumLaw (jobPoly SumsTo)

theorem withPoints_plain (d : Nat) (zs : List E) : ∀ n : Nat,
    withPoints (List.replicate n (Var.plain d)) zs = List.replicate n (Var.plain d)
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ]
    show Var.plain d :: withPoints (List.replicate n (Var.plain d)) zs = _
    rw [withPoints_plain d zs n]

theorem headMergeCall : HeadMergeCall := by
  intro lay w fr
  show ({ headMergeShape lay.lk with
    vs := withPoints (List.replicate lay.lk (Var.plain 3)) [] } : Call) = headMergeShape lay.lk
  rw [withPoints_plain]
  rfl

theorem headMergeSummand : HeadMergeSummand :=
  fun _ _ ρ lay entry x cl h => summand_ends ρ lay entry x cl h

section Read
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem sumOf_plain_three (x0 x1 x2 : E) :
    ρ.val (sumOf (.plain 3) (padTo 3 [x0, x1, x2])) = 2 * ρ.val x0 + ρ.val x1 + ρ.val x2 := by
  have e : sumOf (.plain 3) (padTo 3 [x0, x1, x2]) =
      total [mulE x0 (addE oneE oneE), mulE x1 oneE, mulE x2 oneE] := rfl
  rw [e, total_read]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ρ.mul, ρ.add, ρ.one]
  ring

theorem valueAt_three (x0 x1 x2 r : E) :
    ρ.val (valueAt (padTo 3 [x0, x1, x2]) r) =
      ρ.val x0 + ρ.val x1 * ρ.val r + ρ.val x2 * ρ.val r ^ 2 := by
  have e : valueAt (padTo 3 [x0, x1, x2]) r =
      addE (mulE (addE (mulE (addE (mulE zeroE r) x2) r) x1) r) x0 := rfl
  rw [e]
  simp only [ρ.add, ρ.mul, ρ.zero]
  ring

theorem sumOf_atZero_two (g0 g1 : E) :
    ρ.val (sumOf (.point zeroE 2) (padTo 2 [g0, g1])) = ρ.val g0 := by
  have e : sumOf (.point zeroE 2) (padTo 2 [g0, g1]) = total [mulE g0 oneE, mulE g1 zeroE] := rfl
  rw [e, total_read]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ρ.mul, ρ.one, ρ.zero]
  ring

theorem valueAt_two (g0 g1 r : E) :
    ρ.val (valueAt (padTo 2 [g0, g1]) r) = ρ.val g0 + ρ.val r * ρ.val g1 := by
  have e : valueAt (padTo 2 [g0, g1]) r = addE (mulE (addE (mulE zeroE r) g1) r) g0 := rfl
  rw [e]
  simp only [ρ.add, ρ.mul, ρ.zero]
  ring

theorem sumsTo_cons (v : Var) (vs : List Var) (poly : List E → List E) (past : List E) (r : E)
    (rs : List E) (c c' : K) :
    SumsTo ρ (v :: vs) poly past (r :: rs) c c' ↔
      (ρ.val (sumOf v (padTo v.d (poly past))) = c ∧
        SumsTo ρ vs poly (past ++ [r]) rs (ρ.val (valueAt (padTo v.d (poly past)) r)) c') :=
  Iff.rfl

theorem sumsTo_nil (poly : List E → List E) (past : List E) (c c' : K) :
    SumsTo ρ [] poly past [] c c' ↔ c = c' := Iff.rfl

/-- **The chain.** The session's terms' tables have 2 ^ lk entries. n: how many column bits are
still to come. -/
theorem headMergeChain (lay : WsLay) (w : HeadMergeAsk) (fr : Front Unit) (m : List E) (beta : E)
    (hlen : ∀ t ∈ headMergeTerms lay w fr, t.a.length = 2 ^ lay.lk ∧ t.b.length = 2 ^ lay.lk) :
    ∀ (n : Nat) (past rs : List E), past.length + n = lay.lk → rs.length = n →
      SumsTo ρ (List.replicate n (Var.plain 3) ++ [Var.point zeroE 2])
        (jobPoly (headMergeJob lay) w fr m) past (rs ++ [beta])
        (termsDot ρ (headMergeTerms lay w fr) past)
        (ρ.val (endAt (headMergeTerms lay w fr) (past ++ rs)) +
          ρ.val beta * ρ.val (m.headD zeroE))
  | 0, past, [], hp, _ => by
    have hj : jobPoly (headMergeJob lay) w fr m past =
        [endAt (headMergeTerms lay w fr) past, m.headD zeroE] := by
      unfold jobPoly
      rw [if_neg]
      · rfl
      · show ¬ past.length < (List.replicate lay.lk (Var.plain 3)).length
        rw [List.length_replicate]
        omega
    have h1 : ∀ t ∈ headMergeTerms lay w fr,
        (bindAll past t.a).length = 1 ∧ (bindAll past t.b).length = 1 := fun t ht =>
      ⟨by simpa using bindAll_length past t.a 0 (by rw [(hlen t ht).1, hp]),
        by simpa using bindAll_length past t.b 0 (by rw [(hlen t ht).2, hp])⟩
    show SumsTo ρ [Var.point zeroE 2] _ past [beta] _ _
    rw [sumsTo_cons, sumsTo_nil, hj, List.append_nil]
    exact ⟨(sumOf_atZero_two ρ _ _).trans (endAt_read ρ _ past h1), valueAt_two ρ _ _ _⟩
  | n + 1, past, r :: rs, hp, hr => by
    have hj : jobPoly (headMergeJob lay) w fr m past = roundAt (headMergeTerms lay w fr) past := by
      unfold jobPoly
      rw [if_pos]
      · rfl
      · show past.length < (List.replicate lay.lk (Var.plain 3)).length
        rw [List.length_replicate]
        omega
    have h2 : ∀ t ∈ headMergeTerms lay w fr,
        (bindAll past t.a).length = 2 * 2 ^ n ∧ (bindAll past t.b).length = 2 * 2 ^ n :=
      fun t ht =>
        ⟨by rw [bindAll_length past t.a (n + 1) (by rw [(hlen t ht).1, hp]), pow_succ, mul_comm],
          by rw [bindAll_length past t.b (n + 1) (by rw [(hlen t ht).2, hp]), pow_succ, mul_comm]⟩
    obtain ⟨x0, x1, x2, hx, e1, e2⟩ := roundAt_read ρ (headMergeTerms lay w fr) past (2 ^ n) h2
    have ih := headMergeChain lay w fr m beta hlen n (past ++ [r]) rs
      (by rw [List.length_append, List.length_singleton]; omega) (by simpa using hr)
    rw [List.append_assoc, List.singleton_append] at ih
    show SumsTo ρ (Var.plain 3 :: (List.replicate n (Var.plain 3) ++ [Var.point zeroE 2])) _ past
      (r :: (rs ++ [beta])) _ _
    rw [sumsTo_cons, hj, hx]
    refine ⟨(sumOf_plain_three ρ x0 x1 x2).trans e1, ?_⟩
    show SumsTo ρ _ _ _ _ (ρ.val (valueAt (padTo 3 [x0, x1, x2]) r)) _
    rw [valueAt_three, e2 r]
    exact ih
  | 0, _, _ :: _, _, hr => by simp at hr
  | _ + 1, _, [], _, hr => by simp at hr

end Read

theorem headMergeSumsTo : HeadMergeSumsTo := by
  intro K _ ρ lay w fr cl x beta m rs hcl hx hq hr
  have ht : headMergeTerms lay w fr = termsOf lay w.entry x cl.toList := by
    unfold headMergeTerms
    rw [hcl, hx]
  have hlen : ∀ t ∈ headMergeTerms lay w fr,
      t.a.length = 2 ^ lay.lk ∧ t.b.length = 2 ^ lay.lk := by
    intro t h
    unfold headMergeTerms termsOf at h
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 h
    exact ⟨onColumns_length lay y.1, rowsSummed_length lay w.entry y.1⟩
  obtain ⟨s1, s2⟩ := summand_ends ρ lay w.entry x cl hq
  have c := headMergeChain ρ lay w fr m beta hlen lay.lk [] rs (by simp) hr
  rw [List.nil_append, ← claimedSum_read, ht, s1, s2 rs hr] at c
  exact c

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headMergeCall
#print axioms ProofFile.Honest.K11.headMergeSummand
#print axioms ProofFile.Honest.K11.headMergeSumsTo
