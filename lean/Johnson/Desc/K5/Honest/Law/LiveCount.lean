-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveCount.lean: an attention segment's own rounds: the test on the drawn
elements (heardLive, Johnson/Desc/K5/Honest/Law/Live.lean) as a list of events, each of the form
"the one element that a named round draws is 0", and their number. Definitions with code, and
statements with their proofs. No coin and no value that is sent stands in it.

Main names:
  varsAt, sumParts   a sumcheck's number of variables, by the row's numbers of rounds; the row's
                  sumchecks, by part number, each with the mark "the element that scales the claimed
                  sum is asked too"
  partRounds, liveRounds   **the rounds, by number among the place's own from 0, whose one drawn
                  element must not be 0, and can be**: each sumcheck's variables' rounds; the first
                  round of the softmax-table units' sumchecks, of "denominator times output" and of
                  "the key at the index"; the round that draws the batching element of the second
                  end values of the score at the index
  betaRounds      the rounds of the further variable Y: there the format's plan draws an element
                  that is never 0 (Johnson/Desc/Part/MaskedSum4.lean, entries: "PSC Y")
  k5Live          **the test on the place's own challenges**: at none of these rounds the element
                  drawn fails nzE
  varsAt_unit .. varsAt_iHB, liveRounds_length, betaRounds_length   **the count**: the variables of
                  all sumchecks, and the number of softmax-table units + 3 more
  hear_eps, sum_live, units_live, powers_nz   the hearing's verbs
  heardLive_of_draws   **where the verifier's hearing returns at rounds whose challenges c holds, a
                  yes of k5Live is a yes of heardLive**

heardLive_of_draws is CONDITIONAL on: the hearing's return; the challenges c hold what the rounds
drew (Reads, Johnson/Desc/K5/Honest/Law/HeardIs.lean): whoever ties the rounds as played to the
challenges heard shows the second.
Limits. A count of rounds, no probability: nothing says how an element is drawn. nzE also says no
at an element one of whose words is not below the prime; that a drawn element has such words is
not excluded here: whoever holds the rounds against the format's rule on drawn elements does. One
direction: nothing says that a slot is dead where the test says no.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Live
import Johnson.Desc.K5.Honest.Law.HeardIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E mulE zeroE oneE okE isZeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends hear_spec readAll_spec)
open VerifiableInference.Desc.First.Att.P (Heard hear sum St UnitsRan hear_ran sum_spec)
open HeardIs

/-! ## 1 The events -/

/-- A sumcheck's number of variables, by the row's numbers of rounds: three fewer than rounds. -/
def varsAt (x : OnBytes.Params.AttentionRounds) (p : ℕ) : ℕ := (cut x).getD p 3 - 3

/-- The row's sumchecks, by part number; the mark: the element that scales the claimed sum is asked
too. -/
def sumParts (x : OnBytes.Params.AttentionRounds) : List (ℕ × Bool) :=
  (List.range x.score.length).map (·, true) ++
    [(iSE x, true), (iVM x, false), (iVD x, false), (iSF x, false), (iSD x, true), (iHB x, false)]

/-- A sumcheck's rounds that are asked, but for the further variable's. -/
def partRounds (x : OnBytes.Params.AttentionRounds) (s : ℕ × Bool) : List ℕ :=
  (if s.2 then [firstOf x s.1] else []) ++
    (List.range (varsAt x s.1)).map fun t => firstOf x s.1 + 1 + t

/-- **The rounds whose one drawn element must not be 0, and can be.** -/
def liveRounds (x : OnBytes.Params.AttentionRounds) : List ℕ :=
  (sumParts x).flatMap (partRounds x) ++ [firstOf x (iOm4 x)]

/-- The rounds of the further variable. -/
def betaRounds (x : OnBytes.Params.AttentionRounds) : List ℕ :=
  (sumParts x).map fun s => firstOf x s.1 + 1 + varsAt x s.1

/-- **The test on the place's own challenges.** The second list stands here for the implication
(the weights of the further variable's coefficients are powers of its challenge), not for the
count. -/
def k5Live (x : OnBytes.Params.AttentionRounds) (c : Chal) : Bool :=
  (liveRounds x ++ betaRounds x).all fun n => nzE (c.one n)

/-! ## 2 The count -/

section Count
variable (x : OnBytes.Params.AttentionRounds)

theorem varsAt_of {p v : ℕ} (h : (cut x)[p]? = some (v + 3)) : varsAt x p = v := by
  unfold varsAt
  rw [List.getD_eq_getElem?_getD, h, Option.getD_some, Nat.add_sub_cancel]

theorem varsAt_unit {i : ℕ} {u : ℕ × ℕ} (h : x.score[i]? = some u) : varsAt x i = u.1 :=
  varsAt_of x (cut_unit x h)

theorem varsAt_iSE : varsAt x (iSE x) = x.e := varsAt_of x ((cut_at x 0).trans rfl)
theorem varsAt_iVM : varsAt x (iVM x) = x.valueM := varsAt_of x ((cut_at x 2).trans rfl)
theorem varsAt_iVD : varsAt x (iVD x) = x.valueD := varsAt_of x ((cut_at x 3).trans rfl)
theorem varsAt_iSF : varsAt x (iSF x) = x.attained := varsAt_of x ((cut_at x 6).trans rfl)
theorem varsAt_iSD : varsAt x (iSD x) = x.lt + x.lgk + x.lt := varsAt_of x ((cut_at x 8).trans rfl)
theorem varsAt_iHB : varsAt x (iHB x) = x.bits := varsAt_of x ((cut_at x 10).trans rfl)

theorem partRounds_length (s : ℕ × Bool) :
    (partRounds x s).length = (if s.2 then 1 else 0) + varsAt x s.1 := by
  unfold partRounds
  rw [List.length_append, List.length_map, List.length_range]
  cases s.2 <;> rfl

private theorem units_sum : ∀ (n : ℕ), n ≤ x.score.length →
    (((List.range n).map fun i => ((i, true) : ℕ × Bool)).flatMap (partRounds x)).length =
      ((x.score.take n).map (·.1)).sum + n
  | 0, _ => rfl
  | n + 1, h => by
    have hn : n < x.score.length := h
    rw [List.range_succ, List.map_append, List.flatMap_append, List.length_append,
      units_sum n (by omega), List.take_add_one, List.getElem?_eq_getElem hn]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Option.toList_some, List.map_append, List.sum_append, List.sum_cons, List.sum_nil]
    rw [partRounds_length, varsAt_unit x (List.getElem?_eq_getElem hn)]
    simp only [if_true]
    omega

/-- **The count of the events**: the variables of all sumchecks, one for each softmax-table unit,
and 3: the first rounds of "denominator times output" and of "the key at the index", and one
batching element. -/
theorem liveRounds_length : (liveRounds x).length =
    (x.score.map (·.1)).sum + x.e + x.valueM + x.valueD + x.attained + (x.lt + x.lgk + x.lt) +
      x.bits + (x.score.length + 3) := by
  unfold liveRounds sumParts
  rw [List.length_append, List.flatMap_append, List.length_append, units_sum x _ (le_refl _),
    List.take_length]
  simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil,
    List.length_cons, partRounds_length, varsAt_iSE, varsAt_iVM, varsAt_iVD, varsAt_iSF,
    varsAt_iSD, varsAt_iHB]
  simp only [if_true, Bool.false_eq_true, if_false]
  omega

/-- As many rounds of the further variable as sumchecks. -/
theorem betaRounds_length : (betaRounds x).length = x.score.length + 6 := by
  unfold betaRounds sumParts
  simp

end Count

/-! ## 3 What a yes gives, part by part -/

theorem part_nz {x : OnBytes.Params.AttentionRounds} {c : Chal} (hL : k5Live x c = true)
    {s : ℕ × Bool} (hs : s ∈ sumParts x) :
    (s.2 = true → nzE (c.one (firstOf x s.1)) = true) ∧
      ∀ t, t ≤ varsAt x s.1 → nzE (c.one (firstOf x s.1 + 1 + t)) = true := by
  unfold k5Live at hL
  rw [List.all_eq_true] at hL
  refine ⟨fun h2 => hL _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨s, hs, List.mem_append_left _ ?_⟩))), fun t ht => ?_⟩
  · rw [if_pos h2]
    exact List.mem_singleton.2 rfl
  rcases Nat.lt_or_ge t (varsAt x s.1) with h1 | h1
  · exact hL _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨s, hs,
      List.mem_append_right _ (List.mem_map.2 ⟨t, List.mem_range.2 h1, rfl⟩)⟩)))
  · obtain rfl : t = varsAt x s.1 := by omega
    exact hL _ (List.mem_append_right _ (List.mem_map.2 ⟨s, hs, rfl⟩))

theorem om_nz {x : OnBytes.Params.AttentionRounds} {c : Chal} (hL : k5Live x c = true) :
    nzE (c.one (firstOf x (iOm4 x))) = true := by
  unfold k5Live at hL
  rw [List.all_eq_true] at hL
  exact hL _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))

/-! ## 4 The hearing's verbs -/

private theorem okE_mulE (a b : E) : okE (mulE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.mulE
  simp [Fmt.Fld.ok_add]

/-- A product of two elements that pass the test passes it. -/
theorem nzE_mul {a b : E} (ha : nzE a = true) (hb : nzE b = true) : nzE (mulE a b) = true := by
  unfold nzE
  rw [okE_mulE, Bool.true_and]
  cases hz : isZeroE (mulE a b) with
  | false => rfl
  | true =>
    exfalso
    have e : Reading.gl.val (mulE a b) = 0 := by
      rw [(OnBytes.Slice.isZeroE_eq _).1 hz, Reading.gl.zero]
    rw [Reading.gl.mul] at e
    exact mul_ne_zero (nzE_val ha) (nzE_val hb) e

theorem powersFrom_nz {y : E} (hy : nzE y = true) : ∀ (n : ℕ) (a : E), nzE a = true →
    ∀ w ∈ MaskedSum.powersFrom y n a, nzE w = true
  | 0, _, _, w, hw => nomatch hw
  | n + 1, a, ha, w, hw => by
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ha
    · exact powersFrom_nz hy n (mulE a y) (nzE_mul ha hy) w hw

/-- The powers of an element that passes the test pass it. -/
theorem powers_nz {y : E} (hy : nzE y = true) (n : ℕ) : (powers y n).all nzE = true := by
  unfold powers
  rw [List.all_toArray, List.all_eq_true]
  exact powersFrom_nz hy n oneE rfl

/-- Where a masked sumcheck's hearing returns, eps is what its first round drew. -/
theorem hear_eps {C : Aff} {lead : ℕ} {vs : List Var} {e : Ends} {F G : Fork}
    {rs : List Fmt.RoundView} {hh : MaskedSum.Heard}
    (h : MaskedSum.hear C ⟨lead, vs, some e⟩ F rs = some (hh, G)) :
    ∃ r0, rs[0]? = some r0 ∧ r0.drawn.elems.map E.ofTriple = [hh.eps] := by
  obtain ⟨_, T, R, _, hR, hEq, _⟩ := hear_spec h
  obtain ⟨r0, used, rv, front, hrs, hS, _, _, _⟩ := readAll_spec hR
  refine ⟨r0, by rw [hrs]; rfl, ?_⟩
  rw [hEq]
  exact hS.2.2.2.symm

section Verbs
variable (x : OnBytes.Params.AttentionRounds) (c : Chal) {rs : List Fmt.RoundView} (hc : Reads c rs)
include hc

/-- **A masked sumcheck that is part number p.** -/
theorem sum_live {p : ℕ} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {s s' : St}
    (h : sum C (.sum vs e) s = some (hh, s')) (hs : s.2.1 = rs.drop (firstOf x p)) (b : Bool)
    (h1 : b = true → nzE (c.one (firstOf x p)) = true)
    (h2 : ∀ t, t ≤ vs.length → nzE (c.one (firstOf x p + 1 + t)) = true) :
    sumLive b hh = true := by
  obtain ⟨F, rs0, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  have hs' : rs0 = rs.drop (firstOf x p) := hs
  subst hs'
  obtain ⟨_, _, G1, f, g1, _⟩ := sum_spec h
  obtain ⟨hl, hr⟩ := hear_r g1
  obtain ⟨r0, a0, g0⟩ := hear_eps g1
  unfold sumLive
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨r, g', a1, a2, a3⟩ := hr t (by omega)
    rw [List.getElem?_eq_getElem ht] at a2
    rw [Option.some.inj a2]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at a1
    rw [← one_at c hc (n := firstOf x p + 1 + t) (by rw [← a1]; congr 1; omega) a3]
    exact h2 t (by omega)
  · cases b with
    | false => rfl
    | true =>
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at a0
      show nzE hh.eps = true
      rw [← one_at c hc (n := firstOf x p) (by rw [← a0]; rfl) g0]
      exact h1 rfl

/-- The softmax-table units' sumchecks, from unit number i on. -/
theorem units_live : ∀ (us : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (i : ℕ) (s s' : St),
    x.score.drop i = us → s.2.1 = rs.drop (firstOf x i) → UnitsRan us os s s' →
    (∀ n, n < x.score.length → nzE (c.one (firstOf x n)) = true ∧
      ∀ t, t ≤ varsAt x n → nzE (c.one (firstOf x n + 1 + t)) = true) →
    ∀ o ∈ os, sumLive true o.2 = true
  | [], [], _, _, _, _, _, _, _, o, ho => nomatch ho
  | u :: us, o :: os, i, s, s', hu, hs, ⟨s1, ⟨s0, h1, h2⟩, h3⟩, hn, o', ho => by
    obtain ⟨hi, hu'⟩ := drop_cons hu
    have hcut : (cut x)[i]? = some ((List.replicate u.1 (Var.plain 4)).length + 3) := by
      rw [List.length_replicate]
      exact cut_unit x hi
    have hp := (take_pos h1).trans hs
    obtain ⟨p1, _⟩ := sum_part x c hc hcut h2 hp
    have hlt : i < x.score.length := (List.getElem?_eq_some_iff.1 hi).1
    rcases List.mem_cons.1 ho with rfl | ho
    · refine sum_live x c hc h2 hp true (fun _ => (hn i hlt).1) fun t ht => (hn i hlt).2 t ?_
      rw [varsAt_of x hcut]
      exact ht
    · exact units_live us os (i + 1) s1 s' hu'.symm p1 h3 hn o' ho
  | [], _ :: _, _, _, _, _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, h, _, _, _ => h.elim

end Verbs

/-! ## 5 The tie -/

/-- **Where the verifier's hearing returns at rounds whose challenges c holds, a yes of the test on
the challenges is a yes of the test on what was heard.** -/
theorem heardLive_of_draws {x : OnBytes.Params.AttentionRounds} (c : Chal) {F : Fork}
    {rs : List Fmt.RoundView} {hd : Heard} {s' : St} (hh : hear x (F, rs, 0) = some (hd, s'))
    (hc : Reads c rs) (hL : k5Live x c = true) : heardLive hd = true := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ra, rb, t1,
    t2, t3, u4, b5, t6, u7, u8, c9, ept, t10, b11, u12, b13, u14, b15, u16⟩ := (hear_ran hh).ran
  have L : ∀ j v, (tailCut x)[j]? = some v → (cut x)[x.score.length + j]? = some v :=
    fun j v h => (cut_at x j).trans h
  have R4 : ∀ n : ℕ, (List.replicate n (Var.plain 4)).length + 3 = n + 3 := fun n => by
    rw [List.length_replicate]
  have tl : ∀ s ∈ [(iSE x, true), (iVM x, false), (iVD x, false), (iSF x, false), (iSD x, true),
      (iHB x, false)], s ∈ sumParts x := fun s hs => List.mem_append_right _ hs
  obtain ⟨pa, _⟩ := takes_pos 3 _ _ _ _ ra
  have pa' : sa.2.1 = rs.drop (firstOf x 0) := by
    rw [pa]
    rfl
  obtain ⟨pb, _, _⟩ := units_part x c hc x.score hd.scores.toList 0 sa sb rfl pa' rb
  rw [Nat.zero_add] at pb
  have lU := units_live x c hc x.score hd.scores.toList 0 sa sb rfl pa' rb fun n hn => by
    obtain ⟨a, b⟩ := part_nz hL (s := (n, true)) (List.mem_append_left _
      (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))
    exact ⟨a rfl, b⟩
  have q4 := (take_pos t3).trans ((take_pos t2).trans ((take_pos t1).trans pb))
  have k4 : (cut x)[x.score.length]? = some ((List.replicate x.e (Var.plain 4)).length + 3) := by
    rw [R4]
    exact L 0 _ rfl
  obtain ⟨p4, _⟩ := sum_part x c hc (p := x.score.length) k4 u4 q4
  obtain ⟨p5, _⟩ := batch_part x c hc (p := x.score.length + 1) (L 1 _ rfl) b5 p4
  have q7 := (take_pos t6).trans p5
  have k7 : (cut x)[x.score.length + 2]? =
      some ((List.replicate x.valueM (Var.plain 4)).length + 3) := by
    rw [R4]
    exact L 2 _ rfl
  obtain ⟨p7, _⟩ := sum_part x c hc (p := x.score.length + 2) k7 u7 q7
  have k8 : (cut x)[x.score.length + 3]? =
      some ((List.replicate x.valueD (Var.plain 4)).length + 3) := by
    rw [R4]
    exact L 3 _ rfl
  obtain ⟨p8, _⟩ := sum_part x c hc (p := x.score.length + 3) k8 u8 p7
  obtain ⟨p9, _⟩ := close_part x c hc (p := x.score.length + 4) (L 4 _ rfl) c9 p8
  obtain ⟨p11, _⟩ := batch_part x c hc (p := x.score.length + 5) (L 5 _ rfl) b11
    ((take_pos t10).trans p9)
  have k12 : (cut x)[x.score.length + 6]? =
      some ((List.replicate x.attained (Var.plain 4)).length + 3) := by
    rw [R4]
    exact L 6 _ rfl
  obtain ⟨p12, _⟩ := sum_part x c hc (p := x.score.length + 6) k12 u12 p11
  obtain ⟨p13, e13⟩ := batch_part x c hc (p := x.score.length + 7) (L 7 _ rfl) b13 p12
  have k14 : (cut x)[x.score.length + 8]? = some (((List.replicate x.lt 3 ++
      List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)).map Var.plain).length +
        3) := by
    simp only [List.length_map, List.length_append, List.length_replicate]
    exact L 8 _ rfl
  obtain ⟨p14, _⟩ := sum_part x c hc (p := x.score.length + 8) k14 u14 p13
  obtain ⟨p15, _⟩ := batch_part x c hc (p := x.score.length + 9) (L 9 _ rfl) b15 p14
  have k16 : (cut x)[x.score.length + 10]? =
      some ((List.replicate x.bits (Var.plain 4)).length + 3) := by
    rw [R4]
    exact L 10 _ rfl
  have one : ∀ {p : ℕ} {b : Bool} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
      {s s' : St}, (p, b) ∈ sumParts x → (cut x)[p]? = some (vs.length + 3) →
      sum C (.sum vs e) s = some (hh, s') → s.2.1 = rs.drop (firstOf x p) →
      sumLive b hh = true := fun hm hk hs hq => by
    obtain ⟨a, b'⟩ := part_nz hL hm
    exact sum_live x c hc hs hq _ a fun t ht => b' t (by rw [varsAt_of x hk]; exact ht)
  unfold heardLive
  simp only [Bool.and_eq_true]
  have m4 : (x.score.length, true) ∈ sumParts x := tl (iSE x, true) (by simp)
  have m7 : (x.score.length + 2, false) ∈ sumParts x := tl (iVM x, false) (by simp)
  have m8 : (x.score.length + 3, false) ∈ sumParts x := tl (iVD x, false) (by simp)
  have m12 : (x.score.length + 6, false) ∈ sumParts x := tl (iSF x, false) (by simp)
  have m14 : (x.score.length + 8, true) ∈ sumParts x := tl (iSD x, true) (by simp)
  have m16 : (x.score.length + 10, false) ∈ sumParts x := tl (iHB x, false) (by simp)
  refine ⟨⟨⟨⟨⟨⟨⟨?_, one m4 k4 u4 q4⟩, one m7 k7 u7 q7⟩, one m8 k8 u8 p7⟩, one m12 k12 u12 p11⟩,
    one m14 k14 u14 p13⟩, one m16 k16 u16 p15⟩, ?_⟩
  · rw [← Array.all_toList, List.all_eq_true]
    exact fun o ho => lU o ho
  · rw [e13]
    exact powers_nz (om_nz hL) _

end H2K5.Honest

#print axioms H2K5.Honest.varsAt_of
#print axioms H2K5.Honest.varsAt_unit
#print axioms H2K5.Honest.varsAt_iSE
#print axioms H2K5.Honest.varsAt_iVM
#print axioms H2K5.Honest.varsAt_iVD
#print axioms H2K5.Honest.varsAt_iSF
#print axioms H2K5.Honest.varsAt_iSD
#print axioms H2K5.Honest.varsAt_iHB
#print axioms H2K5.Honest.partRounds_length
#print axioms H2K5.Honest.liveRounds_length
#print axioms H2K5.Honest.betaRounds_length
#print axioms H2K5.Honest.part_nz
#print axioms H2K5.Honest.om_nz
#print axioms H2K5.Honest.nzE_mul
#print axioms H2K5.Honest.powersFrom_nz
#print axioms H2K5.Honest.powers_nz
#print axioms H2K5.Honest.hear_eps
#print axioms H2K5.Honest.sum_live
#print axioms H2K5.Honest.units_live
#print axioms H2K5.Honest.heardLive_of_draws
