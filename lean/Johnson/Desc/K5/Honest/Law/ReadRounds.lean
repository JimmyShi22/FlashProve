-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadRounds.lean: CONDITIONAL: A TEST WITH CODE ON WHAT SOME OF THE OWN
ROUNDS OF AN ATTENTION SEGMENT (kind K5) DREW, under which the test `heardReads`
(Johnson/Desc/K5/Honest/Law/ReadsLiveAt.lean) on what the verifier's hearing hands on says yes.

Which rounds. `firstOf` x p: the number, among the segment's own rounds from 0, of the first round
of part p; coordinate l of the challenges of the sumcheck that is part p is drawn in round
`firstOf` x p + 1 + l.
  of the division's sumcheck (part `iSE` x): the coordinates [lgk, lgk + lt);
  of the sumcheck "at the index" (part `iSF` x): the coordinates [0, lt), and the last ls.

Main names:
  `readRounds`: the rounds' numbers. `readRounds_length`: they are 2 lt + ls.
  `k5Reads`: **the test**: what each of these rounds drew passes `nz01`
    (Johnson/Desc/K5/Honest/Law/EqTabNz.lean): its words are below the prime, and it is neither the
    word 0 nor the word 1.
  `r_size`, `r_at`: how many coordinates a part's challenges have, and which round drew each.
  `heardReads_of_draws`: **where the hearing returns at rounds that drew these challenges, the test
    on the rounds gives the test on what was heard.**
  `reads_fit`, `heardReads_of_plan`: its two premises on the numbers of variables, paid from two
    structures of facts on public numbers (`Sized`, `Planned`:
    Johnson/Desc/K5/Honest/Law/Cells.lean, Weights.lean).
  `k5Reads_no`: where the test says no, one of the listed rounds drew an element that fails `nz01`.

Limits. A list's length, no probability: nothing says how an element is drawn. The test is
sufficient, not necessary. `nz01` also says no at an element a word of which is not below the prime:
that a drawn element has no such word is not shown here. That the test says yes somewhere is seen by
evaluation alone, at three small places (Johnson/Desc/K5/Honest/Law/ReadRoundsToy.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadsLiveAt
import Johnson.Desc.K5.Honest.Law.HeardIs
import Johnson.Desc.K5.Honest.Law.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First.Att.P (Geo Heard hear chal St lastCoords)

/-- **The numbers of the rounds whose challenges the two tables' weights are made of.** -/
def readRounds (x : OnBytes.Params.AttentionRounds) (g : Geo) : List ℕ :=
  (List.range g.lt).map (fun j => firstOf x (iSE x) + 1 + (g.lgk + j)) ++
    ((List.range g.lt).map (fun j => firstOf x (iSF x) + 1 + j) ++
      (List.range g.ls).map fun j => firstOf x (iSF x) + 1 + (x.attained - g.ls + j))

/-- They are 2 lt + ls. No premise. -/
theorem readRounds_length (x : OnBytes.Params.AttentionRounds) (g : Geo) :
    (readRounds x g).length = 2 * g.lt + g.ls := by
  unfold readRounds
  simp only [List.length_append, List.length_map, List.length_range]
  omega

/-- **The test on what these rounds drew.** -/
def k5Reads (x : OnBytes.Params.AttentionRounds) (g : Geo) (c : Chal) : Bool :=
  (readRounds x g).all fun n => nz01 (c.one n)

/-- How many coordinates a part's challenges have. Conditional: h: the part's number of rounds. -/
theorem r_size (x : OnBytes.Params.AttentionRounds) (c : Chal) {p v : ℕ}
    (h : (cut x)[p]? = some (v + 3)) : (c.r x p).size = v := by
  unfold Chal.r
  rw [Array.size_map, Array.size_range, List.getD_eq_getElem?_getD, h]
  rfl

/-- Which round drew a coordinate. -/
theorem r_at (x : OnBytes.Params.AttentionRounds) (c : Chal) (p : ℕ) {l : ℕ}
    (hl : l < (c.r x p).size) : (c.r x p)[l] = c.one (firstOf x p + 1 + l) := by
  unfold Chal.r
  simp

/-- A cut of a part's challenges passes the test where the rounds that drew it do. -/
theorem cut_all (x : OnBytes.Params.AttentionRounds) (c : Chal) (p a n : ℕ)
    (hs : a + n ≤ (c.r x p).size)
    (h : ∀ j < n, nz01 (c.one (firstOf x p + 1 + (a + j))) = true) :
    ((c.r x p).extract a (a + n)).size = n ∧ ((c.r x p).extract a (a + n)).all nz01 = true := by
  have hz : ((c.r x p).extract a (a + n)).size = n := by
    rw [Array.size_extract]
    omega
  refine ⟨hz, Array.all_eq_true.2 fun i hi => ?_⟩
  rw [Array.getElem_extract, r_at]
  exact h i (by rw [← hz]; exact hi)

/-- **WHERE THE HEARING RETURNS AT ROUNDS THAT DREW c's CHALLENGES, THE TEST ON THE ROUNDS GIVES THE
TEST ON WHAT WAS HEARD.** Conditional: hh: the hearing's return; hc: c holds what the rounds drew;
h1, h2: the two sumchecks have variables enough; hk: the test. -/
theorem heardReads_of_draws (P : Pub5) (c : Chal) {F : Fork} {rs : List Fmt.RoundView} {hd : Heard}
    {s' : St} (hh : hear P.x (F, rs, 0) = some (hd, s')) (hc : Reads c rs)
    (h1 : P.g.lgk + P.g.lt ≤ P.x.e) (h2 : P.g.lt + P.g.lgk + P.g.ls ≤ P.x.attained)
    (hk : k5Reads P.x P.g c = true) : heardReads P.g hd = true := by
  have Sm := heard_is_ours P c hh hc (iHB P.x + 1)
  have eD : chal hd.division = c.r P.x (iSE P.x) :=
    (Sm.division (by unfold iSE iHB; omega)).trans (chal_sumAt _)
  have eF : chal hd.atIndex = c.r P.x (iSF P.x) :=
    (Sm.atIndex (by unfold iSF iHB; omega)).trans (chal_sumAt _)
  have zD : (c.r P.x (iSE P.x)).size = P.x.e := r_size P.x c ((HeardIs.cut_at P.x 0).trans rfl)
  have zF : (c.r P.x (iSF P.x)).size = P.x.attained :=
    r_size P.x c ((HeardIs.cut_at P.x 6).trans rfl)
  unfold k5Reads readRounds at hk
  simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Function.comp] at hk
  obtain ⟨k1, k2, k3⟩ := hk
  obtain ⟨a1, b1⟩ := cut_all P.x c (iSE P.x) P.g.lgk P.g.lt (by rw [zD]; exact h1) k1
  obtain ⟨a2, b2⟩ := cut_all P.x c (iSF P.x) 0 P.g.lt (by rw [zF]; omega)
    (fun j hj => by rw [Nat.zero_add]; exact k2 j hj)
  obtain ⟨a3, b3⟩ := cut_all P.x c (iSF P.x) (P.x.attained - P.g.ls) P.g.ls (by rw [zF]; omega) k3
  have e3 : ptFc P.g hd =
      (c.r P.x (iSF P.x)).extract (P.x.attained - P.g.ls) (P.x.attained - P.g.ls + P.g.ls) := by
    unfold ptFc lastCoords
    rw [eF, zF, Array.extract_extract, Array.size_extract, zF]
    congr 1 <;> omega
  unfold heardReads
  rw [e3]
  unfold ptE ptFi
  rw [eD, eF]
  rw [Nat.zero_add] at a2 b2
  rw [b1, b2, b3]
  simp only [a1, a2, a3, beq_self_eq_true, Bool.and_self]

/-- **The two sumchecks have variables enough**, at a place whose shape has the library's sizes and
whose rounds are the plan's. Conditional: H, Pl: two structures of facts on public numbers. -/
theorem reads_fit {P : Pub5} (H : Sized P) (Pl : Planned P) :
    P.g.lgk + P.g.lt ≤ P.x.e ∧ P.g.lt + P.g.lgk + P.g.ls ≤ P.x.attained := by
  have c1 : (cut P.x).getD (iSE P.x) 3 = P.x.e + 3 := by
    rw [List.getD_eq_getElem?_getD,
      show (cut P.x)[iSE P.x]? = some (P.x.e + 3) from (HeardIs.cut_at P.x 0).trans rfl]
    rfl
  have c2 : (cut P.x).getD (iSF P.x) 3 = P.x.attained + 3 := by
    rw [List.getD_eq_getElem?_getD,
      show (cut P.x)[iSF P.x]? = some (P.x.attained + 3) from (HeardIs.cut_at P.x 6).trans rfl]
    rfl
  have e1 : P.x.e + 3 - 3 = P.D.lg + P.D.lT := c1 ▸ Pl.vSE
  have e2 : P.x.attained + 3 - 3 = P.D.lT + P.D.lg + P.D.ln := c2 ▸ Pl.vSF
  have l1 : P.g.lt = P.D.lT := H.lt
  have l2 : P.g.lgk = P.D.lg := rfl
  have l3 : P.g.ldh = P.D.ln := rfl
  have l4 : P.g.ls ≤ P.g.ldh := H.Z.ls
  omega

/-- **The same with the two premises on variables paid.** Conditional: hh; hc; H, Pl; hk. -/
theorem heardReads_of_plan (P : Pub5) (c : Chal) {F : Fork} {rs : List Fmt.RoundView} {hd : Heard}
    {s' : St} (hh : hear P.x (F, rs, 0) = some (hd, s')) (hc : Reads c rs) (H : Sized P)
    (Pl : Planned P) (hk : k5Reads P.x P.g c = true) : heardReads P.g hd = true :=
  heardReads_of_draws P c hh hc (reads_fit H Pl).1 (reads_fit H Pl).2 hk

/-- **Where the test on the rounds says no, one of the listed rounds drew an element that fails the
test on one element.** No premise beside the no. -/
theorem k5Reads_no {x : OnBytes.Params.AttentionRounds} {g : Geo} {c : Chal}
    (h : k5Reads x g c = false) : ∃ n ∈ readRounds x g, nz01 (c.one n) = false := by
  unfold k5Reads at h
  obtain ⟨n, hn, e⟩ := List.all_eq_false.1 h
  exact ⟨n, hn, by simpa using e⟩

end H2K5.Honest

#print axioms H2K5.Honest.readRounds_length
#print axioms H2K5.Honest.r_size
#print axioms H2K5.Honest.r_at
#print axioms H2K5.Honest.cut_all
#print axioms H2K5.Honest.heardReads_of_draws
#print axioms H2K5.Honest.reads_fit
#print axioms H2K5.Honest.heardReads_of_plan
#print axioms H2K5.Honest.k5Reads_no
