-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SampleLaw.lean: what the yes of the test `sampleOk` gives, as a theorem.
Statements and proofs.

The test is in Johnson/Desc/K12/Law/SampleOk.lean.
Main names:
  `zip_all_eq`, `tensorSame_eq`: from the tests on fields to equations.
  `rowSame_eq`: rowSame a b = true gives b = { a with target := b.target }: a Row has six fields
    (kind, terms, units, runs, forms, target); the test holds the first five; Lean's `cases` shows
    that there is no seventh.
  `sample_of_L`: ok (sampleL K m x) = true gives ∃ seed row0 tt (β : a unit of the field): Send.form
    K m.sh m.id seed 0 = some row0 ∧ x.sampleRows.toList = [{ row0 with target := tt }] ∧ bitsZ K
    m.sh ≤ seed.z.length ∧ β = readE seed.beta ∧ one answer ∧ (CaseE ∨ CaseF) ∧ the two powers of
    two: every premise on the sample row that `few_draws_made` (Johnson/Desc/K12/Law/TieMade.lean)
    takes, but "it stands among the rows".
  `sampleL_of_ok`: the test's yes reaches each member.
The seed here is the one read back off the row: that the verifier drew it, and when, is not said.
For a count of the drawn element of the batching nothing of that is needed; for the collisions at
the seed (the sending's price) it is.
Limits: the yes of `sampleOk` is held by runs alone. x is the message in the plain data's statement
D.st; `few_draws_made` reads the rows at t.st and the batching takes `runRows` at the statement in
front: that the three hold one sampleRows for a member is not typed here (see
Johnson/Desc/K12/Law/TieFront.lean). No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `isZeroE_iff`
(OnBytes/Slice/ProgField.lean), `cube_bits` (Johnson/Pack/PortTie.lean); `ok_tagM`
(Johnson/Desc/K12/Law/TieRoad.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.SampleOk
import Johnson.Desc.K12.Law.FormTake
import Johnson.Desc.K12.Law.TieRoad

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack
open H2K.First (Seat1)

theorem zip_all_eq {α : Type} (q : α × α → Bool) (hq : ∀ x y, q (x, y) = true → x = y) :
    ∀ l l' : List α, l.length = l'.length → (l.zip l').all q = true → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | x :: l, y :: l', h, h2 => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h2
    rw [hq x y h2.1, zip_all_eq q hq l l' (by simpa using h) h2.2]

theorem tensorSame_eq {a b : Tensor} (h : tensorSame a b = true) : a = b := by
  simp only [tensorSame, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases a
  cases b
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h5
  rw [Array.toList_inj.1 h4]

/-- rowSame's yes is equality of rows up to the target: a Row has six fields: kind · terms · units
· runs · forms · target: the test holds the first five. -/
theorem rowSame_eq {a b : Row} (h : rowSame a b = true) : b = { a with target := b.target } := by
  simp only [rowSame, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have e3 : a.terms.toList = b.terms.toList := zip_all_eq _ (fun x y hxy => by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxy
    obtain ⟨⟨q1, q2⟩, q3⟩ := hxy
    cases x
    cases y
    simp only at q1 q2 q3
    subst q1 q2
    rw [tensorSame_eq q3]) _ _ (by simpa using h2) h3
  have e5 : a.units.toList = b.units.toList := zip_all_eq _ (fun x y hxy => by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxy
    obtain ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩ := hxy
    cases x
    cases y
    simp only at q1 q2 q3 q4
    subst q1 q2 q3 q4
    rfl) _ _ (by simpa using h4) h5
  cases a
  cases b
  simp only at h1 e3 e5 h6 h7 h8 h9
  subst h1
  rw [Array.toList_inj.1 e3, Array.toList_inj.1 e5, Array.size_eq_zero_iff.1 h6,
    Array.size_eq_zero_iff.1 h7, Array.size_eq_zero_iff.1 h8, Array.size_eq_zero_iff.1 h9]

/-- What sampleL's yes gives: the record's one sample row is { row0 with target := tt } for row0
:= Send.form at a seed whose point has the cube's coordinates and whose factor is a unit of the
field; with the other premises of says_sample_ge. -/
theorem sample_of_L {K : Codes} {m : Seat1} {x : OnBytes.Oracle} (h : ok (sampleL K m x) = true) :
    ∃ (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
      Send.form K m.sh m.id seed 0 = some row0 ∧ x.sampleRows.toList = [{ row0 with target := tt }]
          ∧
      bitsZ K m.sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧ m.sh.answers = 1 ∧
      (CaseE m.sh ∨ CaseF m.sh) ∧
      (0 < m.sh.mainRows → 2 ^ ceilLog2 (pMain K m.sh).ell = (pMain K m.sh).ell) ∧
      (0 < m.sh.maskRows → 2 ^ ceilLog2 (pMask K m.sh).ell = (pMask K m.sh).ell) := by
  simp only [sampleL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨_, h2, h3, _, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  cases hsd : seedOfRow K m.sh (x.sampleRows.getD 0 default) with
  | none => rw [hsd] at h5; cases h5
  | some s =>
    rw [hsd] at h6 h7 h8 h9
    simp only [beq_iff_eq, Bool.not_eq_true'] at h6 h7 h8 h9
    unfold formIs at h6
    cases hf : Send.form K m.sh m.id s 0 with
    | none => rw [hf] at h6; cases h6
    | some row0 =>
      rw [hf] at h6
      have hne : readE s.beta ≠ 0 := fun q => by
        have := (isZeroE_iff s.beta h9).2 q
        rw [h8] at this
        cases this
      refine ⟨s, row0, (x.sampleRows.getD 0 default).target, Units.mk0 _ hne, hf, ?_, ?_, rfl, h3,
          h10,
        fun h0 => ?_, fun h0 => ?_⟩
      · rw [← rowSame_eq h6]
        rcases hx : x.sampleRows with ⟨l⟩
        rw [hx] at h2
        rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
        · cases h2
        · rfl
        · simp at h2
      · rw [← cube_bits, h7]
      · exact h11.resolve_left (by omega)
      · exact h12.resolve_left (by omega)

/-- The test's yes reaches each member: sampleOk p t = true, at the plain data that the place
and the record behind the batching make, gives at every member the message in the plain data's
statement and the twelve clauses' yes. -/
theorem sampleL_of_ok (p : VerifiableInference.Desc.K12.P12) (t : VerifiableInference.Desc.K12.T12)
    (a : Fmt.M1.Stage) (D : H2K.First.Plain) (hp : plainAt p t = some (a, D))
    (h : sampleOk p t = true) (m : Seat1) (hm : m ∈ D.mems) :
    ∃ x, D.st.oracles[m.id]? = some x ∧ ok (sampleL D.st.codes m x) = true := by
  unfold sampleOk sampleAll at h
  rw [hp] at h
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
  have hz : (m, i) ∈ D.mems.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    rw [List.getElem?_eq_getElem hi, e]
  have h2 := fun c hc => (List.all_eq_true.1 h) c (List.mem_flatMap.2 ⟨(m, i), hz, hc⟩)
  cases hx : D.st.oracles[m.id]? with
  | none =>
    have := h2 (toString i ++ ":the statement has not the message", false) (by
      show _ ∈ (match D.st.oracles[m.id]? with
        | some x => tagM i (sampleL D.st.codes m x)
        | none => [(toString i ++ ":the statement has not the message", false)])
      rw [hx]
      exact List.mem_singleton.2 rfl)
    cases this
  | some x =>
    refine ⟨x, rfl, ?_⟩
    rw [← ok_tagM i]
    refine List.all_eq_true.2 fun c hc => h2 c ?_
    show _ ∈ (match D.st.oracles[m.id]? with
      | some x => tagM i (sampleL D.st.codes m x)
      | none => [(toString i ++ ":the statement has not the message", false)])
    rw [hx]
    exact hc

end H2K.Pin

#print axioms H2K.Pin.rowSame_eq
#print axioms H2K.Pin.sample_of_L
#print axioms H2K.Pin.sampleL_of_ok
