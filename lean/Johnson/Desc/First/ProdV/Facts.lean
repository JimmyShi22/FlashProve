--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ProdV/Facts.lean: the grand product: the part's text on a view's rounds laid
into the chain for any text (Johnson/Desc/First/ProdV/Chain.lean). Definitions, statements and
proofs.

`LevF`: "the level returns", said by LevelFacts (on the outputs of the masked sumcheck's texts and
on LINE), not by a text's name: the level's return gives it (level_facts). `Ok5`: every word of the
rounds left is below the prime. `P1Clean5`: no bad eps, challenge or beta in the level's masked
sumcheck: a sentence on what the function readAll reads off the level's first m + 3 rounds: no
"there are". `law5`, `facts5`: LevF pays the chain's two premises (from sound_of_facts and
facts_ledger, Johnson/Desc/First/ProdV/LevelSound.lean). `ran_of_run`: where run returns, the
relation Ran holds. `run_sound5`: the chain's law as an instance of ran_sound; `run_sound5'`:
worded on run's return. The error: Johnson/Desc/First/ProdV/RunCount.lean.

Limits. Those of Johnson/Desc/First/ProdV/LevelSound.lean and Johnson/Desc/First/ProdV/Chain.lean.
Not claimed: anything on an honest prover or on hiding; the soundness of a kind or of the protocol.

-/
import Johnson.Desc.First.ProdV.Chain
import Johnson.Desc.First.ProdV.LevelSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.ProdV
open OnBytes OnBytes.Model OnBytes.PscRun Polynomial
open VerifiableInference.Desc.Part
open OnBytes.Desc.First.P1 OnBytes.Desc.First.P2

/-! ### The run, level by level -/

theorem turn_spec {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) :
    ∃ o, level m s.point order s.form F rs = some (o, G, rest) ∧
      s' = { rows := s.rows.push o.row, point := (stepDown o).1, form := (stepDown o).2 } := by
  unfold turn at h
  cases hl : level m s.point order s.form F rs with
  | none => simp [hl] at h
  | some x =>
    obtain ⟨o, G1, r1⟩ := x
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨a1, a2, a3⟩ := h
    subst a2 a3
    exact ⟨o, rfl, a1.symm⟩

theorem run_zero (m0 : Nat) (orders : Nat → List Nat) (s : Carried) (F : Fork)
    (rs : List Fmt.RoundView) : run m0 0 orders s F rs = some (s, F, rs) := rfl

theorem run_succ (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) (F : Fork)
    (rs : List Fmt.RoundView) : run m0 (n + 1) orders s F rs =
      (run m0 n orders s F rs).bind fun x => turn (orders (m0 + n)) x.1 (m0 + n) x.2.1 x.2.2 := by
  unfold run
  rw [List.range_succ, List.foldlM_append]
  simp [List.foldlM_cons, List.foldlM_nil]

theorem run_succ_spec {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F F' : Fork}
    {rs rest : List Fmt.RoundView} (h : run m0 (n + 1) orders s F rs = some (s', F', rest)) :
    ∃ s1 F1 r1, run m0 n orders s F rs = some (s1, F1, r1) ∧
      turn (orders (m0 + n)) s1 (m0 + n) F1 r1 = some (s', F', rest) := by
  rw [run_succ] at h
  cases hq : run m0 n orders s F rs with
  | none => simp [hq] at h
  | some x =>
    obtain ⟨s1, F1, r1⟩ := x
    rw [hq] at h
    exact ⟨s1, F1, r1, rfl, h⟩

theorem okRounds_drop {rs : List Fmt.RoundView} (h : okRounds rs = true) (k : ℕ) :
    okRounds (rs.drop k) = true := by
  unfold okRounds at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => h r (List.mem_of_mem_drop hr)


/-! ### Form 5 in the chain's letters -/

/-- "The level returns", said on the OUTPUTS of the masked sumcheck's two texts and on LINE
(LevelFacts): so that any text of
a level whose return gives LevelFacts on a view's rounds can be laid in: form 5 by level_facts;
form 1 by the tie of texts. -/
def LevF : LevRel (List Fmt.RoundView) := fun m z order C F rs o G rest =>
  LevelFacts m z order C F rs o G rest

/-- Every word of the rounds left is below the prime. -/
def Ok5 (rs : List Fmt.RoundView) : Prop := okRounds rs = true

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- No bad eps, challenge or beta: on what readAll reads off the level's first m + 3 rounds. -/
def P1Clean5 : P1CleanRel K (List Fmt.RoundView) := fun badE bad m z order _ _ rs T' =>
  ∀ R : MaskedSum.Read, MaskedSum.readAll (levelCall m z order) (rs.take (m + 3)) = some R →
    ρ.val R.eps ∉ badE (ρ.val R.mu) ∧
    (haveI := Classical.decEq K
     NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
      (MaskedSum.movesOf ρ (levelCall m z order).all R.rounds (addE R.mu (mulE R.eps T'))))

/-- The level's law, from LevelFacts, with its public premises behind the sets, so that the sets
are there at all
letters. -/
theorem sound_of_facts' (m : ℕ) (z : Array E) (order : List ℕ) (A B : (ℕ → K) → K) (mask : ℕ → K)
    (nx : ℕ) (Cv T : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧ (∀ mu eps pre g, (bad mu eps pre g).card ≤ 2) ∧
      (orderOk m order = true → z.size = m → Step m A B →
      ∀ (entry : ℕ → ℕ → ℕ → K) (C : Aff) (F G H : Fork) (rs rest : List Fmt.RoundView) (o : LevelOut)
        (R : MaskedSum.Read) (T' : E),
        okRounds rs = true → LevelFacts m z order C F rs o G rest →
        F.next = nx → Sized F → OnFilled F C →
        F.publicPart C = some T' → ρ.val T' = T → C.value ρ (F.worldOf ρ mask entry) = Cv →
        MaskedSum.readAll (levelCall m z order) (rs.take (m + 3)) = some R →
        Later G H →
        o.row.value ρ (H.worldOf ρ mask entry) = 0 →
        (stepDown o).2.value ρ (H.worldOf ρ mask entry) = B (pt ρ (stepDown o).1) →
        ρ.val R.eps ∉ badE (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
          (MaskedSum.movesOf ρ (levelCall m z order).all R.rounds
            (addE R.mu (mulE R.eps T')))) →
        ρ.val o.xi ∉ badLine (B (pcons 0 (pt ρ o.r))) (B (pcons 1 (pt ρ o.r)))
          ((G.worldOf ρ mask entry).slot o.sL) ((G.worldOf ρ mask entry).slot o.sR) →
        Cv = A (pt ρ z)) := by
  by_cases hc : orderOk m order = true ∧ z.size = m ∧ Step m A B
  · obtain ⟨badE, bad, h1, h2, h3⟩ :=
      sound_of_facts ρ m z order hc.1 hc.2.1 A B hc.2.2 mask nx T Cv
    exact ⟨badE, bad, h1, h2, fun _ _ _ => h3⟩
  · exact ⟨fun _ => ∅, fun _ _ _ _ => ∅, fun _ => by simp, fun _ _ _ _ => by simp,
      fun a b c => absurd ⟨a, b, c⟩ hc⟩

theorem law5 : LawOf ρ LevF Ok5 (P1Clean5 ρ) := by
  intro m z order A B mask nx Cv T
  obtain ⟨badE, bad, h1, h2, h3⟩ := sound_of_facts' ρ m z order A B mask nx Cv T
  refine ⟨badE, bad, h1, h2, fun ho hz hs entry C F G H x y o T' hx hl hnx hF hC hp hT hCv hGH hrow
    hnext hclean hxi => ?_⟩
  obtain ⟨R, hR⟩ := facts_read hl
  obtain ⟨c1, c2⟩ := hclean R hR
  exact h3 ho hz hs entry C F G H x y o R T' hx hl hnx hF hC hp hT hCv hR hGH hrow hnext c1 c2 hxi

end

theorem facts5 : FactsOf LevF Ok5 := by
  intro m z order C F G x y o hF hx hl
  obtain ⟨l, s, _, d, p, c⟩ := facts_ledger hF hl
  refine ⟨l, s, p, c, by rw [d]; exact okRounds_drop hx _, ?_⟩
  obtain ⟨hd, G1, _, _, _, _, hh, _⟩ := hl
  obtain ⟨_, T, _, hT, _⟩ := MaskedSum.hear_spec hh
  exact ⟨T, hT⟩

/-- Where run returns, the relation holds. -/
theorem ran_of_run (m0 : Nat) (orders : Nat → List Nat) (s : Carried) (F : Fork)
    (rs : List Fmt.RoundView) :
    ∀ (n : Nat) (s' : Carried) (F' : Fork) (rest : List Fmt.RoundView),
      run m0 n orders s F rs = some (s', F', rest) → Ran LevF m0 orders s F rs n s' F' rest
  | 0, s', F', rest, h => by
    rw [run_zero] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨a1, a2, a3⟩ := h
    subst a1 a2 a3
    exact Ran.zero
  | n + 1, s', F', rest, h => by
    obtain ⟨s1, F1, r1, h1, h2⟩ := run_succ_spec h
    obtain ⟨o, hl, rfl⟩ := turn_spec h2
    exact Ran.succ (ran_of_run m0 orders s F rs n s1 F1 r1 h1) (level_facts hl)

/-- **THE CHAIN's LAW OF FORM 5's run.** CleanRan holds the run itself, level by level, and that no
bad element was drawn;
"CleanRan.ran" and "ran_of_run" say that it is run's own course. -/
theorem run_sound5 {K : Type} [Field K] (ρ : Reading K) (m0 : ℕ) (orders : ℕ → List ℕ)
    (P : ℕ → (ℕ → K) → K) (mask : ℕ → K) :
    ∃ (badE : ℕ → Array E → ℕ → K → K → K → Finset K)
      (bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ m z nx Cv T mu, (badE m z nx Cv T mu).card ≤ 1) ∧
      (∀ m z nx Cv T mu eps pre g, (bad m z nx Cv T mu eps pre g).card ≤ 2) ∧
      ∀ (entry : ℕ → ℕ → ℕ → K) (n : ℕ) (s s' : Carried) (F F' H : Fork) (rs rest : List Fmt.RoundView),
        (∀ i, i < n → orderOk (m0 + i) (orders (m0 + i)) = true) →
        (∀ i, i < n → Step (m0 + i) (P (m0 + i)) (P (m0 + i + 1))) →
        okRounds rs = true → Sized F → s.point.size = m0 → OnFilled F s.form →
        CleanRan ρ LevF (P1Clean5 ρ) mask entry P badE bad m0 orders s F rs n s' F' rest →
        Later F' H →
        (∀ j, s.rows.size ≤ j → j < s'.rows.size →
          (s'.rows.getD j {}).value ρ (H.worldOf ρ mask entry) = 0) →
        s'.form.value ρ (H.worldOf ρ mask entry) = P (m0 + n) (pt ρ s'.point) →
        s.form.value ρ (F.worldOf ρ mask entry) = P m0 (pt ρ s.point) :=
  ran_sound ρ (law5 ρ) facts5 m0 orders P mask

/-- **THE CHAIN's LAW OF FORM 5's run, WORDED ON run's RETURN.** -/
theorem run_sound5' {K : Type} [Field K] (ρ : Reading K) (m0 : ℕ) (orders : ℕ → List ℕ)
    (P : ℕ → (ℕ → K) → K) (mask : ℕ → K) :
    ∃ (badE : ℕ → Array E → ℕ → K → K → K → Finset K)
      (bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ m z nx Cv T mu, (badE m z nx Cv T mu).card ≤ 1) ∧
      (∀ m z nx Cv T mu eps pre g, (bad m z nx Cv T mu eps pre g).card ≤ 2) ∧
      ∀ (entry : ℕ → ℕ → ℕ → K) (n : ℕ) (s s' : Carried) (F F' H : Fork) (rs rest : List Fmt.RoundView),
        (∀ i, i < n → orderOk (m0 + i) (orders (m0 + i)) = true) →
        (∀ i, i < n → Step (m0 + i) (P (m0 + i)) (P (m0 + i + 1))) →
        okRounds rs = true → Sized F → s.point.size = m0 → OnFilled F s.form →
        run m0 n orders s F rs = some (s', F', rest) →
        AllClean ρ LevF (P1Clean5 ρ) mask entry P badE bad m0 orders s F rs n →
        Later F' H →
        (∀ j, s.rows.size ≤ j → j < s'.rows.size →
          (s'.rows.getD j {}).value ρ (H.worldOf ρ mask entry) = 0) →
        s'.form.value ρ (H.worldOf ρ mask entry) = P (m0 + n) (pt ρ s'.point) →
        s.form.value ρ (F.worldOf ρ mask entry) = P m0 (pt ρ s.point) := by
  obtain ⟨badE, bad, h1, h2, h3⟩ := run_sound5 ρ m0 orders P mask
  refine ⟨badE, bad, h1, h2, fun entry n s s' F F' H rs rest hok hP hw hF hp hC hr hall => ?_⟩
  exact h3 entry n s s' F F' H rs rest hok hP hw hF hp hC
    (cleanRan_of_all ρ facts5 hF hw hp hC (ran_of_run m0 orders s F rs n s' F' rest hr) hall)

end VerifiableInference.Desc.First.ProdV

#print axioms VerifiableInference.Desc.First.ProdV.run_sound5'
#print axioms VerifiableInference.Desc.First.ProdV.run_sound5
#print axioms VerifiableInference.Desc.First.ProdV.ran_of_run
