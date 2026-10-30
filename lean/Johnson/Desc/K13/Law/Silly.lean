-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Silly.lean: the form of the batching's law (`SoundAt`,
Johnson/Desc/K13/Law/Law.lean), tried against two silly texts. Statements with their proofs.
Main names:
  `ErrBelow`, `not_doomed`: towards a property that no transcript has, at errors below the numbers
    of challenges, no prover has lost. `below_eps`: the batching's errors are below.
  `rvMk`, `heard_mk`, `backRounds`, `tr_back`: at a reading with a section, every transcript is
    read off some rounds.
  `sillyYes`, `not_sound_yes`: the text that always answers, with a row that is true of everything,
    does not meet `SoundAt`.
  `sillyNo`, `sound_no`: the text that always refuses meets it.
  `AnswersAt`, `batt_answers`, `not_answers_no`: the second half of the law's form: where the tests
    on sizes pass, the text answers; the batching has it; the text that refuses all has not, as soon
    as the tests pass anywhere.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Law.lean names.

What is not claimed. `not_sound_yes` takes a section of the reading and a field of more than 2
elements as premises: neither is shown of the release's reading here. That the tests on sizes pass
somewhere is shown by runs on honest files, not here. The form that is tried is `SoundAt`, which is
idle at a reader that takes all mask entries from one world (Johnson/Desc/K13/Law/Law.lean);
`SoundAt2` (Johnson/Desc/K13/Law/Agree.lean) is not tried here.

-/
import Johnson.Desc.K13.Law.Law
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Prob
open Johnson.L5.Layers (rd sRounds errTo)
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.First.End (sentE)

/-- Each error is below the number of the round's challenges. -/
def ErrBelow : (s : Shape) → Err s → Prop
  | [], _ => True
  | r :: s, (e, ε) => e < Fintype.card r.Chal ∧ ErrBelow s ε

/-- Towards a property that no transcript has, at such errors, no prover has lost. -/
theorem not_doomed : ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop), ErrBelow s ε →
    (∀ τ, ¬ bad τ) → ¬ Doomed s ε bad
  | [], _, _, _, h => fun hd => h () hd
  | r :: s, (e, ε), bad, hb, h => fun hd => by
    have h1 : cnt (fun c : r.Chal => ¬ Doomed s ε (fun τ => bad ((r.dOrc, r.dPlain), c, τ))) ≤ e :=
      hd (r.dOrc, r.dPlain)
    have h2 : cnt (fun c : r.Chal => ¬ Doomed s ε (fun τ => bad ((r.dOrc, r.dPlain), c, τ))) =
        Fintype.card r.Chal := by
      rw [← cnt_true]
      exact cnt_congr fun c => ⟨fun _ => trivial, fun _ => not_doomed s ε _ hb.2 fun τ => h _⟩
    rw [h2] at h1
    exact absurd hb.1 (not_lt.2 h1)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The errors of the variables' rounds are below the number of elements, if that is above 2. -/
theorem below_rounds (h : 2 < Fintype.card K) : ∀ k : ℕ,
    ErrBelow (sRounds (fmtOf K k)) (errTo (sRounds (fmtOf K k)) (pRounds (fmtOf K k))
      (pErr (fmtOf K k)))
  | 0 => trivial
  | k + 1 => ⟨h, below_rounds h k⟩

/-- So are all errors of the batching, if also the pile is not longer than the field is large. -/
theorem below_eps (nR k : ℕ) (pile : List TensorRow) (Ex : ExtSpec) (h : 2 < Fintype.card K)
    (hp : pile.length ≤ Fintype.card K) :
    ErrBelow (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape
      (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex) :=
  ⟨show pile.length - 1 < Fintype.card K by omega, show 1 < Fintype.card K by omega,
    below_rounds h k⟩

/-! ## Every transcript is read off some rounds -/

/-- A round in which the elements s are sent and c is drawn. -/
def rvMk (s : List E) (c : E) : Fmt.RoundView := ⟨s.map fun e => .e e.triple, ⟨[c.triple], [], [], none⟩⟩

/-- What is read as sent of such a round. -/
theorem sentE_mk (s : List E) (c : E) : sentE (rvMk s c) = some s := by
  unfold sentE rvMk
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.map_cons, List.mapM_cons, bind, Option.bind] at ih ⊢
    rw [ih]
    rfl

/-- What is read as drawn of it. -/
theorem oneDrawn_mk (name : String) (s : List E) (c : E) : oneDrawn name (rvMk s c) = .ok c := rfl

/-- Both. -/
theorem oneRound_mk (s : List E) (c : E) : oneRound (rvMk s c) = .ok (s, c) := by
  unfold oneRound
  rw [sentE_mk]
  rfl

/-- The same of a list of such rounds. -/
theorem mapM_mk : ∀ l : List (List E × E),
    (l.map fun p => rvMk p.1 p.2).mapM oneRound = (.ok l : Ans (List (List E × E)))
  | [] => rfl
  | p :: l => by
    rw [List.map_cons, List.mapM_cons, oneRound_mk, mapM_mk l]
    rfl

/-- What is heard in a sumcheck's rounds that are made so. -/
theorem heard_mk (mu eps : E) (l : List (List E × E)) :
    heard (rvMk [mu] eps :: l.map fun p => rvMk p.1 p.2) = .ok ⟨mu, eps, l, []⟩ := by
  simp only [heard, oneRound_mk, mapM_mk]
  rfl

variable (σ : K → E) (hσ : ∀ a, ρ.val (σ a) = a)

/-- Rounds that read as a short transcript. -/
def backRounds : (k : ℕ) → Tr (sRounds (fmtOf K k)) → List (List E × E)
  | 0, _ => []
  | k + 1, (m, c, τ) => ([σ (m.2 0), σ (m.2 1)], σ c) :: backRounds k τ

include hσ in
/-- They read as the transcript. -/
theorem tr_back : ∀ (k : ℕ) (τ : Tr (sRounds (fmtOf K k))), trRounds ρ k (backRounds σ k τ) = τ
  | 0, _ => rfl
  | k + 1, (m, c, τ) => by
    show (((), rd ρ 2 [σ (m.2 0), σ (m.2 1)]), ρ.val (σ c), trRounds ρ k (backRounds σ k τ)) = _
    have e : rd ρ 2 [σ (m.2 0), σ (m.2 1)] = m.2 := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => l.elim0) j) i
      · simp [rd, hσ]
      · simp [rd, hσ]
    rw [e, hσ, tr_back k τ]

/-! ## The text that always answers, with a row that is true of everything -/

/-- It hands on the empty row with the target 0. -/
def sillyYes : RowsOwed → ℕ → ℕ → List TensorRow → ℕ → St → List Fmt.RoundView → Ans (TensorRow × St) :=
  fun _ _ _ _ _ d _ => .ok (⟨[], [], [], zeroE⟩, d)

omit [Fintype K] in
/-- The left side of a row without weights and masks is 0. -/
theorem lhs_nil {nR k : ℕ} (w : Wit K nR k) (t : E) : lhs ρ w ⟨[], [], [], t⟩ = 0 := by
  simp [lhs, weights, formVal, colOf, Alg.mle]

include hσ in
/-- **It does not meet the form of the law**, at a reading onto a field of more than 2 elements. -/
theorem not_sound_yes (nR k : ℕ) (h3 : 2 < Fintype.card K) (d : St) (Ex : ExtSpec) (y : Ex.Str) :
    ¬ SoundAt ρ nR k sillyYes := by
  intro h
  have hD := h Unit (fun _ => (⟨fun _ _ => 0, fun _ => 0⟩ : Wit K nR k)) (fun _ => True)
    (fun _ _ _ _ => rfl) none 1 [⟨[], [], [], oneE⟩] 0 d Ex y
  refine not_doomed _ _ _ (below_eps ρ nR k _ Ex h3 (by simp; omega)) (fun τ hbad => ?_) hD
  obtain ⟨m0, c, m1, e, τ'⟩ := τ
  have hh := hbad (rvMk [] (σ c))
    (rvMk [σ m1.2] (σ e) :: (backRounds σ k τ').map fun p => rvMk p.1 p.2) (σ c)
    ⟨σ m1.2, σ e, backRounds σ k τ', []⟩ (⟨[], [], [], zeroE⟩, d) (oneDrawn_mk _ _ _)
    (heard_mk _ _ _)
    (by
      show (((), ()), ρ.val (σ c), ((), ρ.val (σ m1.2)), ρ.val (σ e),
        trRounds ρ k (backRounds σ k τ')) = _
      rw [hσ, hσ, hσ, tr_back ρ σ hσ]
      rfl)
    rfl () trivial (by show lhs ρ _ _ = ρ.val zeroE; rw [lhs_nil, ρ.zero]) _
    (List.mem_singleton.2 rfl)
  have h1 : lhs ρ _ (⟨[], [], [], oneE⟩ : TensorRow) = ρ.val oneE := hh
  rw [lhs_nil, ρ.one] at h1
  exact zero_ne_one h1

/-! ## The text that always refuses -/

/-- It refuses. -/
def sillyNo : RowsOwed → ℕ → ℕ → List TensorRow → ℕ → St → List Fmt.RoundView → Ans (TensorRow × St) :=
  fun _ _ _ _ _ _ _ => .error "no"

/-- It meets `SoundAt`: a bound on what a cheating prover can reach is met by a text that refuses
all. So the law has a second half. -/
theorem sound_no (nR k : ℕ) : SoundAt ρ nR k sillyNo :=
  fun _ _ _ _ _ _ _ _ _ _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ _ _ _ _ hb => by cases hb

/-- **The second half of the law's form**: where the tests on sizes pass, f answers, with the row
`Batt.rowOf` at what `Psc.run` returns on what `heard` reads. No test is on a value. -/
def AnswersAt (k : ℕ)
    (f : RowsOwed → ℕ → ℕ → List TensorRow → ℕ → St → List Fmt.RoundView → Ans (TensorRow × St)) : Prop :=
  ∀ (owed : RowsOwed) (n : ℕ) (pile : List TensorRow) (ledger : ℕ) (d : St) (r : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (x : E) (t : List ℕ × St) (hd : Psc.Heard) (o : Psc.Out),
    owed.isNone = true → Batt.fits k pile = true → oneDrawn "K13.sigma-one-drawn" r = .ok x →
    pile.length = n → Ground.takeMasksP d ledger (Batt.masksOf k) = some t → heard rs' = .ok hd →
    Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) (t.1.map fun i => ⟨ledger, i⟩) hd =
      some o → o.rowMaps.length = pile.length →
    f owed k n pile ledger d (r :: rs') = .ok (Batt.rowOf pile o, t.2)

/-- The batching's text has it. -/
theorem batt_answers (k : ℕ) : AnswersAt k batt := by
  intro owed n pile ledger d r rs' x t hd o h1 h2 hx h3 ht hh ho h4
  simp only [batt_is, bind_ok, need_ok, there_ok, pure_ok, beq_iff_eq]
  exact ⟨(), h1, (), h2, x, hx, (), h3, t, ht, hd, hh, o, ho, (), h4, rfl⟩

/-- **The text that refuses all does not have it**, as soon as the tests pass anywhere. -/
theorem not_answers_no (k : ℕ) (h : AnswersAt k sillyNo) (owed : RowsOwed) (n : ℕ)
    (pile : List TensorRow) (ledger : ℕ) (d : St) (r : Fmt.RoundView) (rs' : List Fmt.RoundView) (x : E)
    (t : List ℕ × St) (hd : Psc.Heard) (o : Psc.Out) (h1 : owed.isNone = true)
    (h2 : Batt.fits k pile = true) (hx : oneDrawn "K13.sigma-one-drawn" r = .ok x)
    (h3 : pile.length = n) (ht : Ground.takeMasksP d ledger (Batt.masksOf k) = some t)
    (hh : heard rs' = .ok hd)
    (ho : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) (t.1.map fun i => ⟨ledger, i⟩) hd =
      some o) (h4 : o.rowMaps.length = pile.length) : False := by
  have := h owed n pile ledger d r rs' x t hd o h1 h2 hx h3 ht hh ho h4
  cases this

end VerifiableInference.Desc.K13.Law
