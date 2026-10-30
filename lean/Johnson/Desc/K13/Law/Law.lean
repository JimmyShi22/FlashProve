-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Law.lean: the law of kind K13's batching, of the kind's own text
(Johnson/Desc/K13/Text.lean: `batt`). Statements with their proofs.

The batching tests no value: every hearing of the right form is taken, and a false row on the pile
shows only as a false row handed on. So the law goes from claim to claim.
Main names:
  `bind_ok`, `need_ok`, `there_ok`, `pure_ok`: how a text that answers or refuses is unfolded.
  `batt_ok`: where `batt` answers: its tests have passed, and the row is `Batt.rowOf` at what
    `Psc.run` returns on what `heard` reads.
  `SoundAt ρ nR k f`: the form of the law, of any text f in the batching's place.
  `batt_sound`: the batching's text has it. The errors are the library's (`batt_errs`).
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Fit.lean names. Of the kind: `batt`, `heard`,
`oneDrawn`, `need`, `there`; of the ground: `takeMasksP`.

What is not claimed. The witness stands behind all draws here, as a rule of composition asks; what
makes that true is `Pin`: a premise says that it fixes what the reader takes from a witness. That a
pin of the protocol does so (the committed words decode in one way) is not shown here. At a reader
that takes all mask entries from one world that premise cannot be met by a real run: it fixes a
value at every mask entry of every message, and messages are sent behind these draws. There
`SoundAt` is true and idle; the form to carry on is `SoundAt2` (Johnson/Desc/K13/Law/Agree.lean).
The number nR of the matrix's rows is a free letter: that it is the plan's is said nowhere here.
Nothing on the written rounds of a file. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.TextIs
import Johnson.Desc.K13.Law.FitProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP)

/-- A step of a text that answers or refuses. -/
theorem bind_ok {α β : Type} {x : Ans α} {f : α → Ans β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact ⟨fun h => (by cases h), fun ⟨_, h, _⟩ => (by cases h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, h'⟩ => (by cases h; exact h')⟩

/-- A test passes exactly if it is true. -/
theorem need_ok {name : String} {b : Bool} {u : Unit} : need name b = .ok u ↔ b = true := by
  cases b <;> simp [need]

/-- A value is there exactly if it is. -/
theorem there_ok {α : Type} {name : String} {o : Option α} {a : α} :
    there name o = .ok a ↔ o = some a := by
  cases o <;> simp [there]

/-- What is returned. -/
theorem pure_ok {α : Type} {a b : α} : (pure a : Ans α) = .ok b ↔ a = b :=
  ⟨fun h => Except.ok.inj h, fun h => by rw [h]; rfl⟩

/-- **Where the batching answers**: its tests have passed, and the row is `Batt.rowOf` at what
`Psc.run` returns on what `heard` reads. -/
theorem batt_ok {owed : RowsOwed} {k n : ℕ} {pile : List TensorRow} {ledger : ℕ} {d : St}
    {rs : List Fmt.RoundView} {out : TensorRow × St}
    (h : batt owed k n pile ledger d rs = .ok out) :
    ∃ r rs' x t hd o, rs = r :: rs' ∧ owed.isNone = true ∧ Batt.fits k pile = true ∧
      oneDrawn "K13.sigma-one-drawn" r = .ok x ∧ pile.length = n ∧
      takeMasksP d ledger (Batt.masksOf k) = some t ∧ heard rs' = .ok hd ∧
      Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) (t.1.map fun i => ⟨ledger, i⟩) hd =
        some o ∧ o.rowMaps.length = pile.length ∧ out = (Batt.rowOf pile o, t.2) := by
  cases rs with
  | nil =>
    simp only [batt_is, bind_ok, need_ok] at h
    obtain ⟨_, _, _, _, h⟩ := h
    cases h
  | cons r rs' =>
    simp only [batt_is, bind_ok, need_ok, there_ok, pure_ok, beq_iff_eq] at h
    obtain ⟨_, h1, _, h2, x, hx, _, h3, t, ht, hd, hh, o, ho, _, h4, h5⟩ := h
    exact ⟨r, rs', x, t, hd, o, rfl, h1, h2, hx, h3, ht, hh, ho, h4, h5.symm⟩

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) (nR k : ℕ)

/-- **The form of the law**, of any text f in the batching's place. W: any type of witnesses, with a
reader rw. Pin: what ties a witness to what was committed before the first draw: it fixes what rw
reads. From every record in front the prover has lost, round by round, at the library's errors,
towards: whatever rounds read as the transcript, where f answers, every pinned witness of which the
row handed on is true is one of which all rows of the pile are true. -/
def SoundAt (f : RowsOwed → ℕ → ℕ → List TensorRow → ℕ → St → List Fmt.RoundView → Ans (TensorRow × St)) :
    Prop :=
  ∀ (W : Type) (rw : W → Wit K nR k) (Pin : W → Prop),
    (∀ w w', Pin w → Pin w' → rw w = rw w') →
    ∀ (owed : RowsOwed) (n : ℕ) (pile : List TensorRow) (ledger : ℕ) (d : St) (Ex : ExtSpec)
      (_ : Ex.Str),
    Doomed (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape
      (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex)
      fun τ => ∀ (r : Fmt.RoundView) (rs' : List Fmt.RoundView) (x : E) (hd : Psc.Heard) (out : TensorRow × St),
        oneDrawn "K13.sigma-one-drawn" r = .ok x → heard rs' = .ok hd →
        trOf ρ nR pile Ex x hd = τ → f owed k n pile ledger d (r :: rs') = .ok out →
        ∀ w, Pin w → Holds ρ (rw w) out.1 → ∀ r' ∈ pile, Holds ρ (rw w) r'

/-- **The batching's text has it.** -/
theorem batt_sound : SoundAt ρ nR k batt := by
  intro W rw Pin hdet owed n pile ledger d Ex y
  by_cases hw : ∃ w0, Pin w0
  · obtain ⟨w0, hw0⟩ := hw
    by_cases hf : Batt.fits k pile = true
    · cases ht : takeMasksP d ledger (Batt.masksOf k) with
      | none =>
        refine Doomed.of_forall _ _ fun τ r rs' x hd out _ _ _ hb => ?_
        obtain ⟨_, _, _, t, _, _, _, _, _, _, _, ht', _⟩ := batt_ok hb
        rw [ht] at ht'
        cases ht'
      | some t =>
        refine Doomed.mono _ _ ?_
          (batt_doomed K ρ nR k (rw w0) pile (t.1.map fun i => ⟨ledger, i⟩) Ex y hf)
        intro τ hτ r rs' x hd out hx hh htr hb w hp hrow
        obtain ⟨r1, rs1, x1, t1, hd1, o, e, _, _, hx1, _, ht1, hh1, ho, _, rfl⟩ := batt_ok hb
        obtain ⟨rfl, rfl⟩ := List.cons.inj e
        rw [hx] at hx1
        rw [hh] at hh1
        rw [ht] at ht1
        obtain rfl := Except.ok.inj hx1
        obtain rfl := Except.ok.inj hh1
        obtain rfl := Option.some.inj ht1
        rw [hdet w w0 hp hw0] at hrow ⊢
        exact hτ x hd o htr ho hrow
    · refine Doomed.of_forall _ _ fun τ r rs' x hd out _ _ _ hb => ?_
      obtain ⟨_, _, _, _, _, _, _, _, hf', _⟩ := batt_ok hb
      exact absurd hf' hf
  · exact Doomed.of_forall _ _ fun τ r rs' x hd out _ _ _ _ w hp => absurd ⟨w, hp⟩ hw

end VerifiableInference.Desc.K13.Law
