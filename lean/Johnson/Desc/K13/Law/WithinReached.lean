-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/WithinReached.lean: TWO OF THE THREE TESTS ON THE ROWS ON THE TABLE, APART FROM
THE FIRST: "K13.pileWithin" and "K13.oneRow" as one fact on the chain's state, which every step
keeps at ARBITRARY states.

WHY APART. The first test, "K13.pileMasks", reads the index masks' number, which link 0's "opened"
writes while the rows stay: it is kept there only where no row lies on the table: a fact of position
in the chain, not of the step. These two read no such number.

  WithinFact s     pileWithinC s = true ∧ oneRowC s = true (Johnson/Desc/K13/PubK13.lean).
  pileWithinC_quiet  the second test alone, under the first three of these conditions.
  withinFact_quiet   A SUFFICIENT CONDITION: the rows stay, the statement grows, the ledgers stay in
                   order, the chain does not come to stand at its end.
  withinFact_push  where one pending row is laid behind the others (pendingRowO).
  withinFact_start, withinFact_of_rows   at the start; out of RowsFact.
  atM3_withinFact  kind K13's batching.
  reach_inv        THE RULE, general in a fact Inv on the state: an induction on "reached"
                   (Johnson/Top/H0/Walk/Reach.lean).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.OwedFoldFacts
import Johnson.Desc.K13.Law.LedgersB
import Johnson.Desc.K13.Law.LedgersC
import Johnson.Desc.K13.Law.LedgersAtRow
import Johnson.Desc.K13.Law.WithinM3
import Johnson.Desc.K13.Law.WithinM4
import Johnson.Desc.K13.Law.RowMasks
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.Keeps (Decides ofInv)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-- The second and the third test on the rows on the table, as one fact. -/
def WithinFact (s : S) : Prop := pileWithinC s = true ∧ oneRowC s = true

theorem withinFact_of_rows {s : S} (h : RowsFact s) : WithinFact s := h.2

/-- The test on the rows' mask entries, in the laws' word. (The two words for a table's size are one
by unfolding.) -/
theorem rowsWithin_iff (s : S) : rowsWithinC s = true ↔
    ∀ r ∈ s.rows, ∀ t ∈ r.masks, t.1.index < tableSizeC s.st t.1.oracle .mask := by
  unfold rowsWithinC
  simp only [List.all_eq_true, decide_eq_true_eq]

/-- Where the chain does not stand at its end the third test accepts. -/
theorem oneRowC_not_mem {s : S} (h : ∀ a, s.here ≠ .mem a) : oneRowC s = true := by
  cases hq : s.here
  case mem a => exact absurd hq (h a)
  all_goals (unfold oneRowC; rw [hq])

/-- **"K13.pileWithin" alone**: the rows stay, the statement grows, the ledgers stay in order. -/
theorem pileWithinC_quiet {s s' : S} (hr : s'.rows = s.rows) (hg : Grows s.st s'.st)
    (hF : FitStays s.st s'.st) (h2 : pileWithinC s = true) : pileWithinC s' = true := by
  unfold pileWithinC at h2 ⊢
  rw [Bool.and_eq_true] at h2 ⊢
  refine ⟨(ledgersC s').2 (hF ((ledgersC s).1 h2.1)), (rowsWithin_iff s').2 fun r hr' t ht => ?_⟩
  rw [hr] at hr'
  exact tableSizeC_grows hg _ _ _ ((rowsWithin_iff s).1 h2.2 r hr' t ht)

/-- **A sufficient condition.** -/
theorem withinFact_quiet {s s' : S} (hr : s'.rows = s.rows) (hg : Grows s.st s'.st)
    (hF : FitStays s.st s'.st) (hm : ∀ a', s'.here = .mem a' → ∃ a, s.here = .mem a)
    (h : WithinFact s) : WithinFact s' := by
  obtain ⟨h2, h3⟩ := h
  refine ⟨pileWithinC_quiet hr hg hF h2, ?_⟩
  · cases hh : s'.here
    case mem a' =>
      obtain ⟨a, ha⟩ := hm a' hh
      unfold oneRowC at h3 ⊢
      rw [ha] at h3
      rw [hh, hr]
      exact h3
    all_goals (unfold oneRowC; rw [hh])

/-- **Where one pending row is laid behind the others.** -/
theorem withinFact_push {s s' : S} {lay : WsLay} {im : ℕ} {o : WsForkOut} {claims : ℕ}
    {Sh : LinShape} {row : TensorRow} {oracles' : Array OnBytes.Oracle}
    (hp : pendingRowO lay im o claims Sh s.st.oracles = .ok (row, oracles'))
    (hr : s'.rows = s.rows ++ [row]) (hg : Grows s.st s'.st) (hF : FitStays s.st s'.st)
    (hh : ∀ a', s'.here ≠ .mem a') (h : WithinFact s) : WithinFact s' := by
  obtain ⟨h2, -⟩ := h
  unfold pileWithinC at h2
  rw [Bool.and_eq_true] at h2
  obtain ⟨-, f2, -⟩ := pendingRowO_ledgers hp ((ledgersC s).1 h2.1)
  refine ⟨?_, oneRowC_not_mem hh⟩
  unfold pileWithinC
  rw [Bool.and_eq_true]
  refine ⟨(ledgersC s').2 (hF ((ledgersC s).1 h2.1)), (rowsWithin_iff s').2 fun r hr' t ht => ?_⟩
  rw [hr, List.mem_append, List.mem_singleton] at hr'
  have hlt : t.1.index < tableSizeC s.st t.1.oracle .mask := by
    rcases hr' with hr' | rfl
    · exact (rowsWithin_iff s).1 h2.2 r hr' t ht
    · rw [(f2 t ht).1]
      exact (f2 t ht).2
  exact tableSizeC_grows hg _ _ _ hlt

theorem withinFact_start {s : S} (hp : s.out.pending = []) (ho : s.st.oracles = #[])
    (hh : s.here = .between) : WithinFact s := by
  have hr : s.rows = [] := by
    unfold S.rows
    rw [hh]
    exact hp
  refine ⟨?_, oneRowC_not_mem fun a ha => by rw [hh] at ha; cases ha⟩
  unfold pileWithinC
  rw [Bool.and_eq_true]
  refine ⟨(ledgersC s).2 (ledgersFit_none _ ho), ?_⟩
  unfold rowsWithinC
  rw [hr]
  rfl

/-- **Kind K13's batching.** -/
theorem atM3_withinFact {Cl : Type} (p : Where) :
    Decides (ofInv WithinFact) (atM3 (Cl := Cl) p) :=
  fun s rs gs s' h hf => by
    refine ⟨withinM3 ledgersC ledgersKept p s s' rs gs h hf.1, ?_⟩
    obtain ⟨r, hr, _, hne⟩ := rowMasks p s s' rs gs h
    obtain ⟨_, _, o, _, e⟩ := atM3_rec h
    have hh : s'.here = .mem o := by rw [e]
    unfold oneRowC
    rw [hh]
    show (match s'.rows with
      | [r] => !r.masks.isEmpty
      | _ => false) = true
    rw [hr]
    show (!r.masks.isEmpty) = true
    cases hm : r.masks with
    | nil => exact absurd hm hne
    | cons _ _ => rfl

/-- **THE RULE, general in the fact.** -/
theorem reach_inv {Pp T Cl : Type} (Inv : T → Prop) {ft : ℕ} {bs : List (Block T Cl)}
    {start : Pp → T} (h0 : ∀ z, Inv (start z)) (hp : ∀ b ∈ bs, b.planOk = true)
    (hb : ∀ b ∈ bs, b.planOk = true → Decides (ofInv Inv) b) {k : ℕ} {a : Pp × T}
    (h : Reach ft bs start k a) : Inv a.2 := by
  induction h with
  | zero z => exact h0 z
  | @succ k z s s' b _ hk hy ih =>
    obtain ⟨R, c, _, hs⟩ := hy
    obtain ⟨_, gs, hd⟩ := K1.step_ok ft b s s' R c _ hs
    exact hb b (List.mem_of_getElem? hk) (hp b (List.mem_of_getElem? hk)) s _ gs s' hd ih

end VerifiableInference.Desc.K13.Law
