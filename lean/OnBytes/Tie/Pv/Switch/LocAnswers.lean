-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Switch/LocAnswers.lean: the answers that the second round of the program's code
switch holds are, one by one, the targets of the sample rows with which the sampled oracle messages
were admitted.

OnBytes/Tie/Pv/Switch/LocView.lean says that a run of the switch on a view takes two rounds off the
view, and that the second holds answers, as many as the sampled oracle messages have. This file says
which: it walks the two loops of the sending's second part once more and keeps the rows. Statements
and proofs.

Main names:
  `targets rows`: the targets of an array of rows, in order.
  `Admitted S seeds l rowss c c'`: message by message of the list l: the answers of the message were
    received, which made its sample rows (the entry of rowss at its place), and it was admitted with
    these rows.
  `answerSteps_rows`: the loop over one message's answers: the elements taken off the view are the
    targets of the rows that were added.
  `sampleSteps_rows`: the loop over the sampled messages: there is a list rowss with `Admitted`, and
    the elements taken off the view are the targets of its arrays, one array after the other.
  `LocRan.view_rows`: the statement of `LocRan.view` with that: r₂ holds, as its only items, the
    targets of the sample rows with which the sampled oracle messages were admitted, in the order of
`todoOf`.
Limits: those of OnBytes/Tie/Pv/Switch/LocView.lean. That the rows admitted are still the
messages' sample rows in the statement behind the run is not said. What a sample row's coefficients
are is in `answerStep` (OnBytes/Slice/BlkSendRun.lean: `Send.form` at the seed).

-/
import OnBytes.Tie.Pv.Switch.LocView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice

/-- The targets of an array of rows. -/
def targets (rows : Array Row) : List E := rows.toList.map (·.target)

/-- Message by message: the answers were received, which made the sample rows, and the message was
admitted with them. -/
def Admitted (S : Statement) (seeds : List SampleSeed) :
    List (Nat × OracleShape) → List (Array Row) → Ctx → Ctx → Prop
  | [], [], c, c' => c' = c
  | x :: l, rows :: rs, c, c' => ∃ c0 c1,
      RunFold (answerStep S seeds x.1 x.2) (List.range x.2.answers) #[] c rows c0 ∧
      (Send.admit x.1 rows).Yields c0 () c1 ∧ Admitted S seeds l rs c1 c'
  | _, _, _, _ => False

/-- The loop over the answers of one oracle message, with the rows. -/
theorem answerSteps_rows (S : Statement) (seeds : List SampleSeed) (o : Nat) (s : OracleShape) :
    ∀ (l : List Nat) (rows : Array Row) (c : Ctx) (rows' : Array Row) (c' : Ctx),
      c.ch.dry = false → RunFold (answerStep S seeds o s) l rows c rows' c' →
      ∃ a : List E, targets rows' = targets rows ++ a ∧ AteA c.ch.pending a c'.ch.pending ∧
        c'.ch.dry = false
  | [], _, c, _, c', hd, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], (List.append_nil _).symm, AteA.nil _, hd⟩
  | i :: l, rows, c, rows', c', hd, h => by
    obtain ⟨b1, c1, ⟨seed, row, y, -, -, hy, rfl⟩, h2⟩ := h
    obtain ⟨a1, d1⟩ := recvAnswer_view y c c1 hd hy
    obtain ⟨a, ea, a2, d2⟩ := answerSteps_rows S seeds o s l _ c1 rows' c' d1 h2
    refine ⟨y :: a, ?_, a1.trans a2, d2⟩
    rw [ea]
    simp [targets]

/-- The loop over the sampled oracle messages, with the rows. -/
theorem sampleSteps_rows (S : Statement) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (c c' : Ctx), c.ch.dry = false →
      RunFold (sampleStep S seeds) l PUnit.unit c PUnit.unit c' →
      ∃ rowss : List (Array Row), Admitted S seeds l rowss c c' ∧
        AteA c.ch.pending (rowss.flatMap targets) c'.ch.pending ∧ c'.ch.dry = false
  | [], c, c', hd, h => by
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl, AteA.nil _, hd⟩
  | x :: l, c, c', hd, h => by
    obtain ⟨_, c1, ⟨rows, c0, h0, hadm⟩, h2⟩ := h
    obtain ⟨a0, e0, t0, d0⟩ := answerSteps_rows S seeds x.1 x.2 _ _ _ _ _ hd h0
    obtain ⟨_, _, _, _, _, _, _, e1⟩ := admit_inv _ _ _ _ hadm
    have p1 : c1.ch = c0.ch := by rw [e1]
    have d1 : c1.ch.dry = false := by rw [p1]; exact d0
    obtain ⟨rs, ha, t2, d2⟩ := sampleSteps_rows S seeds l c1 c' d1 h2
    rw [p1] at t2
    refine ⟨rows :: rs, ⟨c0, c1, h0, hadm, ha⟩, ?_, d2⟩
    have e0' : targets rows = a0 := by
      rw [e0]
      simp [targets]
    rw [List.flatMap_cons, e0']
    exact t0.trans t2

/-- THE TWO ROUNDS, WITH THE ROWS. -/
theorem LocRan.view_rows {old : SingleRows} {T : SwitchTarget} {gp : Nat}
    {others : Array OracleNotice} {out : Switched} {c c' : Ctx} {D : LocTaken}
    (R : LocRan old T gp others out c c' D) (hd : c.ch.dry = false) :
    ∃ (r₁ r₂ : Fmt.RoundView) (rowss : List (Array Row)), c.ch.pending = r₁ :: r₂ :: c'.ch.pending ∧
      r₁.vals = [] ∧ r₁.drawn = D.dS ∧
      Admitted D.c0.st D.seeds ((todoOf D.c0.st D.ids).zip D.shapes) rowss D.c1 D.cA ∧
      r₂.vals = (rowss.flatMap targets).map (fun x => Fmt.ItemValue.answer x.triple) ∧
      r₂.drawn = D.dL ∧ c'.ch.dry = false := by
  have p0 : D.c0.ch.pending = c.ch.pending := by rw [R.received]; rfl
  have d0 : D.c0.ch.dry = false := by rw [R.received]; exact hd
  obtain ⟨_, _, r₁, rest, _, _, _, s1, s2, s3, _, _, _, s4, _, _, _, _, _, s5, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ d0 R.seedRound
  obtain ⟨rowss, hadm, ta, dA⟩ := sampleSteps_rows _ _ _ _ _ s5 R.answers
  obtain ⟨_, _, r, rest₂, _, _, _, t1, t2, t3, _, _, _, t4, _, _, _, _, _, t5, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ dA R.locRound
  have fC := singleRowsRead_frame _ _ _ _ _ t5 R.read
  have dD : D.cD.ch.dry = false := by rw [R.notes.ch, fC.dry]; exact t5
  have pE : c'.ch.pending = rest₂ := by
    rw [switchAdmit_ch _ _ _ _ _ _ _ dD R.admitted, R.notes.ch, fC.pending]
    exact t4
  have dE : c'.ch.dry = false := by
    rw [switchAdmit_ch _ _ _ _ _ _ _ dD R.admitted]
    exact dD
  rw [s4] at ta
  rw [← p0, s1, pE]
  rcases ta with ⟨e0, e⟩ | ⟨r', t, gs, a1, a2, a3⟩
  · rw [t1] at e
    exact ⟨r₁, r, rowss, by rw [← e], s2, s3.symm, hadm, by rw [e0]; exact t2, t3.symm, dE⟩
  · rw [t1] at a3
    obtain ⟨e1, e2⟩ := List.cons.inj a3
    have g0 : gs = [] := by
      have := congrArg Fmt.RoundView.vals e1
      rw [t2] at this
      exact this.symm
    rw [g0, List.append_nil] at a2
    refine ⟨r₁, r', rowss, by rw [a1, e2], s2, s3.symm, hadm, a2, ?_, dE⟩
    rw [t3, e1]

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.sampleSteps_rows
#print axioms OnBytes.Tie.Pv.Switch.LocRan.view_rows
