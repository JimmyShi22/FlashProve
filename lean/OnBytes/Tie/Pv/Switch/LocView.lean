-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Switch/LocView.lean: on a view, a run of the program's code switch between two groups
of a request's chain takes exactly two rounds off the view, and what these rounds hold.

OnBytes/Tie/Pv/Switch/LocRan.lean has the record of such a run. The laws on single calls are the
library's (`Blk.recvAnswer_inv`, `Blk.close_inv`, OnBytes/Iop/GroundLaws.lean, over `Chan.pending`;
`admit_inv`,
`join_inv`, `addRowsOnView_inv`, OnBytes/Slice/BlkCalls.lean; `singleRowsRead_frame`,
OnBytes/Slice/BlkCsRun.lean). Here they are put together. Statements and proofs.

Main names:
  `AteA A l A'`: the elements l were taken, as items of the kind "answer", off the first of the
    rounds A, and A' is left. `AteA.trans`.
  `answerSteps_view`, `sampleSteps_view`: the two loops of the sending's second part.
  `switchAdmit_ch`: the admission of the claims leaves the channel as it was, for every target.
  `LocRan.view`: the rounds not yet taken before the run are r₁, r₂ and those not yet taken behind
    it. r₁ holds no item and draws what the record has as the seed's draws. r₂ holds the answers, in
    the order of the sampled oracle messages, and no other item, and draws what the record has as
    the positions' draws. The roots of the oracle messages sent are no items of a view's round.
Limits: one direction: from a run's record. On a view alone. If a message is open at c, r₁ is what
is left of that round. Nothing is said on how a view is made from a file or from a transcript, on
the opened columns, or on which answer is which row's target (that is in the record:
`LocRan.answers`).
-/
import OnBytes.Tie.Pv.Switch.LocRan
import OnBytes.Iop.GroundLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice

/-- The elements l were taken, as answers, off the first of the rounds A, and A' is left. -/
def AteA (A : List Fmt.RoundView) (l : List E) (A' : List Fmt.RoundView) : Prop :=
  (l = [] ∧ A' = A) ∨ ∃ (r : Fmt.RoundView) (t : List Fmt.RoundView) (gs : List Fmt.ItemValue), A = r :: t ∧
    r.vals = l.map (fun x => Fmt.ItemValue.answer x.triple) ++ gs ∧ A' = { r with vals := gs } :: t

theorem AteA.nil (A : List Fmt.RoundView) : AteA A [] A := Or.inl ⟨rfl, rfl⟩

theorem AteA.trans {A B C : List Fmt.RoundView} {l m : List E} (h1 : AteA A l B) (h2 : AteA B m C) :
    AteA A (l ++ m) C := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨r, t, gs, a1, a2, a3⟩
  · exact h2
  · rcases h2 with ⟨rfl, rfl⟩ | ⟨r', t', gs', b1, b2, b3⟩
    · rw [List.append_nil]
      exact Or.inr ⟨r, t, gs, a1, a2, a3⟩
    · rw [a3] at b1
      obtain ⟨e1, e2⟩ := List.cons.inj b1
      subst e1
      subst e2
      refine Or.inr ⟨r, t, gs', a1, ?_, b3⟩
      have b2' : gs = m.map (fun x => Fmt.ItemValue.answer x.triple) ++ gs' := b2
      rw [a2, b2', List.map_append, List.append_assoc]

/-- One answer. -/
theorem recvAnswer_view (x : E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : Blk.recvAnswer.Yields c x c') :
    AteA c.ch.pending [x] c'.ch.pending ∧ c'.ch.dry = false := by
  obtain ⟨r, rest, vs, e1, e2, e3, e4⟩ := Blk.recvAnswer_inv x c c' hd h
  exact ⟨Or.inr ⟨r, rest, vs, e1, e2, e3⟩, e4.dry.trans hd⟩

/-- The loop over the answers of one oracle message. -/
theorem answerSteps_view (S : Statement) (seeds : List SampleSeed) (o : Nat) (s : OracleShape) :
    ∀ (l : List Nat) (rows : Array Row) (c : Ctx) (rows' : Array Row) (c' : Ctx),
      c.ch.dry = false → RunFold (answerStep S seeds o s) l rows c rows' c' →
      ∃ a : List E, a.length = l.length ∧ AteA c.ch.pending a c'.ch.pending ∧ c'.ch.dry = false
  | [], _, c, _, c', hd, h => by
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl, AteA.nil _, hd⟩
  | i :: l, rows, c, rows', c', hd, h => by
    obtain ⟨b1, c1, ⟨seed, row, y, -, -, hy, -⟩, h2⟩ := h
    obtain ⟨a1, d1⟩ := recvAnswer_view y c c1 hd hy
    obtain ⟨a, la, a2, d2⟩ := answerSteps_view S seeds o s l b1 c1 rows' c' d1 h2
    exact ⟨y :: a, by rw [List.length_cons, List.length_cons, la], a1.trans a2, d2⟩

/-- The loop over the sampled oracle messages. -/
theorem sampleSteps_view (S : Statement) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (c c' : Ctx), c.ch.dry = false →
      RunFold (sampleStep S seeds) l PUnit.unit c PUnit.unit c' →
      ∃ a : List E, a.length = (l.map fun x => x.2.answers).sum ∧
        AteA c.ch.pending a c'.ch.pending ∧ c'.ch.dry = false
  | [], c, c', hd, h => by
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl, AteA.nil _, hd⟩
  | x :: l, c, c', hd, h => by
    obtain ⟨_, c1, ⟨rows, c0, h0, hadm⟩, h2⟩ := h
    obtain ⟨a0, l0, t0, d0⟩ := answerSteps_view S seeds x.1 x.2 _ _ _ _ _ hd h0
    obtain ⟨_, _, _, _, _, _, _, e1⟩ := admit_inv _ _ _ _ hadm
    have p1 : c1.ch = c0.ch := by rw [e1]
    have d1 : c1.ch.dry = false := by rw [p1]; exact d0
    obtain ⟨a, la, t2, d2⟩ := sampleSteps_view S seeds l c1 c' d1 h2
    rw [p1] at t2
    refine ⟨a0 ++ a, ?_, t0.trans t2, d2⟩
    rw [List.length_append, l0, la, List.length_range, List.map_cons, List.sum_cons]

/-- A loop whose every turn leaves the channel as it was leaves it as it was. -/
theorem runFold_ch {α β : Type} (step : α → β → Ctx → β → Ctx → Prop)
    (hs : ∀ a b c b' c', step a b c b' c' → c'.ch = c.ch) :
    ∀ (l : List α) (b : β) (c : Ctx) (b' : β) (c' : Ctx), RunFold step l b c b' c' → c'.ch = c.ch
  | [], _, _, _, _, h => by rw [h.2]
  | a :: l, b, c, b', c', h => by
    obtain ⟨b1, c1, h1, h2⟩ := h
    exact (runFold_ch step hs l b1 c1 b' c' h2).trans (hs a b c b1 c1 h1)

/-- The admission of the claims leaves the channel as it was. -/
theorem switchAdmit_ch (old : SingleRows) (T : SwitchTarget) (gp : Nat) (out : Switched)
    (y : Array E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (switchAdmit old T gp out y).Yields c () c') : c'.ch = c.ch := by
  unfold switchAdmit at h
  have h0 : ∃ c0, c0.ch = c.ch ∧
      (do
        Blk.join gp out.g
        forIn (out.kept.zip T.kept) PUnit.unit fun p _ => do
            Blk.join gp p.fst p.snd.keptAgain
            pure (ForInStep.yield PUnit.unit)
        let S ← Blk.statement
        Blk.addRowsOnView gp fun _ => switchRows S old T out.g out.kept out.positions y :
        Blk Unit).Yields c0 () c' := by
    by_cases hm : 0 < T.shape.maskRows
    · simp only [hm, if_true] at h
      obtain ⟨_, c0, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
      obtain ⟨_, e0⟩ := onOracle_inv _ _ _ _ k1
      exact ⟨c0, by rw [e0], k2⟩
    · simp only [hm, if_false] at h
      obtain ⟨_, c0, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
      obtain ⟨_, e0⟩ := (Blk.yields_pure _ _ _ _).1 k1
      exact ⟨c0, by rw [e0], k2⟩
  obtain ⟨c0, e0, a0⟩ := h0
  obtain ⟨_, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 a0
  obtain ⟨_, _, _, _, _, _, _, e1⟩ := join_inv _ _ _ _ _ h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  have e2 : c2.ch = c1.ch := by
    refine runFold_ch (fun _ _ c _ c' => c'.ch = c.ch) (fun _ _ _ _ _ k => k) _ _ _ _ _
      (forIn_inv_array _ _ ?_ _ _ _ _ _ h2)
    intro a b d r d1 k
    obtain ⟨_, d2, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k
    obtain ⟨_, _, _, _, _, _, _, f1⟩ := join_inv _ _ _ _ _ k1
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 k2
    exact ⟨PUnit.unit, rfl, by rw [f1]⟩
  obtain ⟨S, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨_, e3⟩ := (Blk.yields_statement _ _ _).1 h3
  have q : c3.ch = c.ch := by rw [e3, e2, e1]; exact e0
  have hd3 : c3.ch.dry = false := by rw [q]; exact hd
  obtain ⟨_, _, _, e4⟩ := addRowsOnView_inv _ _ _ _ hd3 a3
  rw [e4]
  exact q

/-- THE TWO ROUNDS. -/
theorem LocRan.view {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice}
    {out : Switched} {c c' : Ctx} {D : LocTaken} (R : LocRan old T gp others out c c' D)
    (hd : c.ch.dry = false) :
    ∃ (r₁ r₂ : Fmt.RoundView) (ans : List E), c.ch.pending = r₁ :: r₂ :: c'.ch.pending ∧
      r₁.vals = [] ∧ r₁.drawn = D.dS ∧
      r₂.vals = ans.map (fun x => Fmt.ItemValue.answer x.triple) ∧ r₂.drawn = D.dL ∧
      ans.length = (((todoOf D.c0.st D.ids).zip D.shapes).map fun x => x.2.answers).sum ∧
      c'.ch.dry = false := by
  have p0 : D.c0.ch.pending = c.ch.pending := by rw [R.received]; rfl
  have d0 : D.c0.ch.dry = false := by rw [R.received]; exact hd
  obtain ⟨_, _, r₁, rest, _, _, _, s1, s2, s3, _, _, _, s4, _, _, _, _, _, s5, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ d0 R.seedRound
  obtain ⟨ans, la, ta, dA⟩ := sampleSteps_view _ _ _ _ _ s5 R.answers
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
  rcases ta with ⟨rfl, e⟩ | ⟨r', t, gs, a1, a2, a3⟩
  · rw [t1] at e
    exact ⟨r₁, r, [], by rw [← e], s2, s3.symm, t2, t3.symm, la, dE⟩
  · rw [t1] at a3
    obtain ⟨e1, e2⟩ := List.cons.inj a3
    have g0 : gs = [] := by
      have := congrArg Fmt.RoundView.vals e1
      rw [t2] at this
      exact this.symm
    rw [g0, List.append_nil] at a2
    refine ⟨r₁, r', ans, by rw [a1, e2], s2, s3.symm, a2, ?_, la, dE⟩
    rw [t3, e1]

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.switchAdmit_ch
#print axioms OnBytes.Tie.Pv.Switch.LocRan.view
