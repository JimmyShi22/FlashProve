-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/MovesBlock.lean
(kind K9's soundness lemma): THEOREMS: BLOCKS THAT ARE A DRAW WITH MOVES BEHIND
IT (Law/Moves.lean: DrawMoves): K9's draw (K9.drawAlone) joined by Block.andThen with blocks
without a round: the form of K9's place in a description that adds the claims step by step.
  Staged        the same at the block's decision: its one round is the draw's; a yes of its decision
                is a yes of the draw's decision on the first round and then of the row of moves.
  staged_draw   the draw alone: no move.
  staged_then   a staged block, and then a block without a round whose yes is a yes of moves.
  movesYes_append   two rows of moves in a row.
  addsStep_moves    **a step of adding (Batch/Objects.lean: addsStep) is two moves**: add (gather ws
                cut runs), quiet behind. (The counts in front are passed by: nothing is made of
                them. These few lines say the part of that step's yes
                that is used here, over Law/Calls.lean: adds_decide.)
  quiet_moves   a block whose decision reads neither rounds nor groups is one quiet move.
  drawAlone_one, drawMoves_of_staged   **Staged gives DrawMoves.**
No premise beyond those in the statements. Nothing on any seat's list of blocks.

-/
import Johnson.Desc.First.Batch.Objects
import Johnson.Desc.First.Batch.Law.Calls
import Johnson.Desc.First.Batch.Law.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where drawAlone drawnClean addsStep gather RunOf Window)

variable {T Cl : Type}

/-- A draw with moves behind it, at the block's decision. -/
structure Staged (X : Lens T) (p : Where) (ms : List (Move T)) (b : Block T Cl) : Prop where
  rounds : b.rounds = [{ entry := K9.entry p }]
  dec : ∀ s rs gs s', b.decide s rs gs = .ok s' →
    ∃ t₁ cls, (drawAlone (Cl := Cl) X p).decide s (rs.take 1) [] = .ok t₁ ∧
      MovesYes X ms t₁ s' cls

theorem staged_draw (X : Lens T) (p : Where) : Staged X p [] (drawAlone (Cl := Cl) X p) where
  rounds := rfl
  dec := by
    intro s rs gs s' h
    have h0 := h
    simp only [drawAlone] at h
    match rs, h, h0 with
    | [r], _, h0 => exact ⟨s', [], h0, rfl, rfl⟩

theorem movesYes_append (X : Lens T) : ∀ (ms ms' : List (Move T)) (t u v : T)
    (c c' : List Claim), MovesYes X ms t u c → MovesYes X ms' u v c' →
    MovesYes X (ms ++ ms') t v (c ++ c')
  | [], ms', t, u, v, c, c', h, h' => by
    obtain ⟨rfl, rfl⟩ := h
    exact h'
  | m :: l, ms', t, u, v, c, c', h, h' => by
    obtain ⟨w, c₁, c₂, h1, h2, rfl⟩ := h
    exact ⟨w, c₁, c₂ ++ c', h1, movesYes_append X l ms' w u v c₂ c' h2 h',
      List.append_assoc _ _ _⟩

/-- A staged block, and then a block without a round. -/
theorem staged_then (X : Lens T) (p : Where) (ms ms' : List (Move T)) (b q : Block T Cl)
    (name : String) (h : Staged X p ms b) (hq : q.rounds = [])
    (hd : ∀ t rs gs t', q.decide t rs gs = .ok t' → ∃ cls, MovesYes X ms' t t' cls) :
    Staged X p (ms ++ ms') (b.andThen name q) where
  rounds := by
    show b.rounds ++ q.rounds = _
    rw [h.rounds, hq]
    rfl
  dec := by
    intro s rs gs s' hy
    have hy' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind (fun t =>
      q.decide t (rs.drop b.rounds.length) (gs.drop b.openings)) = .ok s' := hy
    cases h1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error e =>
      rw [h1] at hy'
      exact nomatch hy'
    | ok t =>
      rw [h1] at hy'
      obtain ⟨t₁, c, d1, m1⟩ := h.dec _ _ _ _ h1
      obtain ⟨c', m2⟩ := hd _ _ _ _ hy'
      have e : (rs.take b.rounds.length).take 1 = rs.take 1 := by
        rw [h.rounds]
        simp [List.take_take]
      rw [e] at d1
      exact ⟨t₁, c ++ c', d1, movesYes_append X ms ms' _ _ _ _ _ m1 m2⟩

/-- **A step of adding is two moves.** -/
theorem addsStep_moves (X : Lens T) (p : Where) (what : String)
    (counts : List (String × (T → Bool))) (ws : T → List Window) (cut : List (Nat × String))
    (runs : List (RunOf T)) (behind : T → Except String T) (t : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (t' : T)
    (h : (addsStep (Cl := Cl) X p what counts ws cut runs behind).decide t rs gs = .ok t') :
    ∃ cls, MovesYes X [.add (gather ws cut runs), .quiet behind] t t' cls := by
  simp only [addsStep] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t₁, h1, h⟩ := ok_bind h
  obtain ⟨cls, e, b, G, hf, hb, hG, rfl⟩ := adds_decide X p _ _ _ t rs gs t₁ h1
  exact ⟨cls ++ ([] ++ []), _, cls, [] ++ [], ⟨e, b, G, hf, hb, hG, rfl⟩,
    ⟨t', [], [], ⟨h, rfl⟩, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- A block whose decision reads neither rounds nor groups is one quiet move. -/
theorem quiet_moves (X : Lens T) (q : Block T Cl) (f : T → Except String T)
    (hq : ∀ t rs gs, q.decide t rs gs = f t) (t : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (t' : T) (h : q.decide t rs gs = .ok t') :
    ∃ cls, MovesYes X [.quiet f] t t' cls := by
  rw [hq] at h
  exact ⟨[] ++ [], t', [], [], ⟨h, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- The draw's decision on one round, as the step shows it. -/
theorem drawAlone_one (X : Lens T) (p : Where) (s : T) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (t₁ : T)
    (h : (drawAlone (Cl := Cl) X p).decide s [noDigest r] gs = .ok t₁) :
    ∃ x a o, r.drawn.elems = [x] ∧ X.get? s = some a ∧
      drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o ∧
      t₁ = X.set s { a with owed := o.owed, L := o.L, F := o.F } := by
  simp only [drawAlone] at h
  obtain ⟨a, ha, h⟩ := ok_bind h
  obtain ⟨chi, hchi, h⟩ := ok_bind h
  obtain ⟨o, ho, h⟩ := ok_bind h
  have e1 := Except.ok.inj h
  have hc := there_ok hchi
  have hel : (noDigest r).drawn.elems = r.drawn.elems := rfl
  rw [hel] at hc
  match hq : r.drawn.elems, hc with
  | [x], hc =>
    have ec : E.ofTriple x = chi := Option.some.inj hc
    subst ec
    exact ⟨x, a, o, rfl, there_ok ha, ho, e1.symm⟩

theorem roundsFit_one (d : Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit [d] rs = true) :
    ∃ r, rs = [r] := by
  match rs, h with
  | [r], _ => exact ⟨r, rfl⟩
  | r :: r' :: l, h => simp [roundsFit] at h

/-- **Staged gives DrawMoves.** -/
theorem drawMoves_of_staged (X : Lens T) (p : Where) (ms : List (Move T)) (b : Block T Cl)
    (h : Staged X p ms b) : DrawMoves X p ms b := by
  intro ft s rs cols s' k hs
  unfold Block.step at hs
  obtain ⟨_, hfit, hs⟩ := ok_bind hs
  obtain ⟨_, _, hs⟩ := ok_bind hs
  obtain ⟨t', hdec, hs⟩ := ok_bind hs
  have e : t' = s' := congrArg Prod.fst (Except.ok.inj hs)
  subst e
  have hfit' : roundsFit b.rounds rs = true := by
    unfold need at hfit
    split at hfit
    · assumption
    · exact nomatch hfit
  rw [h.rounds] at hfit'
  obtain ⟨r, rfl⟩ := roundsFit_one _ _ hfit'
  obtain ⟨t₁, cls, d1, m1⟩ := h.dec _ _ _ _ hdec
  obtain ⟨x, a, o, hx, ha, ho, rfl⟩ := drawAlone_one X p s r [] t₁ d1
  exact ⟨r, x, a, o, cls, rfl, hx, ha, ho, m1⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.staged_draw
#print axioms VerifiableInference.Desc.K9L.staged_then
#print axioms VerifiableInference.Desc.K9L.addsStep_moves
#print axioms VerifiableInference.Desc.K9L.quiet_moves
#print axioms VerifiableInference.Desc.K9L.drawMoves_of_staged
