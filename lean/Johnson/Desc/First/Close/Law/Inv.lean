-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Inv.lean: what a yes of the closing of a link says: the functions of
Johnson/Desc/First/Close/Closing.lean read backwards. Statements and proofs.

Each theorem takes "the function returned this" and gives what the rounds held and how the result
was made. The proofs unfold the functions' own definitions.
  `ok_bind`, `need_ok`, `got_ok`: a yes of two steps in a row; of a named test; of a named lookup.
  `elems_of_mapM`: items that were all taken as elements are the elements' triples.
  `heard_inv`: a heard round holds just the elements returned, and drew just the element returned.
  `rounds_inv`: the fold's rounds hold two scalars each and drew the challenges returned; the claim
    returned is the running claim behind them (`claimAfter`); as many challenges as rounds.
  `fold_inv`: the fold, its mask sent earlier: the first round holds the sum and drew eps; then the
    k rounds; what is returned is `foldOutput` at the running claim from sum + eps * target.
  `bat_inv`: the batching: the group is there; the round drew x; the row returned is `Bat.combine`
    of the rows `runRows` in their fixed order, at the statement `begun`.
  `closing_inv`: the closing: the two together; as many challenges as the plan's k.
Holds, RoundsHold and claimAfter are plain definitions on rounds of a view
(OnBytes/Tie/Pv/Psc/Run/ViewRounds.lean, OnBytes/Tie/Pv/Fold/FoldView.lean).

Limits. One direction. Of the tests that the functions make, only those are handed on that
Johnson/Desc/First/Close/Law/Proof.lean spends: nothing on the entries, the shapes, the mask or the
statement behind (for these: InvMore.lean and HandsOn.lean beside this file).
Read by one other team as part of the law's proof.
-/
import Johnson.Desc.First.Close.Closing
import OnBytes.Tie.Pv.Fold.FoldView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold

theorem ok_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  unfold need at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem got_ok {α : Type} {n : String} {x : Option α} {a : α} (h : got n x = .ok a) :
    x = some a := by
  cases x with
  | none => exact absurd h (by simp [got])
  | some b => simpa [got] using h

/-- Items that are all elements. -/
theorem elems_of_mapM : ∀ (vs : List Fmt.ItemValue) (xs : List E),
    (vs.mapM fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none) = some xs → vs = xs.map fun x => Fmt.ItemValue.e x.triple
  | [], xs, h => by
    simp at h
    subst h
    rfl
  | v :: vs, xs, h => by
    rw [List.mapM_cons] at h
    cases v with
    | e t =>
      simp only [bind, Option.bind] at h
      cases hm : (vs.mapM fun v => match v with
        | .e x => some (E.ofTriple x)
        | _ => none) with
      | none => simp [hm] at h
      | some ys =>
        simp [hm] at h
        subst h
        rw [List.map_cons, ← elems_of_mapM vs ys hm]
        rfl
    | _ => simp [bind, Option.bind] at h

/-- What a heard round holds. -/
theorem heard_inv {name : String} {items : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {roots : Nat}
    {xs : List E} {x : E} (h : heard name items e r roots = .ok (xs, x)) :
    Holds r xs ∧ r.drawn.elems = [x.triple] := by
  unfold heard at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨ys, h1, h⟩ := ok_bind h
  have h1 := got_ok h1
  split at h
  · rename_i t ht
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨elems_of_mapM _ _ h1, ht⟩
  · exact absurd h (by simp)

/-- What the fold's rounds hold. -/
theorem rounds_inv : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (claim : E) (gs : List E) (cl : E),
    rounds es rs claim = .ok (gs, cl) →
    ∃ qs, RoundsHold rs qs gs ∧ cl = claimAfter claim qs gs ∧ gs.length = rs.length
  | [], [], claim, gs, cl, h => by
    simp only [rounds, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], trivial, rfl, rfl⟩
  | e :: es, r :: rs, claim, gs, cl, h => by
    rw [rounds] at h
    obtain ⟨y, h1, h⟩ := ok_bind h
    split at h
    · rename_i c0 c2 g
      obtain ⟨x, h2, h⟩ := ok_bind h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨a1, a2⟩ := heard_inv h1
      obtain ⟨qs, b1, b2, b3⟩ := rounds_inv es rs _ x.1 x.2 h2
      refine ⟨(c0, c2) :: qs, ⟨a1, a2, b1⟩, ?_, ?_⟩
      · rw [claimAfter_cons]
        exact b2
      · rw [List.length_cons, List.length_cons, b3]
    · exact absurd h (by simp)
  | [], _ :: _, _, _, _, h => by simp [rounds] at h
  | _ :: _, [], _, _, _, h => by simp [rounds] at h

/-- What a yes of the fold says, its mask sent earlier. -/
theorem fold_inv {S S' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : fold S F row m es rs = .ok (out, S')) :
    ∃ (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (sum eps : E) (qs : List (E × E)) (gs : List E)
      (S2 : Statement),
      rs = rE :: rR ∧ Holds rE [sum] ∧ rE.drawn.elems = [eps.triple] ∧ RoundsHold rR qs gs ∧
      gs.length = F.layout.k ∧
      out = foldOutput S2 F row m eps gs (claimAfter (maddE sum eps row.target) qs gs) := by
  unfold fold at h
  cases hD : foldD 0 (onSt S) F row (some m) es rs with
  | error e => rw [hD] at h; exact absurd h (by simp [Except.map])
  | ok y =>
    rw [hD] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    unfold foldD at hD
    split at hD
    · rename_i eE eR rE rR
      obtain ⟨_, k1, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨p, k2, hD⟩ := ok_bind hD
      simp only [pure, Except.pure, Except.ok.injEq] at k2
      subst k2
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨d2, -, hD⟩ := ok_bind hD
      obtain ⟨z, k3, hD⟩ := ok_bind hD
      split at hD
      · rename_i sum eps
        obtain ⟨_, -, hD⟩ := ok_bind hD
        obtain ⟨w, k4, hD⟩ := ok_bind hD
        simp only [pure, Except.pure, Except.ok.injEq] at hD
        subst hD
        obtain ⟨a1, a2⟩ := heard_inv k3
        obtain ⟨qs, b1, b2, b3⟩ := rounds_inv eR rR _ w.1 w.2 k4
        have k1 := need_ok k1
        simp only [Bool.and_eq_true, beq_iff_eq] at k1
        refine ⟨rE, rR, sum, eps, qs, w.1, d2.st, rfl, a1, a2, b1, by rw [b3, k1.2], ?_⟩
        show foldOutput d2.st F row m eps w.1 w.2 = _
        rw [b2]
      · exact absurd hD (by simp)
    · exact absurd hD (by simp)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- What a yes of the batching says. (The proof reads `beginRunP`'s yes in two ways, the first that
fits: one for a text that has the layout by a function that always returns, as the ground's text
has it, and one for a text that has it by a bind.) -/
theorem bat_inv {S S1 : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow}
    {lay : GroupLayout} (h : bat S g e r = .ok (row, lay, S1)) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ r.drawn.elems = [x.triple] ∧
      Bat.combine (begun S g G) g ⟨lay, runRows S G⟩ x = some row ∧ S1 = begun S g G := by
  unfold bat at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨p, k1, h⟩ := ok_bind h
  have k1 := got_ok k1
  obtain ⟨x, k2, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨row', k3, h⟩ := ok_bind h
  have k3 := got_ok k3
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  unfold Ground.beginRunP at k1
  split at k1
  · cases hG : (onSt S).st.groups[g]? with
    | none => simp [hG] at k1
    | some G =>
      have k1' : ∃ l,
          p = (⟨l, runRows (onSt S).st G⟩, { onSt S with st := begun (onSt S).st g G }) := by
        first
          | (simp [hG] at k1
             exact ⟨_, k1.symm⟩)
          | (cases hl : (onSt S).st.layout g with
             | none => simp [hG, hl] at k1
             | some l =>
               simp [hG, hl] at k1
               exact ⟨l, k1.symm⟩)
      obtain ⟨l, rfl⟩ := k1'
      cases hh : heard "BAT" 0 e r with
      | error e' => rw [hh] at k2; exact absurd k2 (by simp [Except.map])
      | ok y =>
        rw [hh] at k2
        simp only [Except.map, Except.ok.injEq] at k2
        subst k2
        exact ⟨G, y.2, hG, (heard_inv (xs := y.1) (x := y.2) hh).2, k3, rfl⟩
  · exact absurd k1 (by simp)

/-- **What a yes of the closing says.** -/
theorem closing_inv {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ (G : Group) (x : E) (row : GroupRow) (lay : GroupLayout) (m : Nat) (F : FoldShape)
      (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (sum eps : E) (qs : List (E × E)) (gs : List E)
      (S2 : Statement),
      rs = rB :: rE :: rR ∧ S.groups[g]? = some G ∧ rB.drawn.elems = [x.triple] ∧
      Bat.combine (begun S g G) g ⟨lay, runRows S G⟩ x = some row ∧
      Holds rE [sum] ∧ rE.drawn.elems = [eps.triple] ∧ RoundsHold rR qs gs ∧ gs.length = P.k ∧
      out = foldOutput S2 F row m eps gs (claimAfter (maddE sum eps row.target) qs gs) := by
  unfold closing at h
  split at h
  · rename_i eB es rB rs' _
    obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨G, x, a1, a2, a3, -⟩ := bat_inv (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    obtain ⟨rE, rR, sum, eps, qs, gs, S2, b1, b2, b3, b4, b5, b6⟩ := fold_inv h
    refine ⟨G, x, p.1, p.2.1, m, _, rB, rE, rR, sum, eps, qs, gs, S2, by rw [b1], a1, a2, a3, b2,
      b3, b4, ?_, b6⟩
    rw [b5]
    rfl
  · exact absurd h (by simp)

end VerifiableInference.Desc.First.Close
