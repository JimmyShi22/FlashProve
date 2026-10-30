-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Leaves.lean: WHAT THE SEATED BATCHING BLOCK LEAVES AS IT WAS. Statements and proofs
ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

The batching is three steps in a row: K9's draw, which lays K9's part into the state; the frame's gatherer, which runs
the OTHER kinds' runs of claims in the order's order; K9's adding, which lays K9's part again. So what the block
leaves of the state is what these leave: K9 can say it of its own two steps, each kind of its own run.
  **`left_of_behind`**   FROM `BatBehind p g s x y G s'` ALONE (Honest/K9/YesAtSeat.lean), g the frame's gatherer: no
      seat and no yes is spent. For EVERY relation R on states that holds of a state and itself, passes along two
      steps in a row, holds from a state to that state with K9's part laid into it AS K9's TWO STEPS LAY IT (the part
      that the lens reads there, turned in whatever but its field d), and holds from the state in front of each run of
      the order to the state that the run returns: R s s'
  `bat_leaves`, `step_leaves`   so of each yes of the seated block's decision, or of its step, at a segment of which
      `SeatedFree` holds (Honest/K9/AtSeatAll.lean)
  `get_st`         the part that the lens reads holds the state's own statement in its field d
  `setLeaves`, `set_leaves`, `setLeaves.refl`, `setLeaves.trans`   K9's OWN SHARE, ONCE FOR ALL: such a laying leaves
      SEVEN fields of the state: the statement, the book, the roots, the mark of failure, the check, what goes out,
      the request
  **`seven_left`**     `step_leaves` CALLED at R := `setLeaves`: these fields are left by the member, under ONE
      premise: each run of the order leaves them
  `pinLeft O`, `pinLeft_of_leaves`   the relation that the frame means its pins to read: for each
      number o in O the first sample row of the statement's oracle message number o is the same; `setLeaves` gives it
So a clause "the member leaves … as it was" at the batching is owed as: K9's share (here) and ONE clause for each run
of the order. No member. `left_of_behind` is called by `bat_leaves`, by `step_leaves` and by Honest/K9/Keeps.lean;
`bat_leaves` by no line; `step_leaves` by `seven_left`, which no line calls; `set_leaves`, `setLeaves.refl`,
`setLeaves.trans` and `pinLeft_of_leaves` here and by Honest/K9/Keeps.lean.
WHAT IS NOT CLAIMED. The clause of any kind's run: IT IS ASKED AT EVERY STATE AND NUMBER, not only at those that the
fold reaches: a kind whose run leaves a field only at reached states cannot pay it in this form. What the laying
leaves inside the open segment beside K9's part. That a pin reads no more than
`pinLeft`: a pin's text and a theorem to that end stand in a file that
is not imported here; its laying at the library's head is not typed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FromYes
import Johnson.Desc.ProofFile.Honest.K9.GatherFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **What is left, from `BatBehind` alone.** -/
theorem left_of_behind (p : Desc.K9.Where) (each : ℕ × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (ℕ × String)) (R : S → S → Prop) (hrefl : ∀ u, R u u)
    (htrans : ∀ u v z, R u v → R v z → R u z)
    (hset : ∀ u a q, Desc.K9.atS.get? u = some a → q.d = a.d → R u (Desc.K9.atS.set u q))
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n u z, run n u = .ok z → R u z.2)
    (s s' : S) (x : E) (y : S × Desc.K9.Part × List Claim) (G : Fork)
    (hB : BatBehind p (claimsInBy each bs order) s x y G s') : R s s' := by
  obtain ⟨t₁, hdraw, hz, he⟩ := gathered_split p _ s x y hB.gathered
  obtain ⟨a0, ha0⟩ := draw_open p s t₁ x hdraw
  have h1 : R s t₁ := by
    rw [draw_is p s t₁ x a0 ha0 hdraw]
    exact hset s a0 _ ha0 rfl
  obtain ⟨ls, _, hR⟩ := gather_ran each bs order t₁ (y.2.2, y.1) hz
  have h2 : R t₁ y.1 := (ran_inv bs (fun u => R t₁ u) order 0 t₁ ls y.1
    (fun o ho run hr n u z hu hzz => htrans _ _ _ hu (hrun o ho run hr n u z hzz)) (hrefl t₁) hR).2
  have h3 : R y.1 s' := by
    rw [hB.state]
    exact hset y.1 y.2.1 _ he rfl
  exact htrans _ _ _ h1 (htrans _ _ _ h2 h3)

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
  {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- What the seated block's decision leaves. -/
theorem bat_leaves (Sd : SeatedFree c Z l k Lk p w) (R : S → S → Prop) (hrefl : ∀ u, R u u)
    (htrans : ∀ u v z, R u v → R v z → R u z)
    (hset : ∀ u a q, Desc.K9.atS.get? u = some a → q.d = a.d → R u (Desc.K9.atS.set u q))
    (hrun : ∀ o ∈ Lk.order, ∀ run, claimsRunOf Lk.hear o = some run → ∀ n u z, run n u = .ok z → R u z.2)
    (s t : S) (x : E)
    (hd : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    R s t := by
  obtain ⟨y, G, hB, _, _⟩ := behind_of_yes Sd s t x hd
  exact left_of_behind p Lk.each Lk.hear Lk.order R hrefl htrans hset hrun s t x y G hB

/-- The same of each yes of the step. -/
theorem step_leaves (Sd : SeatedFree c Z l k Lk p w) (R : S → S → Prop) (hrefl : ∀ u, R u u)
    (htrans : ∀ u v z, R u v → R v z → R u z)
    (hset : ∀ u a q, Desc.K9.atS.get? u = some a → q.d = a.d → R u (Desc.K9.atS.set u q))
    (hrun : ∀ o ∈ Lk.order, ∀ run, claimsRunOf Lk.hear o = some run → ∀ n u z, run n u = .ok z → R u z.2)
    (ft : ℕ) (s t : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (t, n)) : R s t := by
  obtain ⟨_, _, _, _, _, y, G, hB, _, _⟩ := behind_of_step Sd ft s t rs cols n hy
  exact left_of_behind p Lk.each Lk.hear Lk.order R hrefl htrans hset hrun s t _ y G hB

/-- The part that the lens reads holds the state's own statement. -/
theorem get_st (t : S) (a : Desc.K9.Part) (h : Desc.K9.atS.get? t = some a) : a.d.st = t.st := by
  have h' : (t.link?.bind fun L => t.fork?.bind fun F => t.tl?.bind fun tl => (Desc.K9.usedOf t).bind fun used =>
      some ({ owed := Desc.K9.owedOf t, used := used, laid := Desc.K9.laidOf tl, L := L, F := F,
              d := { st := t.st, book := t.book, roots := t.roots, opened := [], loc := () } } : Desc.K9.Part)) =
      some a := h
  cases h1 : t.link? with
  | none => rw [h1] at h'; exact nomatch h'
  | some L =>
    rw [h1] at h'
    cases h2 : t.fork? with
    | none => rw [h2] at h'; exact nomatch h'
    | some F =>
      rw [h2] at h'
      cases h3 : t.tl? with
      | none => rw [h3] at h'; exact nomatch h'
      | some tl =>
        rw [h3] at h'
        cases h4 : Desc.K9.usedOf t with
        | none => rw [h4] at h'; exact nomatch h'
        | some used =>
          rw [h4] at h'
          rw [← Option.some.inj h']

/-- Seven fields of the state are the same. -/
def setLeaves (u v : S) : Prop :=
  v.st = u.st ∧ v.book = u.book ∧ v.roots = u.roots ∧ v.failed = u.failed ∧ v.check = u.check ∧ v.out = u.out ∧
    v.req = u.req

/-- **K9's own share**: laying K9's part, as its two steps lay it, leaves these seven. -/
theorem set_leaves (u : S) (a q : Desc.K9.Part) (ha : Desc.K9.atS.get? u = some a) (hq : q.d = a.d) :
    setLeaves u (Desc.K9.atS.set u q) := by
  have hst : q.d.st = u.st := by rw [hq]; exact get_st u a ha
  clear ha hq
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := u
  cases here with
  | head h0 =>
    obtain ⟨o1, o2⟩ : ∃ b, h0.opened = b := ⟨_, rfl⟩
    cases o1 with
    | true =>
      show setLeaves _ { ((S.mk st book roots rowsOwed failed check out (.head h0) req).putLink q.L).putFork q.F
        with st := q.d.st, rowsOwed := q.owed }
      simp only [S.putLink, S.putFork, o2, if_true, setLeaves, and_self, and_true]
      exact hst
    | false =>
      show setLeaves _ { ((S.mk st book roots rowsOwed failed check out (.head h0) req).putLink q.L).putFork q.F
        with st := q.d.st, rowsOwed := q.owed }
      simp only [S.putLink, S.putFork, o2, Bool.false_eq_true, if_false, setLeaves, and_self, and_true]
      exact hst
  | _ => exact ⟨hst, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A state leaves itself. -/
theorem setLeaves.refl (u : S) : setLeaves u u := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two steps in a row. -/
theorem setLeaves.trans {u v z : S} (h : setLeaves u v) (h' : setLeaves v z) : setLeaves u z :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- **The seven fields are left by the member**, if each run of the order leaves them. -/
theorem seven_left (Sd : SeatedFree c Z l k Lk p w)
    (hrun : ∀ o ∈ Lk.order, ∀ run, claimsRunOf Lk.hear o = some run → ∀ n u z, run n u = .ok z → setLeaves u z.2)
    (ft : ℕ) (s t : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (t, n)) : setLeaves s t :=
  step_leaves Sd setLeaves setLeaves.refl (fun _ _ _ h h' => h.trans h') set_leaves hrun ft s t rs cols n hy

/-- The first sample row of each oracle message whose number is in O is the same. -/
def pinLeft (O : List ℕ) (s s' : S) : Prop :=
  ∀ o ∈ O, ((s'.st.oracles[o]?).bind fun x => x.sampleRows[0]?) = ((s.st.oracles[o]?).bind fun x => x.sampleRows[0]?)

/-- Where the statement is left, so are its messages' first sample rows. -/
theorem pinLeft_of_leaves (O : List ℕ) {s s' : S} (h : setLeaves s s') : pinLeft O s s' := by
  intro o _
  rw [h.1]

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.left_of_behind
#print axioms ProofFile.Honest.K9.bat_leaves
#print axioms ProofFile.Honest.K9.step_leaves
#print axioms ProofFile.Honest.K9.get_st
#print axioms ProofFile.Honest.K9.set_leaves
#print axioms ProofFile.Honest.K9.setLeaves.refl
#print axioms ProofFile.Honest.K9.setLeaves.trans
#print axioms ProofFile.Honest.K9.seven_left
#print axioms ProofFile.Honest.K9.pinLeft_of_leaves
#print axioms ProofFile.Honest.K9.setLeaves
#print axioms ProofFile.Honest.K9.pinLeft
