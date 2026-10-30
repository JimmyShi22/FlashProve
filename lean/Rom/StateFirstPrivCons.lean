-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstPrivCons.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), index privacy, part 4: consistency of a replayed trace
(`consistent_replaySt`). Lemmas on tables; no probability.

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.) The reduction and the replay `replaySt` are in
Rom/StateFirstPrivReplay.lean, the reduction's table `Book` in Rom/StateFirstMix.lean; `drVal C b p`
is what the table b gives at the query p to dr.

  `note_le`, `loose_le`
                  Entering an answer, or storing a newly sampled answer at a query where the table
                  gave nothing, only adds (`Book.Le`).
  `mem_note`      An entry of the table after `note` is an old one or the new one.
  `replaySt_ok`   For every log l of the reduction, every list T of entries over the first family
                  and every table b whose entered answers, like the entries of l, are in T: there is
                  a table b' with `Book.Le C b b'` such that every entry of the replayed trace is
                  consistent with T and b' (`okEntry`).

The delicate point: a query to dr that is answered from an entered answer (`findBlock`) is not
written into `loose`. A later lookup gives the same hash block because the list of entered answers
grows only at its end and the search takes the oldest entry: this is `drVal_note`
(Rom/StateFirstRel.lean), used in `note_le`.

Limits: nothing on probabilities; nothing on logs that no run of the reduction produces, beyond the
statement itself (it holds for every log).
-/
import Rom.StateFirstPrivIdeal
import Rom.StateFirstRel

set_option autoImplicit false

namespace Rom
open ZKCP

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {X Pf : Type}

/-- whatever b gives at a query to dr, b' gives too -/
def Book.Le (b b' : Book S lam) : Prop := ∀ p r, drVal C b p = some r → drVal C b' p = some r

theorem note_le (b : Book S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    Book.Le C b (b.note C o q r) := by
  intro p r0 h
  cases hf : findMade b.made o q with
  | some r' => rw [note_old C b o q r r' hf]; exact h
  | none => rw [drVal_note C b o q r hf, h]; rfl

theorem loose_le (b : Book S lam) (p : (Dg lam × Dg lam) × ℕ)
    (v : Dg lam) (hp : drVal C b p = none) :
    Book.Le C b { b with loose := (p, v) :: b.loose } := by
  intro p' r0 h
  rw [drVal_loose, if_neg (fun e => by rw [e, hp] at h; cases h)]
  exact h

theorem mem_note (b : Book S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o)
    (x : QA S) (hx : x ∈ (b.note C o q r).made) : x ∈ b.made ∨ x = ⟨o, q, r⟩ := by
  unfold Book.note at hx
  split at hx
  · exact Or.inl hx
  · split at hx
    · exact Or.inl hx
    · rcases List.mem_append.1 hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)

/-- An entry of a trace over the second family is consistent with the list T and the table b: at an
oracle of the first family it is the image (`Link.toAns`) of an entry of T at the same query; at dr
it is what b gives. -/
def okEntry (T : List (QA S)) (b : Book S lam) : QA (stSpec S lam C) → Prop
  | ⟨.inl o, q, a⟩ => ∃ r : S.Rng o, (⟨o, q, r⟩ : QA S) ∈ T ∧ a = (C o).toAns r
  | ⟨.inr _, p, r⟩ => drVal C b p = some r

theorem replaySt_ok (T : List (QA S)) (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (n : ℕ) (b : Book S lam) (l : Log S X Pf), (∀ x ∈ b.made, x ∈ T) → (∀ x ∈ l.trace, x ∈ T) →
      ∃ b', Book.Le C b b' ∧ ∀ e ∈ (replaySt C V n b l).trace, okEntry C T b' e := by
  have nilCase : ∀ b : Book S lam,
      ∃ b', Book.Le C b b' ∧ ∀ e ∈ (Log.nil : Log (stSpec S lam C) X Pf).trace, okEntry C T b' e :=
    fun b => ⟨b, fun _ _ h => h, fun e he => by cases he⟩
  induction V with
  | halt => intro n b l _ _; exact nilCase b
  | sample mm k ih =>
    intro n b l hb hl
    simp only [replaySt]
    cases hc : l.coins with
    | nil => exact nilCase b
    | cons c cs =>
      by_cases hlt : c < mm + 1
      · simp only [hlt, dif_pos]
        exact ih _ n b { l with coins := cs } hb hl
      · simp only [hlt, dif_neg, not_false_iff]
        exact nilCase b
  | request k ih =>
    intro n b l hb hl
    cases n with
    | zero => exact nilCase b
    | succ n =>
      simp only [replaySt]
      cases hs : l.sessions with
      | nil => exact nilCase b
      | cons x xs => exact ih _ n b { l with sessions := xs } hb hl
  | query x q k ih =>
    intro n b l hb hl
    match x, q, k, ih with
    | .inl o, q, k, ih =>
      cases hk : b.kept C o q with
      | some r =>
        rw [replaySt_inl_some C n b k hk]
        obtain ⟨b', h1, h2⟩ := ih ((C o).toAns r) n b l hb hl
        refine ⟨b', h1, fun e he => ?_⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact ⟨r, hb _ (findMade_mem (kept_findMade hk).2), rfl⟩
        · exact h2 e he
      | none =>
        simp only [replaySt, hk]
        cases ht : l.trace with
        | nil => exact nilCase b
        | cons e0 tr =>
          dsimp only
          cases hf : findMade [e0] o q with
          | none => exact nilCase b
          | some r =>
            have he0 : (⟨o, q, r⟩ : QA S) = e0 := List.mem_singleton.1 (findMade_mem hf)
            have hin : (⟨o, q, r⟩ : QA S) ∈ T := hl _ (by rw [ht, he0]; exact List.mem_cons_self)
            obtain ⟨b', h1, h2⟩ := ih ((C o).toAns r) n (b.note C o q r) { l with trace := tr }
              (fun x hx => (mem_note C b o q r x hx).elim (hb x) (fun e => e ▸ hin))
              (fun x hx => hl x (by rw [ht]; exact List.mem_cons_of_mem _ hx))
            refine ⟨b', fun p r0 h => h1 p r0 (note_le C b o q r p r0 h), fun e he => ?_⟩
            rcases List.mem_cons.1 he with rfl | he
            · exact ⟨r, hin, rfl⟩
            · exact h2 e he
    | .inr u, p, k, ih =>
      cases h1 : drVal C b p with
      | some r =>
        rw [replaySt_dr_some C n b k h1]
        obtain ⟨b', h3, h4⟩ := ih r n b l hb hl
        refine ⟨b', h3, fun e he => ?_⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact h3 p r h1
        · exact h4 e he
      | none =>
        simp only [replaySt, h1]
        cases hc : l.coins with
        | nil => exact nilCase b
        | cons c cs =>
          by_cases hlt : c < nDg lam + 1
          · simp only [hlt, dif_pos]
            obtain ⟨b', h3, h4⟩ := ih (digE lam ⟨c, hlt⟩) n
              { b with loose := (p, digE lam ⟨c, hlt⟩) :: b.loose } { l with coins := cs } hb hl
            refine ⟨b', fun p' r0 h => h3 p' r0 (loose_le C b p _ h1 p' r0 h), fun e he => ?_⟩
            rcases List.mem_cons.1 he with rfl | he
            · exact h3 p _ (by rw [drVal_loose, if_pos rfl])
            · exact h4 e he
          · simp only [hlt, dif_neg, not_false_iff]
            exact nilCase b

/-- If the reduction's trace answers repeated queries in the same way, so does the replayed trace
(from the empty table). -/
theorem consistent_replaySt (V : Gen.AdvVerifier (stSpec S lam C) X Pf) (n : ℕ)
    (l : Log S X Pf) (h : Gen.TraceConsistent l.trace) :
    Gen.TraceConsistent (replaySt C V n ⟨[], []⟩ l).trace := by
  obtain ⟨b', _, hok⟩ :=
    replaySt_ok C l.trace V n ⟨[], []⟩ l (fun x hx => by cases hx) (fun x hx => hx)
  rintro (o | u) q r r' h1 h2
  · obtain ⟨s, hs, e⟩ := hok _ h1
    obtain ⟨s', hs', e'⟩ := hok _ h2
    rw [e, e', h o q s s' hs hs']
  · exact Option.some.inj ((hok _ h1).symm.trans (hok _ h2))

end Rom
