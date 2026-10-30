-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/DealLaw.lean: dealOk p = true gives what the law's arithmetic of dealing wants
of the declared rounds of the proximity test (the kind K12), so that the test
Johnson/Desc/K12/Law/DealOk.lean is no transcription.

Statements and proofs.
Main names:
  `nOpenB_eq`: the test's count of a cut's groups is nOpen (Johnson/Desc/K12/Law/JointK.lean).
  `OneAt`: the rounds cut declare just one opening o and no stored table; o's uncut label is
    firstTree + free + own + (j - 1), its source "own", number free + own + (j - 1), its depth and
    width the entry number own + (j - 1) of TestNums.sent: the tree that switch j - 1 sends, by the
    plan.
  `nOpen_of_flat`, `OneAt.nOpen`: such a cut has nOpen = 1.
  `oneAt_of_ok`: the five clauses' yes gives OneAt.
  `Dealt`: by recursion, as stagesFrom cuts (in cutF and cutS of Johnson/Desc/K12/Law/JointK.lean):
    at a stage but the last nOpen (cutF l k) = 0, for j ≥ 1 OneAt at cutS l k, on at l.drop (k + 3);
    at the last stage j ≥ 1 and OneAt at all that is left, which is two rounds.
  `dealt_of_walk`, `dealt_of_ok`: dealOk p = true gives Dealt p 0 a rest (laidS p).
So in srcFrom (Johnson/Desc/K12/Law/Written.lean), at a stage j ≥ 1, "i < nOpen (cutF ...) + nOpen
(cutS ...)" is "i < 1": just the one opening, whose declared label is that of the tree which the
switch before has sent. In srcFirst the cut-off subtraction at i < nOpen (cutF ...) is idle, since
there is no such i.
Limits: No soundness is claimed, and nothing is said on hiding.
Dealt speaks at cur.k; the chain's s.h + s.g is that under h ≤ k (sg_k,
Johnson/Desc/K12/Law/FirstCutLaw.lean).
It does not say that the written round of switch j - 1 carries that label in its tree
(Johnson/Desc/K12/Law/TieLaw.lean does), nor anything of stage 0's openings but that the fold's cut
declares none. The clause 0:some is spent by no theorem.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.StepAt
import Johnson.Desc.K12.Law.DealOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw

theorem nOpenB_eq : ∀ (cut : List Fmt.DeclaredRound), nOpenB cut = nOpen cut
  | [] => rfl
  | d :: l => by
    rw [nOpen_cons, ← nOpenB_eq l]
    rfl

/-- The rounds cut declare just one opening and no stored table: the tree that switch j − 1 sends,
by its uncut label, its source, its depth and width. -/
structure OneAt (p : P12) (j : ℕ) (cut : List Fmt.DeclaredRound) (o : Fmt.Shape × Fmt.TreeSource) : Prop
    where
  one : cut.flatMap (·.opens) = [o]
  stored : ∀ d ∈ cut, d.stored = []
  label : o.1.tree = p.nums.firstTree + p.nums.free + (ownN p + (j - 1))
  src : o.2 = .own (p.nums.free + (ownN p + (j - 1)))
  sent : ∃ x, p.nums.sent[ownN p + (j - 1)]? = some x ∧ x.1 = o.1.a ∧ x.2 = o.1.W

theorem nOpen_of_flat : ∀ (cut : List Fmt.DeclaredRound), (∀ d ∈ cut, d.stored = []) →
    nOpen cut = (cut.flatMap (·.opens)).length
  | [], _ => rfl
  | d :: l, h => by
    rw [nOpen_cons, List.flatMap_cons, List.length_append,
      nOpen_of_flat l fun x hx => h x (List.mem_cons_of_mem _ hx), h d List.mem_cons_self]
    simp

theorem OneAt.nOpen {p : P12} {j : ℕ} {cut : List Fmt.DeclaredRound} {o : Fmt.Shape × Fmt.TreeSource}
    (h : OneAt p j cut o) : H2K.JointK.nOpen cut = 1 := by
  rw [nOpen_of_flat cut h.stored, h.one]
  rfl

theorem oneAt_of_ok (p : P12) (j : ℕ) (cut : List Fmt.DeclaredRound)
    (h : ok (oneL p 0 j cut) = true) : ∃ o, OneAt p j cut o := by
  unfold ok oneL at h
  dsimp only at h
  split at h
  · rename_i o ho
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.all_eq_true, List.isEmpty_iff, Nat.add_zero, Option.any_eq_true] at h
    obtain ⟨h1, h2, h3, ⟨x, hx, hxa⟩, ⟨y, hy, hyW⟩⟩ := h
    refine ⟨o, ho, h1, h2, h3, x, hx, hxa, ?_⟩
    rw [hx] at hy
    cases hy
    exact hyW
  · simp at h

/-- What dealOk says, as a proposition: by recursion, as the frame cuts. -/
def Dealt (p : P12) : ℕ → Fmt.M1.Stage → List Fmt.M1.Stage → Laid → Prop
  | j, _, [], l => j ≠ 0 ∧ (∃ o, OneAt p j (l.map (·.1)) o) ∧ l.length = 2
  | j, cur, nxt :: rest, l =>
    nOpen (cutF l cur.k) = 0 ∧ (j ≠ 0 → ∃ o, OneAt p j (cutS l cur.k) o) ∧
      Dealt p (j + 1) nxt rest (l.drop (cur.k + 3))

theorem ok_append (a b : Clauses) : ok (a ++ b) = true ↔ ok a = true ∧ ok b = true := by
  unfold ok
  rw [List.all_append, Bool.and_eq_true]

theorem ok_tagJ (j : ℕ) (l : Clauses) : ok (tagJ j l) = ok l := by
  unfold ok tagJ
  rw [List.all_map]
  rfl

theorem dealt_of_walk (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid), ok (dealWalk p 0 j cur rest l) = true → Dealt p j cur rest l
  | [], j, cur, l, h => by
    unfold dealWalk at h
    rw [ok_append, ok_tagJ] at h
    obtain ⟨h1, h2⟩ := h
    by_cases e : j = 0
    · subst e
      simp [ok] at h1
    · have hj : (j == 0) = false := by simpa using e
      rw [hj] at h1
      refine ⟨e, oneAt_of_ok p j _ h1, ?_⟩
      simpa [ok] using h2
  | nxt :: rest, j, cur, l, h => by
    unfold dealWalk at h
    dsimp only at h
    rw [ok_append, ok_tagJ, ok_append] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨?_, fun e => ?_, dealt_of_walk p rest (j + 1) nxt _ h3⟩
    · rw [← nOpenB_eq]
      have h1' : (nOpenB ((l.take (1 + cur.k)).map (·.1)) == 0) = true := by
        unfold ok at h1
        simpa only [List.all_cons, List.all_nil, Bool.and_true] using h1
      exact beq_iff_eq.1 h1'
    · have hj : (j == 0) = false := by simpa using e
      rw [hj] at h2
      exact oneAt_of_ok p j _ h2

/-- dealOk p = true gives Dealt along the place's own laid rounds. -/
theorem dealt_of_ok (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (h : dealOk p = true) : Dealt p 0 a rest (laidS p) := by
  unfold dealOk dealOn at h
  rw [hs] at h
  exact dealt_of_walk p rest 0 a _ h

end H2K.First
