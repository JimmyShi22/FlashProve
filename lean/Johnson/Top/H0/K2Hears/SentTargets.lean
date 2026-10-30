-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/SentTargets.lean: the code switch: WHICH ANSWER IS A STORED SAMPLE
ROW's TARGET.

SentRows.lean says which rows a yes of the sending lays, «with some element as its target». Here:
which.
  rowsFor_targets   the ground's rowsFor takes the answers in their order: row number j's target is
                    answer number j, and the answers left are those behind
  offOf, offOf_ones  how many answers the messages in front of number k take
  loop_targets      the ground's loop: the k-th message's row number j has as its target answer
                    number offOf k + j
  filter_prefix     a filter leaves a first stretch as it is, if all of it passes
  loop_first        the heart: the loop over a filtered list of numbers whose first N pass, are n0,
                    n0 + 1, … and have one answer each
  SentTargets       what stands behind a sending whose first L notices have one answer each: there
                    are answers an, read by the ground's answersOf off round 2's first items, such
                    that for new message number i < L the target of its stored row number 0, IF
                    THERE IS ONE, is an[i], IF THERE IS ONE: an equation of two options
                    ((rows[0]?).map (·.target) = an[i]?), which also holds with no row and no
                    answer. That there is a row is SentRows.lean's sent_rows; AnsBehind.lean joins
                    the two
  sendP_targets1, sendOpen_targets1, sent_targets  of the plain ground's sendP, of Send.sendOpen, of
                    the sending that K2 runs: NO PREMISE BUT THE YES and «the first L notices have
                    one answer each»
No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.SentRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model Desc.Plain VerifiableInference.Desc.Ground

theorem rowsFor_targets (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed) :
    ∀ (is : List Nat) (ys : List E) (acc rows : Array OnBytes.Row) (ys' : List E),
      rowsFor codes s o seeds is ys acc = some (rows, ys') →
      ys' = ys.drop is.length ∧
      ∀ j, j < is.length → (rows[acc.size + j]?).map (·.target) = ys[j]?
  | [], ys, acc, rows, ys', h => by
    simp only [rowsFor, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | i :: is, [], acc, rows, ys', h => by simp [rowsFor] at h
  | i :: is, y :: ys, acc, rows, ys', h => by
    unfold rowsFor at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i row _
        obtain ⟨-, h2, -⟩ := rowsFor_spec codes s o seeds is ys _ rows ys' h
        obtain ⟨e1, e3⟩ := rowsFor_targets codes s o seeds is ys _ rows ys' h
        rw [Array.size_push] at h2 e3
        refine ⟨by rw [e1]; rfl, fun j hj => ?_⟩
        cases j with
        | zero =>
          rw [Nat.add_zero, h2 acc.size (by omega), Array.getElem?_push_size]
          rfl
        | succ j =>
          have := e3 j (by simpa using hj)
          rw [List.getElem?_cons_succ, ← this]
          congr 2
          omega

/-- How many answers the messages in front of number k take. -/
def offOf (l : List (Nat × OracleShape)) (k : Nat) : Nat := ((l.take k).map (·.2.answers)).sum

/-- **The k-th message's row number j has answer number offOf k + j as its target.** -/
theorem loop_targets {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      Fmt.increasing (l.map (·.1)) = true →
      sampleLoop groundG p codes seeds l ys d = some (d', left) →
      ∀ k (hk : k < l.length), ∃ rows,
        (d'.st.oracles[l[k].1]?).map (·.sampleRows) = some rows ∧
        ∀ j, j < l[k].2.answers → (rows[j]?).map (·.target) = ys[offOf l k + j]?
  | [], ys, d, d', left, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | (o, s) :: l, ys, d, d', left, hi, h, k, hk => by
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i rows ys' hr
      split at h
      · cases h
      · rename_i d1 h1
        have hi' : Fmt.increasing (o :: l.map (·.1)) = true := hi
        obtain ⟨ha, -⟩ := admit_rows (show admitP d o rows = some d1 from h1)
        obtain ⟨-, hd⟩ := loop_rows p codes seeds l ys' d1 d' left (incr_tail _ _ hi') h
        obtain ⟨e1, e3⟩ := rowsFor_targets codes s o seeds _ ys #[] rows ys' hr
        cases k with
        | zero =>
          refine ⟨rows, ?_, fun j hj => ?_⟩
          · show (d'.st.oracles[o]?).map (·.sampleRows) = some rows
            rw [hd o fun z hz => Nat.ne_of_gt (incr_lt _ _ hi' z.1 (List.mem_map_of_mem hz))]
            exact ha
          · have := e3 j (by simpa using hj)
            simpa [offOf] using this
        | succ k =>
          obtain ⟨rws, g1, g2⟩ :=
              loop_targets p codes seeds l ys' d1 d' left (incr_tail _ _ hi') h k
            (by simpa using hk)
          refine ⟨rws, g1, fun j hj => ?_⟩
          have := g2 j hj
          rw [this, e1, List.getElem?_drop]
          congr 1
          simp [offOf]
          omega

theorem filter_prefix {α : Type} (P : α → Bool) : ∀ (l : List α) (n : Nat),
    (∀ x ∈ l.take n, P x = true) → (l.filter P).take n = l.take n
  | [], n, _ => by simp
  | a :: l, 0, _ => by simp
  | a :: l, n + 1, h => by
    have ha : P a = true := h a (by simp)
    rw [List.filter_cons_of_pos ha, List.take_succ_cons, List.take_succ_cons,
      filter_prefix P l n fun x hx => h x (by simp [hx])]

theorem offOf_ones (l : List (Nat × OracleShape)) : ∀ k : Nat,
    (∀ m (hm : m < l.length), m < k → l[m].2.answers = 1) → k ≤ l.length → offOf l k = k
  | 0, _, _ => by simp [offOf]
  | k + 1, h, hk => by
    have e := offOf_ones l k (fun m hm hmk => h m hm (by omega)) (by omega)
    unfold offOf at e ⊢
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega : k < l.length)]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    rw [e, h k (by omega) (by omega)]
    rfl

/-- The heart: the loop over a filtered list of numbers whose first N pass, are n0, n0 + 1, … and
have one
answer each. -/
theorem loop_first {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) (S : Statement)
    (ids : List Nat) (P : Nat → Bool) (shapes : List OracleShape) (an : List E) (d₁ d₂ : DState L)
    (left : List E) (n0 N : Nat)
    (hsh : (ids.filter P).mapM (fun o => (S.oracles[o]?).map (·.shape)) = some shapes)
    (hinc : Fmt.increasing (ids.filter P) = true)
    (h2 : sampleLoop groundG p codes seeds ((ids.filter P).zip shapes) an d₁ = some (d₂, left))
    (hid : ∀ i, i < N → ids[i]? = some (n0 + i)) (hP : ∀ i, i < N → P (n0 + i) = true)
    (hs1 : ∀ i, i < N → ∃ x, S.oracles[n0 + i]? = some x ∧ x.shape.answers = 1) :
    ∀ i, i < N → ∃ rows, (d₂.st.oracles[n0 + i]?).map (·.sampleRows) = some rows ∧
      (rows[0]?).map (·.target) = an[i]? := by
  have hpre : (ids.filter P).take N = ids.take N := filter_prefix P ids N fun z hz => by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
    by_cases hiN : i < N
    · rw [List.getElem?_take_of_lt hiN, hid i hiN] at hi
      rw [← Option.some.inj hi]
      exact hP i hiN
    · rw [List.getElem?_take_eq_none (by omega)] at hi
      cases hi
  have ht : ∀ i, i < N → (ids.filter P)[i]? = some (n0 + i) := fun i hi => by
    have e := congrArg (·[i]?) hpre
    simp only [List.getElem?_take_of_lt hi] at e
    rw [e, hid i hi]
  obtain ⟨hlen, -⟩ := mapM_zip _ _ _ hsh
  obtain ⟨-, hget⟩ := OnBytes.Slice.list_mapM_inv _ _ _ hsh
  have hl : ∀ i, i < N → ∃ h : i < ((ids.filter P).zip shapes).length,
      ((ids.filter P).zip shapes)[i].1 = n0 + i ∧ ((ids.filter P).zip shapes)[i].2.answers = 1 := by
    intro i hi
    obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.1 (ht i hi)
    have h2' : i < shapes.length := by rw [hlen]; exact h1
    refine ⟨by rw [List.length_zip]; omega, ?_, ?_⟩
    · rw [List.getElem_zip]
      exact e1
    · rw [List.getElem_zip]
      obtain ⟨x, hx, ha⟩ := hs1 i hi
      have g := hget i h1
      rw [e1, hx, List.getElem?_eq_getElem h2'] at g
      rw [← Option.some.inj g]
      exact ha
  intro i hi
  obtain ⟨hi', e1, e2⟩ := hl i hi
  obtain ⟨rows, g1, g2⟩ := loop_targets p codes seeds _ an d₁ d₂ left
    (by rw [List.map_fst_zip (by omega)]; exact hinc) h2 i hi'
  rw [e1] at g1
  refine ⟨rows, g1, ?_⟩
  have g3 := g2 0 (by omega)
  rw [offOf_ones _ i (fun m _ hm => (hl m (by omega)).2.2) (by omega), Nat.add_zero] at g3
  exact g3

/-- **What stands behind a sending whose first L notices have one answer each.** -/
def SentTargets (S : Statement) (r₂ : Fmt.RoundView) (S' : Statement) (L : Nat) : Prop :=
  ∃ (need : Nat) (an : List E), answersOf { r₂ with vals := r₂.vals.take need } = some an ∧
    ∀ i, i < L → ∃ rows, (S'.oracles[S.oracles.size + i]?).map (·.sampleRows) = some rows ∧
      (rows[0]?).map (·.target) = an[i]?

theorem sendP_targets1 {L : Type} {p : GPar} {own : Bool} {d : DState L}
    {sent : Array OracleNotice} {r₁ r₂ : Fmt.RoundView}
    {x : Array Nat × List E × List E × Nat × DState L}
    (h : sendP groundG p own d sent r₁ r₂ = some x) (N : Nat)
    (hN : ∀ i, i < N → ∃ n, sent[i]? = some n ∧ n.shape.answers = 1) :
    SentTargets d.st r₂ x.2.2.2.2.st N := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := optBind h
  dsimp only at h
  obtain ⟨shapes, hsh, h⟩ := optBind h
  obtain ⟨seeds, -, h⟩ := optBind h
  obtain ⟨an, han, h⟩ := optBind h
  split at h
  · rename_i hc
    obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBind h
    dsimp only at h
    split at h
    · cases h
      have hr : recvP p.firstTree d sent = some (ids, d₁) := h1
      unfold recvP at hr
      split at hr
      · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 hr
        cases e
        simp only [Bool.and_eq_true] at hc
        have hinc := hc.1.1.1.1.1.1.1.1.2
        rw [← VerifiableInference.Desc.Own.rising_agrees] at hinc
        have hnew : ∀ i, i < N → ∃ n, sent[i]? = some n ∧ n.shape.answers = 1 ∧
            (OnBytes.Slice.stSent d.st sent).oracles[d.st.oracles.size + i]? =
              some { shape := n.shape } := fun i hi => by
          obtain ⟨n, hn, ha⟩ := hN i hi
          refine ⟨n, hn, ha, ?_⟩
          rw [OnBytes.Slice.stSent_new, hn]
          rfl
        refine ⟨_, an, han, loop_first p _ seeds _ _ _ shapes an _ d₂ left d.st.oracles.size N hsh
          hinc h2 (fun i hi => ?_) (fun i hi => ?_) fun i hi => ?_⟩
        · obtain ⟨n, hn, -, -⟩ := hnew i hi
          have hlt : i < sent.size := by
            by_contra hcon
            rw [Array.getElem?_eq_none (by omega)] at hn
            cases hn
          simp [hlt, Nat.add_comm]
        · obtain ⟨n, -, ha, hx⟩ := hnew i hi
          rw [hx]
          simp [ha]
        · obtain ⟨n, -, ha, hx⟩ := hnew i hi
          exact ⟨_, hx, ha⟩
      · cases hr
    · cases h
  · cases h

theorem sendOpen_targets1 {L : Type} {p : GPar} {owed : Option Nat} {sent : Array OracleNotice}
    {e₁ : Fmt.Entry} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array Nat} {took : Nat}
    (h : VerifiableInference.Desc.First.Send.sendOpen groundG p owed sent e₁ d r₁ r₂ =
      some (ids, took, d')) (N : Nat)
    (hN : ∀ i, i < N → ∃ n, sent[i]? = some n ∧ n.shape.answers = 1) :
    SentTargets d.st r₂ d'.st N := by
  unfold VerifiableInference.Desc.First.Send.sendOpen at h
  split at h
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact sendP_targets1 hx N hN
  · cases h

attribute [local irreducible] SentTargets

/-- **The sending that K2 runs.** -/
theorem sent_targets {P : _root_.Tw.K2.Par9} {S : Statement} {B : TreeBook} {roots : Nat}
    {settled : Bool} {notices : Array OracleNotice} {rS rL : Fmt.RoundView} {y : _root_.Tw.K2.Sent}
    (h : _root_.Tw.K2.sendByL8 P S B roots settled notices rS rL = .ok y) (N : Nat)
    (hN : ∀ i, i < N → ∃ n, notices[i]? = some n ∧ n.shape.answers = 1) :
    SentTargets S rL y.st N := by
  unfold _root_.Tw.K2.sendByL8 at h
  split at h
  · rename_i ids took d hd
    cases h
    exact sendOpen_targets1 hd N hN
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sent_targets
#print axioms VerifiableInference.Desc.First.K2.loop_targets
