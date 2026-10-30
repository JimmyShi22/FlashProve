-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstAvg.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): averages over fresh hids at a list of queries (`avgH`,
Rom/StateFirstHitDef.lean). hid is the second block of a state.

  `avgH_mono`, `avgH_congr`
                Only tables T' with `SimH C H T T'` (T' is T but for the hids at the queries of H)
                matter.
  `avgH_set`    A write outside H commutes with the average.
  `avgH_extract`
                One query of H may be averaged first.

Also lemmas on tables, `setHid`, `agH`, `SimH`.

Notation:
  `PtS S` (Rom/StateFirstHitDef.lean): a query to a family: an oracle and an input
  `avgH C H F T` (Rom/StateFirstHitDef.lean): the average over fresh uniform hids at the queries of
      a list; H: a list of queries (`PtS S`); F: a function from tables to `ℝ≥0∞`; T, T': tables
      (`Table S`)
  `setHid` (Rom/StateFirstHitDef.lean): the answer with another last block (hid)
  `Table.reHid` (Rom/StateFirstHitDef.lean): the table with another hid at one query
  `C`: for each oracle o of S, a `Link lam (S.Rng o)` (Rom/StateFirst.lean): how an oracle with
      answers in R is treated (`plain` or `chain K e`)
  `Table S` (Rom/OSpec.lean): a partial table: what lazy sampling has fixed so far
-/
import Rom.StateFirstHitDef

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

theorem Table.set_ne {S : OSpec} (T : Table S) {o o' : S.ι} {q : S.Dom o} {q' : S.Dom o'}
    (h : (⟨o', q'⟩ : PtS S) ≠ ⟨o, q⟩) (r : S.Rng o) :
    (T.set o q r) o' q' = T o' q' := by
  by_cases ho : o' = o
  · subst ho
    exact Table.set_ne_point T o' (fun e => h (by rw [e])) r
  · rw [Table.set_ne_oracle T ho]

theorem Table.set_comm {S : OSpec} (T : Table S) {o o' : S.ι} {q : S.Dom o} {q' : S.Dom o'}
    (h : (⟨o', q'⟩ : PtS S) ≠ ⟨o, q⟩) (r : S.Rng o) (r' : S.Rng o') :
    (T.set o q r).set o' q' r' = (T.set o' q' r').set o q r := by
  funext o'' q''
  by_cases a : (⟨o'', q''⟩ : PtS S) = ⟨o, q⟩
  · cases a
    rw [Table.set_ne _ (Ne.symm h), Table.set_self, Table.set_self]
  · by_cases b : (⟨o'', q''⟩ : PtS S) = ⟨o', q'⟩
    · cases b
      rw [Table.set_self, Table.set_ne _ h, Table.set_self]
    · rw [Table.set_ne _ b, Table.set_ne _ a, Table.set_ne _ a, Table.set_ne _ b]

namespace Link
variable {lam : ℕ} {R : Type} (c : Link lam R)

theorem agH_refl (r : R) : c.agH r r := by cases c <;> simp [agH]
theorem agH_symm {r r' : R} (h : c.agH r r') : c.agH r' r := by
  cases c with
  | plain => exact Eq.symm h
  | chain K e => exact ⟨h.1.symm, h.2.symm⟩
theorem agH_trans {r r' r'' : R} (h : c.agH r r') (h' : c.agH r' r'') : c.agH r r'' := by
  cases c with
  | plain => exact Eq.trans h h'
  | chain K e => exact ⟨h.1.trans h'.1, h.2.trans h'.2⟩
theorem agH_setHid (r : R) (u : Dg lam) : c.agH r (c.setHid r u) := by
  cases c with
  | plain => rfl
  | chain K e =>
    show (e r).1 = (e (e.symm ((e r).1, (e r).2.1, u))).1 ∧
      (e r).2.1 = (e (e.symm ((e r).1, (e r).2.1, u))).2.1
    rw [Equiv.apply_symm_apply]
    exact ⟨rfl, rfl⟩
theorem setHid_setHid (r : R) (u u' : Dg lam) : c.setHid (c.setHid r u) u' = c.setHid r u' := by
  cases c with
  | plain => rfl
  | chain K e =>
    show e.symm
        ((e (e.symm ((e r).1, (e r).2.1, u))).1, (e (e.symm ((e r).1, (e r).2.1, u))).2.1, u') = _
    rw [Equiv.apply_symm_apply]
    rfl
/-- the state after a new hid u: u is its second block, so at most one hid gives a given state -/
theorem stateOf_setHid {r : R} {u : Dg lam} {σ : Dg lam × Dg lam}
    (h : c.stateOf (c.setHid r u) = some σ) : u = σ.2 := by
  cases c with
  | plain => cases h
  | chain K e =>
    have h' : some (e (e.symm ((e r).1, (e r).2.1, u))).2 = some σ := h
    rw [Equiv.apply_symm_apply] at h'
    rw [← Option.some.inj h']

end Link

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))

theorem reHid_some {T : Table S} {h : PtS S} {r : S.Rng h.1}
    (hT : T h.1 h.2 = some r) (u : Dg lam) :
    Table.reHid C T h u = T.set h.1 h.2 ((C h.1).setHid r u) := by
  unfold Table.reHid
  rw [hT]

theorem reHid_none {T : Table S} {h : PtS S} (hT : T h.1 h.2 = none) (u : Dg lam) :
    Table.reHid C T h u = T := by
  unfold Table.reHid
  rw [hT]

theorem reHid_ne (T : Table S) (h : PtS S) (u : Dg lam) {o : S.ι}
    {q : S.Dom o} (hne : (⟨o, q⟩ : PtS S) ≠ h) :
    (Table.reHid C T h u) o q = T o q := by
  cases hT : T h.1 h.2 with
  | none => rw [reHid_none C hT]
  | some r =>
    rw [reHid_some C hT]
    exact Table.set_ne T hne _

theorem reHid_at (T : Table S) (h : PtS S) (u : Dg lam) :
    (Table.reHid C T h u) h.1 h.2 = (T h.1 h.2).map fun r => (C h.1).setHid r u := by
  cases hT : T h.1 h.2 with
  | none => rw [reHid_none C hT, hT]; rfl
  | some r => rw [reHid_some C hT, Table.set_self]; rfl

theorem reHid_comm (T : Table S) {h h' : PtS S} (hne : h' ≠ h) (u u' : Dg lam) :
    Table.reHid C (Table.reHid C T h u) h' u' = Table.reHid C (Table.reHid C T h' u') h u := by
  have e1 : (Table.reHid C T h u) h'.1 h'.2 = T h'.1 h'.2 := reHid_ne C T h u hne
  have e2 : (Table.reHid C T h' u') h.1 h.2 = T h.1 h.2 := reHid_ne C T h' u' (Ne.symm hne)
  cases hT : T h.1 h.2 with
  | none =>
    rw [reHid_none C hT, reHid_none C (e2.trans hT)]
  | some r =>
    cases hT' : T h'.1 h'.2 with
    | none => rw [reHid_none C (e1.trans hT'), reHid_none C hT']
    | some r' =>
      rw [reHid_some C (e1.trans hT'), reHid_some C (e2.trans hT),
        reHid_some C hT, reHid_some C hT']
      exact Table.set_comm T hne _ _

theorem reHid_set (T : Table S) (h : PtS S) (u : Dg lam) {o : S.ι} {q : S.Dom o}
    (hne : (⟨o, q⟩ : PtS S) ≠ h) (r : S.Rng o) :
    (Table.reHid C T h u).set o q r = Table.reHid C (T.set o q r) h u := by
  have e1 : (T.set o q r) h.1 h.2 = T h.1 h.2 := Table.set_ne T (Ne.symm hne) r
  cases hT : T h.1 h.2 with
  | none => rw [reHid_none C hT, reHid_none C (e1.trans hT)]
  | some r' =>
    rw [reHid_some C hT, reHid_some C (e1.trans hT)]
    exact Table.set_comm T hne _ _

/-- T' is T but for the hids at the queries of H. -/
def SimH (H : List (PtS S)) (T T' : Table S) : Prop :=
  ∀ o q, ((⟨o, q⟩ : PtS S) ∉ H → T' o q = T o q) ∧ Option.Rel (C o).agH (T o q) (T' o q)

theorem optRel_refl (o : S.ι) (x : Option (S.Rng o)) : Option.Rel (C o).agH x x := by
  cases x with
  | none => exact .none
  | some r => exact .some ((C o).agH_refl r)

theorem simH_refl (H : List (PtS S)) (T : Table S) : SimH C H T T := fun o _ =>
  ⟨fun _ => rfl, optRel_refl C o _⟩

theorem simH_cons {H : List (PtS S)} {T T' : Table S} {h : PtS S} {u : Dg lam}
    (hs : SimH C H (Table.reHid C T h u) T') :
    SimH C (h :: H) T T' := fun o q => by
  obtain ⟨h1, h2⟩ := hs o q
  by_cases e : (⟨o, q⟩ : PtS S) = h
  · subst e
    refine ⟨fun hn => absurd List.mem_cons_self hn, ?_⟩
    have e3 := reHid_at C T ⟨o, q⟩ u
    simp only at e3
    rw [e3] at h2
    cases hT : T o q with
    | none =>
      rw [hT] at h2
      exact h2
    | some r =>
      rw [hT] at h2
      cases hT' : T' o q with
      | none => rw [hT'] at h2; cases h2
      | some r' =>
        rw [hT'] at h2
        cases h2 with
        | some hab => exact .some ((C o).agH_trans ((C o).agH_setHid r u) hab)
  · rw [reHid_ne C T h u e] at h1 h2
    exact ⟨fun hn => h1 fun hm => hn (List.mem_cons_of_mem _ hm), h2⟩

variable {C}

theorem SimH.none {H : List (PtS S)} {T T' : Table S} (hs : SimH C H T T') {o : S.ι}
    {q : S.Dom o} (h : T o q = none) : T' o q = none := by
  have := (hs o q).2
  rw [h] at this
  cases hT' : T' o q with
  | none => rfl
  | some r' => rw [hT'] at this; cases this

theorem SimH.some {H : List (PtS S)} {T T' : Table S} (hs : SimH C H T T') {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : T o q = some r) :
    ∃ r', T' o q = some r' ∧ (C o).agH r r' := by
  have := (hs o q).2
  rw [h] at this
  cases hT' : T' o q with
  | none => rw [hT'] at this; cases this
  | some r' =>
    rw [hT'] at this
    cases this with
    | some hab => exact ⟨r', rfl, hab⟩

variable (C)

theorem avgH_mono :
    ∀ (H : List (PtS S)) {F G : Table S → ℝ≥0∞} (T : Table S),
      (∀ T', SimH C H T T' → F T' ≤ G T') → avgH C H F T ≤ avgH C H G T
  | [], _, _, T, h => h T (simH_refl C [] T)
  | _ :: H, _, _, _, h => expect_mono _ fun _ => avgH_mono H _ fun T' hs => h T' (simH_cons C hs)

theorem avgH_congr (H : List (PtS S)) {F G : Table S → ℝ≥0∞} (T : Table S)
    (h : ∀ T', SimH C H T T' → F T' = G T') : avgH C H F T = avgH C H G T :=
  le_antisymm (avgH_mono C H T fun T' hs => le_of_eq (h T' hs))
    (avgH_mono C H T fun T' hs => le_of_eq (h T' hs).symm)

theorem avgH_const : ∀ (H : List (PtS S)) (x : ℝ≥0∞) (T : Table S), avgH C H (fun _ => x) T = x
  | [], _, _ => rfl
  | h :: H, x, T => by
    show expect (unif (Dg lam)) (fun u => avgH C H (fun _ => x) (Table.reHid C T h u)) = x
    rw [expect_congr _ (G := fun _ => x) fun u => avgH_const H x _, expect_const]

theorem avgH_add :
    ∀ (H : List (PtS S)) (F G : Table S → ℝ≥0∞) (T : Table S),
      avgH C H (fun T' => F T' + G T') T = avgH C H F T + avgH C H G T
  | [], _, _, _ => rfl
  | h :: H, F, G, T => by
    show expect (unif (Dg lam)) (fun u => avgH C H (fun T' => F T' + G T') (Table.reHid C T h u)) =
      expect _ _ + expect _ _
    rw [expect_congr _ fun u => avgH_add H F G _, expect_add]

theorem avgH_expect {γ : Type} (p : PMF γ) :
    ∀ (H : List (PtS S)) (F : γ → Table S → ℝ≥0∞) (T : Table S),
      avgH C H (fun T' => expect p fun x => F x T') T = expect p fun x => avgH C H (F x) T
  | [], _, _ => rfl
  | h :: H, F, T => by
    show expect (unif (Dg lam))
        (fun u => avgH C H (fun T' => expect p fun x => F x T') (Table.reHid C T h u)) =
      expect p fun x => expect (unif (Dg lam)) fun u => avgH C H (F x) (Table.reHid C T h u)
    rw [expect_congr _ fun u => avgH_expect p H F _, expect_comm]

theorem avgH_set :
    ∀ (H : List (PtS S)) (F : Table S → ℝ≥0∞) (T : Table S) {o : S.ι} {q : S.Dom o}
        (_ : (⟨o, q⟩ : PtS S) ∉ H) (r : S.Rng o),
      avgH C H (fun T' => F (T'.set o q r)) T = avgH C H F (T.set o q r)
  | [], _, _, _, _, _, _ => rfl
  | h :: H, F, T, o, q, hn, r => by
    show expect (unif (Dg lam))
        (fun u => avgH C H (fun T' => F (T'.set o q r)) (Table.reHid C T h u)) =
      expect (unif (Dg lam)) fun u => avgH C H F (Table.reHid C (T.set o q r) h u)
    refine expect_congr _ fun u => ?_
    rw [avgH_set H F _ (fun hm => hn (List.mem_cons_of_mem _ hm)) r,
      reHid_set C T h u (fun e => hn (e ▸ List.mem_cons_self))]

open Classical in
theorem avgH_extract :
    ∀ (H : List (PtS S)) (F : Table S → ℝ≥0∞) (T : Table S) (h : PtS S), h ∈ H →
      avgH C H F T = expect (unif (Dg lam)) fun u => avgH C (H.erase h) F (Table.reHid C T h u)
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | h' :: H, F, T, h, hm => by
    by_cases e : h' = h
    · subst e
      rw [List.erase_cons_head]
      rfl
    · have hm' : h ∈ H := (List.mem_cons.mp hm).resolve_left (Ne.symm e)
      rw [List.erase_cons_tail (by simpa using e)]
      show expect (unif (Dg lam)) (fun u' => avgH C H F (Table.reHid C T h' u')) =
        expect (unif (Dg lam)) fun u =>
          expect (unif (Dg lam)) fun u' =>
            avgH C (H.erase h) F (Table.reHid C (Table.reHid C T h u) h' u')
      rw [expect_congr _ fun u' => avgH_extract H F _ h hm', expect_comm]
      refine expect_congr _ fun u => expect_congr _ fun u' => ?_
      rw [reHid_comm C T (Ne.symm e) u' u]

/-- A uniform answer with a fresh uniform hid is a uniform answer (R nonempty). -/
theorem unif_setHid {R : Type} [Fintype R] [Nonempty R] (c : Link lam R) (G : R → ℝ≥0∞) :
    (expect (unif R) fun r => expect (unif (Dg lam)) fun u => G (c.setHid r u)) =
      expect (unif R) G := by
  cases c with
  | plain =>
    refine expect_congr _ fun r => ?_
    exact expect_const (unif (Dg lam)) (G r)
  | chain K e =>
    have hR : unif R = (unif ((Fin K → Dg lam) × Dg lam × Dg lam)).map e.symm :=
      (map_unif_equiv e.symm).symm
    rw [hR, expect_map, expect_map, unif_prod, unif_prod, expect_prod, expect_prod]
    refine expect_congr _ fun bl => ?_
    rw [expect_prod, expect_prod]
    refine expect_congr _ fun t => ?_
    have : ∀ u0 : Dg lam,
        (expect (unif (Dg lam)) fun u => G ((Link.chain K e).setHid (e.symm (bl, t, u0)) u)) =
          expect (unif (Dg lam)) fun u => G (e.symm (bl, t, u)) := fun u0 => by
      refine expect_congr _ fun u => ?_
      show G (e.symm ((e (e.symm (bl, t, u0))).1, (e (e.symm (bl, t, u0))).2.1, u)) = _
      rw [Equiv.apply_symm_apply]
    rw [expect_congr _ this, expect_const]

end Rom
