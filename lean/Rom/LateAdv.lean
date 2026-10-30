-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/LateAdv.lean: a program of the language `LStep` (Rom/DeferLate.lean) as an adversary.

A reduction (for instance that of Compile/Batch/PubWr.lean) between an adversary and a challenger
(`World`, Rom/World.lean) keeps the state `LSt` of the experiment itself; its table holds every
answer that it has given or programmed. `LStep.toAdv` runs a program in this way, with the coins of
an adversary: a plain evaluation is read from the table or, where the table has no entry, sampled
and stored; marked evaluations and reveals are changes of the state. It makes neither a call nor an
oracle query (`toAdv_quiet`), so the challenger that it faces has no influence:

  `interact_toAdv`  Against any challenger: the result and the new state have the distribution of
                    `LStep.run`, and the challenger's state is unchanged.

Notation:
  `LStep S sp α` (Rom/DeferLate.lean): one step of a challenger that supplies points at the release;
    as `Step` (Rom/Defer.lean), but for marked and reveal
  `.fresh ℓ k`: `ℓ : ℕ`, `k : Tok → LStep S sp α`; `.marked o t us A hA k`: `t : Tok`,
    `us : List Tok`, `A : Finset (S.Rng o)`, `hA : A.Nonempty`, `k : sp.Vis o → Tok → LStep S sp α`;
    `.reveal ts pts k`: `ts : List Tok`, `pts : Tok → ∀ o, Option (Clo S o)`,
    `k : List Bits → LStep S sp α`
  `LSt S` (Rom/DeferLate.lean): the state of the experiment beside the challenger's own: the fields
    `table`, `vals`, `shown`, `evs`; `d.val t`: `d.vals.getD t []`
  `LEv S` (Rom/DeferLate.lean): the record of one marked evaluation, without its point: the fields
    `o`, `ans`, `charged`, `others`, `tail`, `released`, in this order (so `false` in `LStep.toAdv`
    is `released`)
-/
import Rom.DeferLate
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom

variable {S : OSpec} {sp : Split S} {Out In α : Type}

/-! ## Uniform samples by the coins of an adversary -/

/-- an enumeration of a finite non-empty type, in the form in which `Adv.sample` samples -/
def finEnum (β : Type) [Fintype β] [Nonempty β] : Fin (Fintype.card β - 1 + 1) ≃ β :=
  (finCongr (by have := Fintype.card_pos (α := β); omega)).trans (Fintype.equivFin β).symm

theorem unif_enum_bind {γ : Type} (β : Type) [Fintype β] [Nonempty β] (F : β → PMF γ) :
    ((PMF.uniformOfFintype (Fin (Fintype.card β - 1 + 1))).bind fun r => F (finEnum β r))
      = (PMF.uniformOfFintype β).bind F := by
  have h := map_unif_equiv (finEnum β)
  rw [show PMF.uniformOfFintype β = unif β from rfl, ← h, PMF.bind_map]
  rfl

theorem uniformOfFinset_eq_map {β : Type} (A : Finset β) (hA : A.Nonempty) :
    haveI := hA.to_subtype
    PMF.uniformOfFinset A hA = (PMF.uniformOfFintype A).map Subtype.val := by
  classical
  haveI := hA.to_subtype
  ext a
  rw [PMF.uniformOfFinset_apply, PMF.map_apply, tsum_fintype]
  by_cases ha : a ∈ A
  · rw [if_pos ha, Finset.sum_eq_single (⟨a, ha⟩ : A)]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (Subtype.ext h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg ha]
    exact (Finset.sum_eq_zero fun b _ => if_neg fun h : a = b.val => ha (by rw [h]; exact b.2)).symm

/-! ## The interpreter -/

/-- The program as an adversary, from the state d; it ends with the result and the new state. -/
def LStep.toAdv : LStep S sp α → LSt S → Adv S Out In (α × LSt S)
  | .pure a, d => .halt (a, d)
  | .sample n k, d => .sample n fun r => (k r).toAdv d
  | .plain o q k, d =>
      match d.table o q with
      | some r => (k r).toAdv d
      | none => .sample (Fintype.card (S.Rng o) - 1) fun r =>
          (k (finEnum (S.Rng o) r)).toAdv { d with table := d.table.set o q (finEnum (S.Rng o) r) }
  | .fresh ℓ k, d => .sample (Fintype.card (Fin ℓ → Bool) - 1) fun r =>
      (k d.vals.length).toAdv { d with vals := d.vals ++ [List.ofFn (finEnum (Fin ℓ → Bool) r)] }
  | .marked o t us A hA k, d =>
      haveI := hA.to_subtype
      .sample (Fintype.card A - 1) fun r =>
        (k (sp.split o (finEnum A r).val).1 d.vals.length).toAdv
          { d with vals := d.vals ++ [List.ofFn (sp.split o (finEnum A r).val).2],
                   evs := d.evs ++ [⟨o, (finEnum A r).val, t, us, d.vals.length, false⟩] }
  | .reveal ts pts k, d =>
      (k (ts.map d.val)).toAdv
        { d with
          table := (lrelease pts d.val (d.shown ++ ts) d.evs d.table).2, shown := d.shown ++ ts,
          evs := (lrelease pts d.val (d.shown ++ ts) d.evs d.table).1 }

theorem toAdv_plain_some {o : S.ι} {q : S.Dom o} (k : S.Rng o → LStep S sp α) {d : LSt S}
    {r : S.Rng o} (h : d.table o q = some r) :
    (LStep.plain o q k).toAdv (Out := Out) (In := In) d = (k r).toAdv d := by
  simp only [LStep.toAdv, h]

theorem toAdv_plain_none {o : S.ι} {q : S.Dom o} (k : S.Rng o → LStep S sp α)
    {d : LSt S} (h : d.table o q = none) :
    (LStep.plain o q k).toAdv (Out := Out) (In := In) d =
      .sample (Fintype.card (S.Rng o) - 1) fun r =>
          (k (finEnum (S.Rng o) r)).toAdv
              { d with table := d.table.set o q (finEnum (S.Rng o) r) } := by
  simp only [LStep.toAdv, h]

/-- the adversary makes neither a call nor an oracle query -/
def Adv.Quiet : Adv S Out In α → Prop
  | .halt _ => True
  | .sample _ k => ∀ r, (k r).Quiet
  | .query _ _ _ => False
  | .call _ _ => False

theorem toAdv_quiet (Q : LStep S sp α) :
    ∀ d : LSt S, (Q.toAdv (Out := Out) (In := In) d).Quiet := by
  induction Q with
  | pure a => intro d; trivial
  | sample n k ih => intro d r; exact ih r d
  | plain o q k ih =>
    intro d
    cases h : d.table o q with
    | some r => rw [toAdv_plain_some k h]; exact ih r d
    | none => rw [toAdv_plain_none k h]; exact fun r => ih _ _
  | fresh ℓ k ih => intro d r; exact ih _ _
  | marked o t us A hA k ih => intro d r; exact ih _ _ _
  | reveal ts pts k ih => intro d; exact ih _ _

theorem lazyAnswer_of_some {T : Table S} {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : T o q = some r) :
    lazyAnswer T o q = PMF.pure (r, T) := by
  simp [lazyAnswer, h]

theorem lazyAnswer_of_none {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) :
    lazyAnswer T o q = (PMF.uniformOfFintype (S.Rng o)).map fun r => (r, T.set o q r) := by
  simp [lazyAnswer, h]

/-- The interpreter is faithful, against any challenger. -/
theorem interact_toAdv (G : World S Out In) (Q : LStep S sp α) :
    ∀ (d : LSt S) (g : G.σ), interact G (Q.toAdv d) g = (Q.run d).map fun y => (y, g) := by
  induction Q with
  | pure a => intro d g; simp only [LStep.toAdv, interact, LStep.run, PMF.pure_map]
  | sample n k ih =>
    intro d g
    simp only [LStep.toAdv, interact, LStep.run, PMF.map_bind, ih]
  | plain o q k ih =>
    intro d g
    cases hd : d.table o q with
    | some r =>
      rw [toAdv_plain_some k hd, LStep.run, lazyAnswer_of_some hd, PMF.pure_bind]
      exact ih r d g
    | none =>
      rw [toAdv_plain_none k hd, interact, LStep.run, lazyAnswer_of_none hd, PMF.bind_map,
        PMF.map_bind, ← unif_enum_bind (S.Rng o)]
      exact congrArg _ (funext fun r => ih _ _ g)
  | fresh ℓ k ih =>
    intro d g
    simp only [LStep.toAdv, interact, LStep.run, PMF.map_bind]
    rw [← unif_enum_bind (Fin ℓ → Bool)]
    exact congrArg _ (funext fun r => ih _ _ g)
  | marked o t us A hA k ih =>
    intro d g
    haveI := hA.to_subtype
    simp only [LStep.toAdv, interact, LStep.run, PMF.map_bind]
    rw [uniformOfFinset_eq_map A hA, PMF.bind_map, ← unif_enum_bind A]
    exact congrArg _ (funext fun r => ih _ _ _ g)
  | reveal ts pts k ih =>
    intro d g
    simp only [LStep.toAdv, LStep.run]
    exact ih _ _ g

/-! ## Tables -/

/-- every entry of T is an entry of T' -/
def Table.Sub (T T' : Table S) : Prop := ∀ o q r, T o q = some r → T' o q = some r

theorem Table.Sub.refl (T : Table S) : T.Sub T := fun _ _ _ h => h

theorem Table.Sub.trans {T T' T'' : Table S} (h : T.Sub T') (h' : T'.Sub T'') : T.Sub T'' :=
  fun o q r hr => h' o q r (h o q r hr)

theorem Table.set_apply_same (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    (T.set o q r) o q = some r := by
  simp [Table.set]

theorem Table.set_apply_of_some {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none)
    (r : S.Rng o) {o' : S.ι} {q' : S.Dom o'} {r' : S.Rng o'} (h' : T o' q' = some r') :
    (T.set o q r) o' q' = some r' := by
  unfold Table.set
  by_cases ho : o' = o
  · subst ho
    rw [Function.update_self]
    by_cases hq : q' = q
    · subst hq; rw [h] at h'; exact absurd h' (by simp)
    · rw [Function.update_of_ne hq]; exact h'
  · rw [Function.update_of_ne ho]; exact h'

theorem Table.sub_set {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) (r : S.Rng o) :
    T.Sub (T.set o q r) :=
  fun _ _ _ h' => Table.set_apply_of_some h r h'

theorem lwrite_sub (pts : Tok → ∀ o : S.ι, Option (Clo S o)) (val : Tok → Bits)
    (T : Table S) (e : LEv S) : T.Sub (lwrite pts val T e) := by
  unfold lwrite
  cases pts e.charged e.o with
  | none => exact Table.Sub.refl T
  | some pt =>
    cases h : T e.o (pt (val e.charged) (e.others.map val)) with
    | none => simp only [h]; exact Table.sub_set h _
    | some r => simp only [h]; exact Table.Sub.refl T

theorem lrelease_sub (pts : Tok → ∀ o : S.ι, Option (Clo S o))
    (val : Tok → Bits) (shown : List Tok) :
    ∀ (evs : List (LEv S)) (T : Table S), T.Sub (lrelease pts val shown evs T).2 := by
  intro evs
  induction evs with
  | nil => intro T; exact Table.Sub.refl T
  | cons e es ih =>
    intro T
    rw [lrelease]
    split
    · exact (lwrite_sub pts val T e).trans (ih _)
    · exact ih T

/-- The table only grows along a run. -/
theorem run_table_mono (Q : LStep S sp α) :
    ∀ (d : LSt S), ∀ y ∈ (Q.run d).support, d.table.Sub y.2.table := by
  induction Q with
  | pure a =>
    intro d y hy
    rw [LStep.run, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact Table.Sub.refl _
  | sample n k ih =>
    intro d y hy
    rw [LStep.run] at hy
    obtain ⟨r, _, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    exact ih r d y hy
  | plain o q k ih =>
    intro d y hy
    rw [LStep.run] at hy
    obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    have h1 := ih _ _ y hy
    refine Table.Sub.trans ?_ h1
    cases hd : d.table o q with
    | some r =>
      rw [lazyAnswer_of_some hd, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Table.Sub.refl _
    | none =>
      rw [lazyAnswer_of_none hd] at hz
      obtain ⟨r, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      exact Table.sub_set hd r
  | fresh ℓ k ih =>
    intro d y hy
    rw [LStep.run] at hy
    obtain ⟨r, _, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    have h1 := ih _ _ y hy
    exact h1
  | marked o t us A hA k ih =>
    intro d y hy
    rw [LStep.run] at hy
    obtain ⟨r, _, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    have h1 := ih _ _ _ y hy
    exact h1
  | reveal ts pts k ih =>
    intro d y hy
    rw [LStep.run] at hy
    have h1 := ih _ _ y hy
    exact (lrelease_sub pts d.val (d.shown ++ ts) d.evs d.table).trans h1

end Rom
