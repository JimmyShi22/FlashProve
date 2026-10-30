-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecWholeKit.lean: generic lemmas on algorithms that read a random table with independent rows.

Definitions, lemmas and proofs, for Hiop/RecWholeProof.lean. Generic: no protocol occurs here.

Compile/Batch/Life.lean proves "the whole lifetime of the encodings" by seeing adversary and
simulators as one algorithm that reads a table with independent rows, at most b places in each row.
With records a
row has one thing more: the record of its encoded index, which everybody is shown and which the
simulators of runs are handed. Here that is a further place of the row, the free place: it holds a
symbol of another type, and reading it costs nothing, however often.

Main names:
  Places are (row, none) and (row, some q): `Sy`, `tab`, `wd`, `wp`.
  `AddsF c w`: c reads at most w e new word places in row e: `addsF_up` (from Compile/Life.lean's
    `Adds`), `addsF_free` (reading a free place first adds nothing).
  `within_plugF`: under the hypotheses of its statement, an adversary within the budget, with
    sessions that keep to their loads, reads at most b word places in each row (Compile/Life.lean:
    `Play.within_plug`).
  `rows_lawF`: independent rows (`[Nonempty R]`): if the law of (free symbol, any b word places) of
    each row is the same for two families of rows, so is the law of the whole table on every set of
    places with at most b word places in each row (the premise `h` has `T.card ≤ b`)
    (Compile/Life.lean: `rows_law`).
  `lifetimeD`: Compile/Life.lean's `lifetime_abstract` for tables whose symbols have a type that
    depends on the place: the same proof.

Limits: this file says nothing on any protocol, object or experiment.
Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Life

set_option autoImplicit false

noncomputable section

namespace Hiop.Free
open Prob Iop Compile.Lifetime
open scoped ENNReal

variable {ι Q F Sg : Type}

/-- the type of the symbol at a place: F at the free place of a row, Sg at a word place -/
def Sy (ι Q F Sg : Type) : ι × Option Q → Type := fun p => match p.2 with
  | none => F
  | some _ => Sg

/-- a table from its free symbols and its words -/
def tab (a : ι → F) (u : ι → Q → Sg) : ∀ p, Sy ι Q F Sg p
  | (e, none) => a e
  | (e, some q) => u e q

/-- a word place -/
def wd (p : ι × Q) : ι × Option Q := (p.1, some p.2)

theorem wd_inj : Function.Injective (wd : ι × Q → ι × Option Q) := fun p q h => by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have h1 : p1 = q1 := congrArg Prod.fst h
  have h2 : some p2 = some q2 := congrArg Prod.snd h
  rw [h1, Option.some.inj h2]

/-- the word places of a set of places -/
def wp (T : Finset (ι × Option Q)) : Finset (ι × Q) := T.preimage wd wd_inj.injOn

theorem mem_wp {T : Finset (ι × Option Q)} {p : ι × Q} : p ∈ wp T ↔ wd p ∈ T := Finset.mem_preimage

theorem wp_empty : wp (∅ : Finset (ι × Option Q)) = ∅ := Finset.preimage_empty

section Dec
variable [DecidableEq ι] [DecidableEq Q]

theorem wp_insert_wd (p : ι × Q) (T : Finset (ι × Option Q)) :
    wp (insert (wd p) T) = insert p (wp T) := by
  ext q
  rw [mem_wp, Finset.mem_insert, Finset.mem_insert, mem_wp, wd_inj.eq_iff]

theorem wp_insert_free (e : ι) (T : Finset (ι × Option Q)) : wp (insert (e, none) T) = wp T := by
  ext q
  rw [mem_wp, Finset.mem_insert, mem_wp]
  exact ⟨fun h => h.resolve_left fun hh => Option.some_ne_none q.2 (congrArg Prod.snd hh), Or.inr⟩

end Dec

variable {β : Type}

/-- An algorithm that reads a table of words, on a table with free places. -/
def up : Reader (ι × Q) (fun _ => Sg) β → Reader (ι × Option Q) (Sy ι Q F Sg) β
  | .done a => .done a
  | .read p k => .read (wd p) fun x => up (k x)
  | .draw γ d k => .draw γ d fun y => up (k y)

theorem run_up (c : Reader (ι × Q) (fun _ => Sg) β) (f : ∀ p, Sy ι Q F Sg p) :
    (up c).run f = c.run fun p => f (wd p) := by
  induction c with
  | done a => rfl
  | read p k ih => exact ih (f (wd p))
  | draw γ d k ih =>
    show (d.bind fun y => (up (k y)).run f) = d.bind fun y => (k y).run fun p => f (wd p)
    exact congrArg _ (funext ih)

variable [DecidableEq ι] [DecidableEq Q]

theorem within_up {good : Finset (ι × Q) → Prop} (c : Reader (ι × Q) (fun _ => Sg) β)
    (S : Finset (ι × Option Q)) (h : c.Within good (wp S)) :
    (up (F := F) c).Within (fun T => good (wp T)) S := by
  induction c generalizing S with
  | done a => exact h
  | read p k ih =>
    intro x
    refine ih x _ ?_
    rw [wp_insert_wd]
    exact h x
  | draw γ d k ih => exact fun y => ih y S (h y)

/-- The algorithm reads at most w e new word places in row e, whatever answers it receives and
whatever was read before. -/
def AddsF (c : Reader (ι × Option Q) (Sy ι Q F Sg) β) (w : ι → ℕ) : Prop :=
  ∀ S, c.Within (fun T => ∀ e, rowCard (wp T) e ≤ rowCard (wp S) e + w e) S

theorem addsF_up {c : Reader (ι × Q) (fun _ => Sg) β} {w : ι → ℕ} (h : Adds c w) :
    AddsF (up (F := F) c) w :=
  fun S => within_up c S (h (wp S))

/-- Reading a free place first adds nothing. -/
theorem addsF_free (e : ι) {g : F → Reader (ι × Option Q) (Sy ι Q F Sg) β}
    {w : ι → ℕ} (h : ∀ x, AddsF (g x) w) :
    AddsF (.read (e, none) g) w := by
  intro S x
  have h1 := h x (insert (e, none) S)
  rw [wp_insert_free] at h1
  exact h1

variable {C : Type} {A : C → Type} {α : Type}

/-- Under the hypotheses below, an adversary within the budget, together with sessions that keep to
their loads, reads at most b word places in each row. -/
theorem within_plugF {s : ∀ c, Reader (ι × Option Q) (Sy ι Q F Sg) (A c)} {w : C → ι → ℕ} {b : ℕ}
    (hs : ∀ c, AddsF (s c) (w c)) (t : Play C A α) (ld : ι → ℕ) (S : Finset (ι × Option Q))
    (hS : ∀ e, rowCard (wp S) e ≤ ld e) (ht : t.Fits w b ld) :
    (t.plug s).Within (fun T => ∀ e, rowCard (wp T) e ≤ b) S := by
  induction t generalizing ld S with
  | done a => exact fun e => (hS e).trans (ht e)
  | call c k ih =>
    exact Reader.within_bind _ _ S
      (Reader.Within.mono
        (fun T hT a => ih a _ T (fun e => (hT e).trans (Nat.add_le_add_right (hS e) _)) (ht a))
        (hs c S))
  | draw β d k ih => exact fun y => ih y ld S hS (ht y)

/-- Independent rows with a free place. -/
theorem rows_lawF {R : Type} [Fintype ι] [Fintype R] [Nonempty R] (a a' : ι → R → F)
    (u u' : ι → R → Q → Sg) (b : ℕ)
    (h : ∀ e (T : Finset Q), T.card ≤ b →
      (unif R).map (fun r => (a e r, fun p : T => u e r p)) =
        (unif R).map (fun r => (a' e r, fun p : T => u' e r p)))
    (S : Finset (ι × Option Q)) (hS : ∀ e, rowCard (wp S) e ≤ b) :
    ((unif (ι → R)).map fun r => tab (fun e => a e (r e)) fun e => u e (r e)).map (res S) =
      ((unif (ι → R)).map fun r => tab (fun e => a' e (r e)) fun e => u' e (r e)).map (res S) := by
  rw [map_res_eq_iff]
  intro v
  have key : ∀ (c : ι → R → F) (w : ι → R → Q → Sg),
      cyl ((unif (ι → R)).map fun r => tab (fun e => c e (r e)) fun e => w e (r e)) S v =
        ((∏ e, cnt fun ρ : R =>
            ((e, none) ∈ S → c e ρ = v (e, none)) ∧
            ∀ q, (e, some q) ∈ S → w e ρ q = v (e, some q) : ℕ) : ℝ≥0∞) /
          Fintype.card (ι → R) := by
    intro c w
    rw [cyl_eq_pr, pr_map, ← cnt_forall_pi, ← pr_unif_eq]
    congr 1
    ext r
    constructor
    · intro hh e
      exact ⟨fun hq => hh (e, none) hq, fun q hq => hh (e, some q) hq⟩
    · rintro hh ⟨e, _ | q⟩ hp
      · exact (hh e).1 hp
      · exact (hh e).2 q hp
  rw [key a u, key a' u']
  congr 2
  refine Finset.prod_congr rfl fun e _ => ?_
  obtain ⟨T, hT⟩ : ∃ T : Finset Q, T = ((wp S).filter fun p => p.1 = e).image Prod.snd := ⟨_, rfl⟩
  have hmem : ∀ q, q ∈ T ↔ (e, some q) ∈ S := by
    intro q
    rw [hT]
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨hpS, hpe⟩ := Finset.mem_filter.1 hp
      subst hpe
      exact mem_wp.1 hpS
    · intro hq
      exact Finset.mem_image.2 ⟨(e, q), Finset.mem_filter.2 ⟨mem_wp.2 hq, rfl⟩, rfl⟩
  have hTb : T.card ≤ b := by
    rw [hT]
    exact Finset.card_image_le.trans (hS e)
  have hw : ∀ (w : ι → R → Q → Sg) (ρ : R),
      (∀ q, (e, some q) ∈ S → w e ρ q = v (e, some q)) ↔
      (fun p : T => w e ρ p) = fun p : T => v (e, some (p : Q)) :=
    fun w ρ =>
      ⟨fun hh => funext fun p => hh p ((hmem p).1 p.2),
        fun hh q hq => congrFun hh ⟨q, (hmem q).2 hq⟩⟩
  by_cases hn : (e, none) ∈ S
  · have hc : ∀ (c : ι → R → F) (w : ι → R → Q → Sg), (cnt fun ρ : R =>
      ((e, none) ∈ S → c e ρ = v (e, none)) ∧ ∀ q, (e, some q) ∈ S → w e ρ q = v (e, some q))
        = cnt fun ρ : R =>
            (c e ρ, fun p : T => w e ρ p) =
                ((v (e, none) : F), fun p : T => (v (e, some (p : Q)) : Sg)) := by
      intro c w
      refine cnt_congr fun ρ => ?_
      rw [hw]
      exact ⟨fun hh => Prod.ext (hh.1 hn) hh.2,
        fun hh => ⟨fun _ => congrArg Prod.fst hh, congrArg Prod.snd hh⟩⟩
    have h4 := (map_unif_eq_map_unif_iff _ _).1
      (h e T hTb) ((v (e, none) : F), fun p : T => (v (e, some (p : Q)) : Sg))
    rw [hc a u, hc a' u']
    exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos h4
  · have hc : ∀ (c : ι → R → F) (w : ι → R → Q → Sg), (cnt fun ρ : R =>
      ((e, none) ∈ S → c e ρ = v (e, none)) ∧ ∀ q, (e, some q) ∈ S → w e ρ q = v (e, some q))
        = cnt fun ρ : R => (fun p : T => w e ρ p) = fun p : T => (v (e, some (p : Q)) : Sg) := by
      intro c w
      refine cnt_congr fun ρ => ?_
      rw [hw]
      exact ⟨fun hh => hh.2, fun hh => ⟨fun h0 => absurd h0 hn, hh⟩⟩
    have h5 : (unif R).map (fun r => fun p : T => u e r p) =
        (unif R).map (fun r => fun p : T => u' e r p) := by
      have h6 := congrArg (PMF.map Prod.snd) (h e T hTb)
      rw [PMF.map_comp, PMF.map_comp] at h6
      exact h6
    have h4 := (map_unif_eq_map_unif_iff _ _).1 h5 fun p : T => (v (e, some (p : Q)) : Sg)
    rw [hc a u, hc a' u']
    exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos h4

end Hiop.Free

namespace Hiop
open Prob Compile.Lifetime
open scoped ENNReal

/-- The lifetime theorem in abstract form, for tables whose symbols have a type that depends on the
place. -/
theorem lifetimeD {C : Type} {A : C → Type} {α P Ω : Type} {X : P → Type} [DecidableEq P]
    (ν : PMF Ω) (tab : Ω → ∀ p, X p) (O' : PMF (∀ p, X p)) (real : Ω → ∀ c, PMF (A c))
    (s : ∀ c, Reader P X (A c)) (ok : C → Prop) (z : C → ℝ≥0∞) (good : Finset P → Prop)
    (h1 : ∀ ω c, ok c → tv (real ω c) ((s c).run (tab ω)) ≤ z c)
    (h2 : ∀ S, good S → (ν.map tab).map (res S) = O'.map (res S)) (t : Play C A α)
    (hok : t.Calls ok) (hin : (t.plug s).Within good ∅) :
    tv (ν.bind fun ω => t.run (real ω)) (O'.bind fun f => t.run fun c => (s c).run f) ≤
      t.cost z := by
  have e : (ν.bind fun ω => t.run fun c => (s c).run (tab ω)) =
      O'.bind fun f => t.run fun c => (s c).run f := by
    have h3 := Reader.law_eq h2 (t.plug s) hin
    have hr : (t.plug s).run = fun f => t.run fun c => (s c).run f := funext (Play.run_plug s t)
    rw [PMF.bind_map, hr] at h3
    exact h3
  rw [← e]
  exact tv_bind_right_le_of_forall ν _ _ fun ω _ => Play.tv_run_le (h1 ω) t hok

end Hiop
