-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/DeferProof_tail.lean: a proof of Spec.defer (deferred programming), for the
  challengers of Rom/Defer.lean.  Main result: DeferTail.defer.

  `DeferTail.defer : Spec.defer`: for an adversary with at most t o queries to each oracle o and at
  most N calls (N is in no bound), if every run in mode I stays within (e, M, ℓ, os) (`DSt.Within`,
  Rom/Defer.lean: no violation of the rules; at most e o plain and M o marked evaluations of o;
  marked ones only at oracles of os, each charged to a token of at least ℓ o bits), the outputs in
  mode R and mode I are within Σ over o in os of M o (t o + e o + M o) / 2^(ℓ o). (Words of this
  library: lean/GLOSSARY.md.)

  Part 1 (the two modes agree until a hit).
  A *hit* is a moment of the run in mode I at which the two modes can part: a query or a plain
  evaluation at the point of an unreleased marked evaluation, or a marked evaluation at a point that
  is in the table or is the point of an unreleased marked evaluation. cost and advCost are the
  expected number of hits in mode I plus the expectation of a final pay-off. Rel relates the two
  tables: mode R holds the unreleased evaluations, mode I does not, otherwise they agree. From
  related states every expectation in mode R of a pay-off in [0, 1] is at most the cost in mode I
  (step_le, adv_le; in step_le: of a pay-off that is no smaller on related states, hFG), so the
  distance of the views is at most the expected number of hits (tv_le_hits).

  Part 2 (a bound on the expected number of hits).  In mode I, while no rule is violated, what is
  public does not depend on the values of the tokens that are not shown.
  PSt is the public state: the table, for each token its length (hidden) or its
  value (shown), and each marked evaluation as a function of tokens. law gives the values their law
  given the public state (hidden ones uniform and independent), and PSt.inst puts values into a
  public state. Under the hypotheses of their statements, for each operation, "draw the values, then
  run the operation" equals "run the public operation, then draw the values" (inst_fresh, inst_mark,
  inst_reveal with E_snoc, E_fixLaw). One hidden coordinate can be drawn again without changing the
  law (E_resample);
  hence hitQ_bound and hitM_bound.  Each pair (marked
  evaluation, other point) is charged once, at the later of the two, to the potential pot = Σ a
  (b + a) / 2^ℓ, for `a` marked evaluations and `b` logged points of an oracle (step_bound,
  adv_bound).

  Notation:
    `c.run modeI d`, `C.world modeI` (Rom/Defer.lean): modeI = true is mode I, false is mode R
    `Ev S` (Rom/Defer.lean): the record of one marked evaluation: the fields `o`, `pt`, `ans`,
      `charged`, `others`, `tail`, `released`, in this order
    `sp`: `Split S` (Rom/Defer.lean): the fields `Vis`, `tl` and
      `split : ∀ o, S.Rng o ≃ Vis o × (Fin (tl o) → Bool)`
    `cost c d K`: the expected number of hits during a step in mode I, plus the expectation of K at
      its end; `advCost C A s G`: the same for a whole run of an adversary against a challenger
    `Rel TR T evs`: TR is the table of mode R, T the table of mode I, evs the marked evaluations
      (the same in both modes)
    `FR`, `G` in `step_le`, `G` in `adv_le`: `α × DSt S → ℝ≥0∞`, `α → ℝ≥0∞`: pay-offs
    `u`, `t'` in `adv_bound`: `S.ι → ℕ`: tied by `Valid ℓ os u p` (the log has at most u o + nPlain
      o points of o), `A.Bounded t' N` and `∀ o, u o + t' o ≤ t o`
    `H`, `K`, `Q` in `step_bound`: `ℝ≥0∞`, `α × DSt S → ℝ≥0∞`, `α × DSt S → Prop`
    `A.Bounded t N` (Rom/World.lean): at most t o queries to oracle o and at most N calls, on every
      path
    `tv p q` (Prob/Basic.lean): statistical (total variation) distance of two discrete distributions
-/
import Rom.Defer
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail

variable {S : OSpec}

/-- 1 if P holds, 0 otherwise -/
def ind (P : Prop) : ℝ≥0∞ := by classical exact if P then 1 else 0

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]
theorem ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by simp [ind, h]
theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_pos h]
  · rw [ind_neg h]; exact zero_le _
theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases hp : P
  · rw [ind_pos hp, ind_pos (h hp)]
  · rw [ind_neg hp]; exact zero_le _

/-- an oracle with a point of its domain -/
abbrev Pt (S : OSpec) : Type := Σ o : S.ι, S.Dom o

theorem set_same (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    (T.set o q r) o q = some r := by
  simp [Table.set]

theorem set_ne (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) (o' : S.ι) (q' : S.Dom o')
    (h : (⟨o', q'⟩ : Pt S) ≠ ⟨o, q⟩) : (T.set o q r) o' q' = T o' q' := by
  unfold Table.set
  by_cases ho : o' = o
  · subst ho
    have hq : q' ≠ q := fun e => h (by rw [e])
    rw [Function.update_self, Function.update_of_ne hq]
  · rw [Function.update_of_ne ho]

theorem lazyAnswer_some {T : Table S} {o : S.ι} {q : S.Dom o} {r : S.Rng o} (h : T o q = some r) :
    lazyAnswer T o q = PMF.pure (r, T) := by
  simp [lazyAnswer, h]

theorem lazyAnswer_none {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) :
    lazyAnswer T o q = (PMF.uniformOfFintype (S.Rng o)).map fun r => (r, T.set o q r) := by
  simp [lazyAnswer, h]

/-! ### The states after each operation, by name -/

def withT (d : DSt S) (T : Table S) : DSt S := { d with table := T }

def postPlain (d : DSt S) (o : S.ι) (T : Table S) : DSt S :=
  { d with table := T, nPlain := Function.update d.nPlain o (d.nPlain o + 1) }

def postFresh (d : DSt S) (v : Bits) : DSt S := { d with vals := d.vals ++ [v] }

def markedBad (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) : Bool :=
  decide (d.vals.length ≤ t) || us.any (fun u => decide (d.vals.length ≤ u)) || us.contains t ||
    d.shown.contains t ||
    d.evs.any fun e => decide (e.o = o) && (e.charged == t || e.others.contains t)

def postMarked (sp : Split S) (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) : DSt S :=
  { d with
    table := T, vals := d.vals ++ [List.ofFn (sp.split o r).2],
    evs := d.evs ++ [⟨o, P, r, t, us, d.vals.length, false⟩], viol := d.viol || markedBad d o t us }

def postReveal (modeI : Bool) (d : DSt S) (ts : List Tok) : DSt S :=
  { d with
    table := (releaseAll modeI (d.shown ++ ts) d.evs d.table).2, shown := d.shown ++ ts,
    evs := (releaseAll modeI (d.shown ++ ts) d.evs d.table).1,
    viol := d.viol ||
        !closedUnder (d.shown ++ ts) (releaseAll modeI (d.shown ++ ts) d.evs d.table).1 ||
        ts.any (fun u => decide (d.vals.length ≤ u)) }

section RunEqs
variable {sp : Split S} {α : Type}

theorem run_pure (m : Bool) (a : α) (d : DSt S) :
    (Step.pure a : Step S sp α).run m d = PMF.pure (a, d) := rfl

theorem run_sample (m : Bool) (n : ℕ) (k : Fin (n + 1) → Step S sp α) (d : DSt S) :
    (Step.sample n k).run m d = (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).run m d :=
  rfl

theorem run_plain (m : Bool) (o : S.ι) (q : S.Dom o) (k : S.Rng o → Step S sp α) (d : DSt S) :
    (Step.plain o q k).run m d
      = (lazyAnswer d.table o q).bind fun p => (k p.1).run m (postPlain d o p.2) := rfl

theorem run_fresh (m : Bool) (ℓ : ℕ) (k : Tok → Step S sp α) (d : DSt S) :
    (Step.fresh ℓ k).run m d
      = (PMF.uniformOfFintype (Fin ℓ → Bool)).bind fun u =>
          (k d.vals.length).run m (postFresh d (List.ofFn u)) := rfl

theorem run_marked_I (o : S.ι) (t : Tok) (us : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    (k : sp.Vis o → Tok → Step S sp α) (d : DSt S) :
    (Step.marked o t us pt inj k).run true d = (PMF.uniformOfFintype (S.Rng o)).bind fun r =>
          (k (sp.split o r).1 d.vals.length).run true
            (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table) := rfl

theorem run_marked_R (o : S.ι) (t : Tok) (us : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    (k : sp.Vis o → Tok → Step S sp α) (d : DSt S) :
    (Step.marked o t us pt inj k).run false d =
      (lazyAnswer d.table o (pt (d.val t) (us.map d.val))).bind fun p =>
          (k (sp.split o p.1).1 d.vals.length).run false
            (postMarked sp d o t us (pt (d.val t) (us.map d.val)) p.1 p.2) := rfl

theorem run_reveal (m : Bool) (ts : List Tok) (k : List Bits → Step S sp α) (d : DSt S) :
    (Step.reveal ts k).run m d = (k (ts.map d.val)).run m (postReveal m d ts) := rfl

end RunEqs

/-! ### Hits and costs -/

/-- k is the point of a marked evaluation that is not released -/
def Unrel (evs : List (Ev S)) (k : Pt S) : Prop :=
  ∃ e ∈ evs, e.released = false ∧ (⟨e.o, e.pt⟩ : Pt S) = k

/-- 1 if a query or a plain evaluation at this point is a hit -/
def hitQ (evs : List (Ev S)) (k : Pt S) : ℝ≥0∞ := ind (Unrel evs k)

/-- 1 if a marked evaluation at this point is a hit -/
def hitM (T : Table S) (evs : List (Ev S)) (k : Pt S) : ℝ≥0∞ :=
  ind (T k.1 k.2 ≠ none ∨ Unrel evs k)

/-- the expected number of hits during a step in mode I, plus the expectation of K at its end -/
def cost {sp : Split S} {α : Type} :
    Step S sp α → DSt S → (α × DSt S → ℝ≥0∞) → ℝ≥0∞
  | .pure a, d, K => K (a, d)
  | .sample n k, d, K => expect (PMF.uniformOfFintype (Fin (n + 1))) fun r => cost (k r) d K
  | .plain o q k, d, K => hitQ d.evs ⟨o, q⟩ +
      expect (lazyAnswer d.table o q) fun p => cost (k p.1) (postPlain d o p.2) K
  | .fresh ℓ k, d, K => expect (PMF.uniformOfFintype (Fin ℓ → Bool)) fun u =>
      cost (k d.vals.length) (postFresh d (List.ofFn u)) K
  | .marked o t us pt _ k, d, K => hitM d.table d.evs ⟨o, pt (d.val t) (us.map d.val)⟩ +
      expect (PMF.uniformOfFintype (S.Rng o)) fun r =>
        cost (k (sp.split o r).1 d.vals.length)
          (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table) K
  | .reveal ts k, d, K => cost (k (ts.map d.val)) (postReveal true d ts) K

/-- the same for a whole run of an adversary against a challenger -/
def advCost {sp : Split S} {Out In α : Type} (C : Chall S sp Out In) :
    Adv S Out In α → C.τ × DSt S → (α → ℝ≥0∞) → ℝ≥0∞
  | .halt a, _, G => G a
  | .sample n k, s, G => expect (PMF.uniformOfFintype (Fin (n + 1))) fun r => advCost C (k r) s G
  | .query o q k, s, G => hitQ s.2.evs ⟨o, q⟩ +
      expect (lazyAnswer s.2.table o q) fun p => advCost C (k p.1) (s.1, withT s.2 p.2) G
  | .call m k, s, G => cost (C.step s.1 m) s.2 fun y => advCost C (k y.1.1) (y.1.2, y.2) G

/-- cost is the expectation of the pay-off in mode I plus the expected number of hits -/
theorem cost_add {sp : Split S} {α : Type} (c : Step S sp α) :
    ∀ (d : DSt S) (K₁ K₂ : α × DSt S → ℝ≥0∞),
      cost c d (fun y => K₁ y + K₂ y) = expect (c.run true d) K₁ + cost c d K₂ := by
  induction c with
  | pure a => intro d K₁ K₂; simp only [cost, run_pure, expect_pure]
  | sample n k ih =>
    intro d K₁ K₂
    simp only [cost, run_sample, expect_bind, ih, expect_add]
  | plain o q k ih =>
    intro d K₁ K₂
    simp only [cost, run_plain, expect_bind, ih, expect_add]
    exact add_left_comm _ _ _
  | fresh ℓ k ih =>
    intro d K₁ K₂
    simp only [cost, run_fresh, expect_bind, ih, expect_add]
  | marked o t us pt inj k ih =>
    intro d K₁ K₂
    simp only [cost, run_marked_I, expect_bind, ih, expect_add]
    exact add_left_comm _ _ _
  | reveal ts k ih =>
    intro d K₁ K₂
    simp only [cost, run_reveal, ih]

theorem advCost_add {sp : Split S} {Out In α : Type} (C : Chall S sp Out In) (A : Adv S Out In α) :
    ∀ (s : C.τ × DSt S) (G₁ G₂ : α → ℝ≥0∞),
      advCost C A s (fun a => G₁ a + G₂ a)
        = expect (interact (C.world true) A s) (fun x => G₁ x.1) + advCost C A s G₂ := by
  induction A with
  | halt a => intro s G₁ G₂; simp only [advCost, interact, expect_pure]
  | sample n k ih =>
    intro s G₁ G₂
    simp only [advCost, interact, expect_bind, ih, expect_add]
  | query o q k ih =>
    intro s G₁ G₂
    simp only [advCost, interact, Chall.world, expect_bind, expect_map, ih, expect_add]
    exact add_left_comm _ _ _
  | call m k ih =>
    intro s G₁ G₂
    simp only [advCost, interact, Chall.world, expect_bind, expect_map, ih]
    exact cost_add _ _ _ _

/-! ### releaseAll -/

/-- the evaluation is released by a reveal after which the tokens of shown are shown -/
def Newly (shown : List Tok) (e : Ev S) : Prop :=
  e.released = false ∧ shown.contains e.charged = true

/-- what a reveal does to the record of one evaluation -/
def rel1 (shown : List Tok) (e : Ev S) : Ev S :=
  if !e.released && shown.contains e.charged then { e with released := true } else e

theorem cond_iff_newly (shown : List Tok) (e : Ev S) :
    (!e.released && shown.contains e.charged) = true ↔ Newly shown e := by
  simp [Newly]

theorem rel1_of_newly {shown : List Tok} {e : Ev S} (h : Newly shown e) :
    rel1 shown e = { e with released := true } := by
  rw [rel1, if_pos ((cond_iff_newly shown e).2 h)]

theorem rel1_of_not_newly {shown : List Tok} {e : Ev S} (h : ¬ Newly shown e) :
    rel1 shown e = e := by
  rw [rel1, if_neg fun hc => h ((cond_iff_newly shown e).1 hc)]

/-- the release of one evaluation in mode I: its answer is written if the entry is empty -/
def wr (T : Table S) (e : Ev S) : Table S :=
  match T e.o e.pt with
  | none => T.set e.o e.pt e.ans
  | some _ => T

theorem wr_ne (T : Table S) (e : Ev S) (o : S.ι) (x : S.Dom o) (h : (⟨o, x⟩ : Pt S) ≠ ⟨e.o, e.pt⟩) :
    (wr T e) o x = T o x := by
  have hw : wr T e = T.set e.o e.pt e.ans ∨ wr T e = T := by
    unfold wr
    cases T e.o e.pt <;> simp
  rcases hw with hw | hw
  · rw [hw]; exact set_ne _ _ _ _ _ _ h
  · rw [hw]

theorem wr_same (T : Table S) (e : Ev S) (h : T e.o e.pt = none) :
    (wr T e) e.o e.pt = some e.ans := by
  unfold wr
  rw [h]
  exact set_same _ _ _ _

theorem releaseAll_cons_newly
    (m : Bool) {shown : List Tok} {e : Ev S} (h : Newly shown e) (es : List (Ev S)) (T : Table S) :
    releaseAll m shown (e :: es) T =
      ({ e with released := true } :: (releaseAll m shown es (if m then wr T e else T)).1,
        (releaseAll m shown es (if m then wr T e else T)).2) := by
  rw [releaseAll, if_pos ((cond_iff_newly shown e).2 h)]
  rfl

theorem releaseAll_cons_not (m : Bool) {shown : List Tok} {e : Ev S} (h : ¬ Newly shown e)
    (es : List (Ev S)) (T : Table S) :
    releaseAll m shown (e :: es) T =
      (e :: (releaseAll m shown es T).1, (releaseAll m shown es T).2) := by
  rw [releaseAll, if_neg fun hc => h ((cond_iff_newly shown e).1 hc)]

theorem releaseAll_fst (m : Bool) (shown : List Tok) (evs : List (Ev S)) :
    ∀ T : Table S, (releaseAll m shown evs T).1 = evs.map (rel1 shown) := by
  induction evs with
  | nil => intro T; rfl
  | cons e es ih =>
    intro T
    by_cases h : Newly shown e
    · rw [releaseAll_cons_newly m h, List.map_cons, rel1_of_newly h, ih]
    · rw [releaseAll_cons_not m h, List.map_cons, rel1_of_not_newly h, ih]

theorem releaseAll_snd_false (shown : List Tok) (evs : List (Ev S)) :
    ∀ T : Table S, (releaseAll false shown evs T).2 = T := by
  induction evs with
  | nil => intro T; rfl
  | cons e es ih =>
    intro T
    by_cases h : Newly shown e
    · rw [releaseAll_cons_newly false h]; exact ih T
    · rw [releaseAll_cons_not false h]; exact ih T

/-- a release leaves every entry that is not the point of a newly released evaluation -/
theorem releaseAll_snd_other (shown : List Tok) (evs : List (Ev S)) (o : S.ι) (x : S.Dom o) :
    ∀ T : Table S, (∀ e ∈ evs, Newly shown e → (⟨e.o, e.pt⟩ : Pt S) ≠ ⟨o, x⟩) →
      (releaseAll true shown evs T).2 o x = T o x := by
  induction evs with
  | nil => intro T _; rfl
  | cons e es ih =>
    intro T h
    have hes : ∀ e' ∈ es, Newly shown e' → (⟨e'.o, e'.pt⟩ : Pt S) ≠ ⟨o, x⟩ :=
      fun e' he' => h e' (List.mem_cons_of_mem _ he')
    by_cases hn : Newly shown e
    · rw [releaseAll_cons_newly true hn]
      show (releaseAll true shown es (wr T e)).2 o x = T o x
      rw [ih _ hes, wr_ne _ _ _ _ (h e List.mem_cons_self hn).symm]
    · rw [releaseAll_cons_not true hn]
      exact ih T hes

/-- unreleased evaluations have different points -/
def Distinct (evs : List (Ev S)) : Prop :=
  evs.Pairwise fun e e' =>
    e.released = false → e'.released = false → (⟨e.o, e.pt⟩ : Pt S) ≠ ⟨e'.o, e'.pt⟩

/-- Under `Distinct`, if the entries of all newly released evaluations are empty, a release writes
their answers. -/
theorem releaseAll_snd_new (shown : List Tok) (evs : List (Ev S)) :
    ∀ T : Table S, Distinct evs → (∀ e ∈ evs, Newly shown e → T e.o e.pt = none) →
      ∀ e ∈ evs, Newly shown e → (releaseAll true shown evs T).2 e.o e.pt = some e.ans := by
  induction evs with
  | nil => intro T _ _ e he; simp at he
  | cons e₀ es ih =>
    intro T hd hT e he hn
    have hd' := List.pairwise_cons.1 hd
    rcases List.mem_cons.1 he with rfl | he'
    · rw [releaseAll_cons_newly true hn]
      show (releaseAll true shown es (wr T e)).2 e.o e.pt = some e.ans
      rw [releaseAll_snd_other shown es e.o e.pt _ fun e' he' hn' => (hd'.1 e' he' hn.1 hn'.1).symm,
        wr_same _ _ (hT e List.mem_cons_self hn)]
    · by_cases hn₀ : Newly shown e₀
      · rw [releaseAll_cons_newly true hn₀]
        refine ih _ hd'.2 (fun e' he'' hn' => ?_) e he' hn
        show (wr T e₀) e'.o e'.pt = none
        rw [wr_ne _ _ _ _ (hd'.1 e' he'' hn₀.1 hn'.1).symm]
        exact hT e' (List.mem_cons_of_mem _ he'') hn'
      · rw [releaseAll_cons_not true hn₀]
        exact ih _ hd'.2 (fun e' he'' hn' => hT e' (List.mem_cons_of_mem _ he'') hn') e he' hn

/-! ### The relation between the two modes -/

/-- TR is the table of mode R, T the table of mode I, evs the marked evaluations (the same in both
modes):
mode R has the unreleased evaluations in its table, mode I has not, and otherwise the tables
agree. -/
structure Rel (TR T : Table S) (evs : List (Ev S)) : Prop where
  unrel : ∀ e ∈ evs, e.released = false → TR e.o e.pt = some e.ans ∧ T e.o e.pt = none
  other : ∀ o x, ¬ Unrel evs ⟨o, x⟩ → TR o x = T o x
  distinct : Distinct evs

theorem Rel.init : Rel (Table.empty S) (Table.empty S) [] :=
  ⟨fun e he => by simp at he, fun _ _ _ => rfl, List.Pairwise.nil⟩

theorem Rel.query {TR T : Table S} {evs : List (Ev S)} (h : Rel TR T evs) {o : S.ι} {q : S.Dom o}
    (hit : ¬ Unrel evs ⟨o, q⟩) (r : S.Rng o) : Rel (TR.set o q r) (T.set o q r) evs := by
  refine ⟨fun e he hr => ?_, fun o' x hx => ?_, h.distinct⟩
  · have hne : (⟨e.o, e.pt⟩ : Pt S) ≠ ⟨o, q⟩ := fun hk => hit ⟨e, he, hr, hk⟩
    rw [set_ne _ _ _ _ _ _ hne, set_ne _ _ _ _ _ _ hne]
    exact h.unrel e he hr
  · by_cases hk : (⟨o', x⟩ : Pt S) = ⟨o, q⟩
    · obtain ⟨rfl, hx'⟩ := Sigma.mk.inj_iff.1 hk
      obtain rfl := eq_of_heq hx'
      rw [set_same, set_same]
    · rw [set_ne _ _ _ _ _ _ hk, set_ne _ _ _ _ _ _ hk]
      exact h.other o' x hx

theorem unrel_append {evs : List (Ev S)} {e : Ev S} {k : Pt S} :
    Unrel (evs ++ [e]) k ↔ Unrel evs k ∨ (e.released = false ∧ (⟨e.o, e.pt⟩ : Pt S) = k) := by
  constructor
  · rintro ⟨e', he', hr, hk⟩
    rcases List.mem_append.1 he' with h | h
    · exact Or.inl ⟨e', h, hr, hk⟩
    · obtain rfl := List.mem_singleton.1 h
      exact Or.inr ⟨hr, hk⟩
  · rintro (⟨e', he', hr, hk⟩ | ⟨hr, hk⟩)
    · exact ⟨e', List.mem_append_left _ he', hr, hk⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton.2 rfl), hr, hk⟩

theorem Rel.marked {TR T : Table S} {evs : List (Ev S)} (h : Rel TR T evs) (e : Ev S)
    (hr : e.released = false) (hT : T e.o e.pt = none) (hit : ¬ Unrel evs ⟨e.o, e.pt⟩) :
    Rel (TR.set e.o e.pt e.ans) T (evs ++ [e]) := by
  refine ⟨fun e' he' hr' => ?_, fun o' x hx => ?_, ?_⟩
  · rcases List.mem_append.1 he' with h' | h'
    · have hne : (⟨e'.o, e'.pt⟩ : Pt S) ≠ ⟨e.o, e.pt⟩ := fun hk => hit ⟨e', h', hr', hk⟩
      rw [set_ne _ _ _ _ _ _ hne]
      exact h.unrel e' h' hr'
    · obtain rfl := List.mem_singleton.1 h'
      exact ⟨set_same _ _ _ _, hT⟩
  · have hx' := fun hh => hx (unrel_append.2 hh)
    have hne : (⟨o', x⟩ : Pt S) ≠ ⟨e.o, e.pt⟩ := fun hk => hx' (Or.inr ⟨hr, hk.symm⟩)
    rw [set_ne _ _ _ _ _ _ hne]
    exact h.other o' x fun hh => hx' (Or.inl hh)
  · refine List.pairwise_append.2 ⟨h.distinct, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    obtain rfl := List.mem_singleton.1 hb
    exact fun hra _ hk => hit ⟨a, ha, hra, hk⟩

theorem rel1_o_pt (shown : List Tok) (e : Ev S) :
    (⟨(rel1 shown e).o, (rel1 shown e).pt⟩ : Pt S) = ⟨e.o, e.pt⟩ := by
  by_cases h : Newly shown e
  · rw [rel1_of_newly h]
  · rw [rel1_of_not_newly h]

theorem rel1_unreleased {shown : List Tok} {e : Ev S} (h : (rel1 shown e).released = false) :
    ¬ Newly shown e ∧ e.released = false := by
  by_cases hn : Newly shown e
  · rw [rel1_of_newly hn] at h; simp at h
  · rw [rel1_of_not_newly hn] at h; exact ⟨hn, h⟩

theorem Rel.release {TR T : Table S} {evs : List (Ev S)} (h : Rel TR T evs) (shown : List Tok) :
    Rel TR (releaseAll true shown evs T).2 (evs.map (rel1 shown)) := by
  have hpair : ∀ e ∈ evs, ∀ e' ∈ evs, e.released = false → e'.released = false → ¬ Newly shown e →
      Newly shown e' → (⟨e'.o, e'.pt⟩ : Pt S) ≠ ⟨e.o, e.pt⟩ := by
    intro e he e' he' hr hr' hn hn' hk
    have hsym : Symmetric fun a b : Ev S =>
        a.released = false → b.released = false → (⟨a.o, a.pt⟩ : Pt S) ≠ ⟨b.o, b.pt⟩ :=
      fun a b hab hb ha hk => hab ha hb hk.symm
    have hne : e ≠ e' := fun hee => hn (hee ▸ hn')
    exact (h.distinct.forall hsym he he' hne) hr hr' hk.symm
  refine ⟨fun e₁ he₁ hr₁ => ?_, fun o x hx => ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he₁
    obtain ⟨hn, hr⟩ := rel1_unreleased hr₁
    rw [rel1_of_not_newly hn]
    refine ⟨(h.unrel e he hr).1, ?_⟩
    rw [releaseAll_snd_other shown evs e.o e.pt T fun e' he' hn' =>
        hpair e he e' he' hr hn'.1 hn hn']
    exact (h.unrel e he hr).2
  · by_cases hu : Unrel evs ⟨o, x⟩
    · obtain ⟨e, he, hr, hk⟩ := hu
      have hn : Newly shown e := by
        by_contra hn
        exact hx ⟨rel1 shown e, List.mem_map_of_mem he, by rw [rel1_of_not_newly hn]; exact hr,
          by rw [rel1_o_pt]; exact hk⟩
      obtain ⟨rfl, hx'⟩ := Sigma.mk.inj_iff.1 hk
      obtain rfl := eq_of_heq hx'
      rw [releaseAll_snd_new shown evs T h.distinct
          (fun e' he' hn' => (h.unrel e' he' hn'.1).2) e he hn]
      exact (h.unrel e he hr).1
    · rw [releaseAll_snd_other shown evs o x T fun e he hn hk => hu ⟨e, he, hn.1, hk⟩]
      exact h.other o x hu
  · refine List.pairwise_map.2 (h.distinct.imp fun {a b} hab ha hb => ?_)
    rw [rel1_o_pt, rel1_o_pt]
    exact hab (rel1_unreleased ha).2 (rel1_unreleased hb).2

/-! ### Expectations in mode R against the cost in mode I -/

/-- one lazily answered query, in both modes -/
theorem lazy_le {TR T : Table S} {evs : List (Ev S)} (h : Rel TR T evs) (o : S.ι) (q : S.Dom o)
    (XR XI : S.Rng o × Table S → ℝ≥0∞) (h1 : ∀ y, XR y ≤ 1)
    (hX : ∀ r TR' T', Rel TR' T' evs → XR (r, TR') ≤ XI (r, T')) :
    expect (lazyAnswer TR o q) XR ≤ hitQ evs ⟨o, q⟩ + expect (lazyAnswer T o q) XI := by
  by_cases hit : Unrel evs ⟨o, q⟩
  · rw [hitQ, ind_pos hit]
    exact le_add_right (expect_le_of_forall_le _ fun y _ => h1 y)
  · rw [hitQ, ind_neg hit, zero_add]
    have e := h.other o q hit
    cases hT : T o q with
    | some r =>
      rw [lazyAnswer_some hT, lazyAnswer_some (e.trans hT), expect_pure, expect_pure]
      exact hX r TR T h
    | none =>
      rw [lazyAnswer_none hT, lazyAnswer_none (e.trans hT), expect_map, expect_map]
      exact expect_mono _ fun r => hX r _ _ (h.query hit r)

theorem step_le {sp : Split S} {α : Type} (FR G : α × DSt S → ℝ≥0∞) (h1 : ∀ y, FR y ≤ 1)
    (hFG : ∀ a d TR, Rel TR d.table d.evs → FR (a, withT d TR) ≤ G (a, d)) (c : Step S sp α) :
    ∀ (d : DSt S) (TR : Table S), Rel TR d.table d.evs →
      expect (c.run false (withT d TR)) FR ≤ cost c d G := by
  induction c with
  | pure a =>
    intro d TR h
    rw [run_pure, expect_pure, cost]
    exact hFG a d TR h
  | sample n k ih =>
    intro d TR h
    rw [run_sample, expect_bind, cost]
    exact expect_mono _ fun r => ih r d TR h
  | plain o q k ih =>
    intro d TR h
    rw [run_plain, expect_bind, cost]
    refine lazy_le h o q _ _
      (fun y => expect_le_of_forall_le _ fun z _ => h1 z) fun r TR' T' h' => ?_
    exact ih r (postPlain d o T') TR' h'
  | fresh ℓ k ih =>
    intro d TR h
    rw [run_fresh, expect_bind, cost]
    exact expect_mono _ fun u => ih _ (postFresh d (List.ofFn u)) TR h
  | marked o t us pt inj k ih =>
    intro d TR h
    rw [run_marked_R, expect_bind, cost]
    by_cases hit : d.table o (pt (d.val t) (us.map d.val)) ≠ none ∨
      Unrel d.evs ⟨o, pt (d.val t) (us.map d.val)⟩
    · rw [hitM, ind_pos hit]
      exact le_add_right
        (expect_le_of_forall_le _ fun y _ => expect_le_of_forall_le _ fun z _ => h1 z)
    · rw [hitM, ind_neg hit, zero_add]
      have hT : d.table o (pt (d.val t) (us.map d.val)) = none := by
        by_contra hc; exact hit (Or.inl hc)
      have hU : ¬ Unrel d.evs ⟨o, pt (d.val t) (us.map d.val)⟩ := fun hc => hit (Or.inr hc)
      have hTR : (withT d TR).table o (pt (d.val t) (us.map d.val)) = none :=
        (h.other _ _ hU).trans hT
      have hl : lazyAnswer (withT d TR).table o (pt ((withT d TR).val t) (us.map (withT d TR).val))
          = (PMF.uniformOfFintype (S.Rng o)).map fun r =>
              (r, TR.set o (pt (d.val t) (us.map d.val)) r) := lazyAnswer_none hTR
      rw [hl, expect_map]
      refine expect_mono _ fun r => ?_
      exact ih _ _ (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table)
        (TR.set o (pt (d.val t) (us.map d.val)) r)
        (h.marked ⟨o, pt (d.val t) (us.map d.val), r, t, us, d.vals.length, false⟩ rfl hT hU)
  | reveal ts k ih =>
    intro d TR h
    rw [run_reveal, cost]
    have e : postReveal false (withT d TR) ts = withT (postReveal true d ts) TR := by
      simp only [postReveal, withT, releaseAll_fst, releaseAll_snd_false]
      rfl
    rw [e]
    refine ih _ (postReveal true d ts) TR ?_
    have := h.release (d.shown ++ ts)
    simpa only [postReveal, releaseAll_fst] using this

theorem adv_le {sp : Split S} {Out In α : Type} (C : Chall S sp Out In) (G : α → ℝ≥0∞)
    (h1 : ∀ a, G a ≤ 1) (A : Adv S Out In α) :
    ∀ (s : C.τ × DSt S) (TR : Table S), Rel TR s.2.table s.2.evs →
      expect (interact (C.world false) A (s.1, withT s.2 TR)) (fun x => G x.1) ≤
        advCost C A s G := by
  induction A with
  | halt a =>
    intro s TR _
    simp only [interact, expect_pure, advCost, le_refl]
  | sample n k ih =>
    intro s TR h
    simp only [interact, expect_bind, advCost]
    exact expect_mono _ fun r => ih r s TR h
  | query o q k ih =>
    intro s TR h
    simp only [interact, Chall.world, expect_bind, expect_map, advCost]
    refine lazy_le h o q _ _
      (fun y => expect_le_of_forall_le _ fun z _ => h1 z.1) fun r TR' T' h' => ?_
    exact ih r (s.1, withT s.2 T') TR' h'
  | call m k ih =>
    intro s TR h
    simp only [interact, Chall.world, expect_bind, expect_map, advCost]
    refine step_le _ _ (fun y => expect_le_of_forall_le _ fun z _ => h1 z.1)
      (fun a d TR' h' => ?_) _ s.2 TR h
    exact ih a.1 (a.2, d) TR' h'

/-- Part 1. The distance of the two modes is at most the expected number of hits in mode I. -/
theorem tv_le_hits {sp : Split S} {Out In α : Type} (C : Chall S sp Out In)
    (s₀ : C.τ) (A : Adv S Out In α) :
    tv ((interact (C.world false) A (s₀, DSt.init S)).map Prod.fst)
        ((interact (C.world true) A (s₀, DSt.init S)).map Prod.fst) ≤
      advCost C A (s₀, DSt.init S) fun _ => 0 := by
  classical
  refine tv_le_of_forall_pr_le fun E => ?_
  rw [pr_eq_expect, pr_eq_expect, expect_map, expect_map]
  have h := adv_le C (fun a => if a ∈ E then 1 else 0) (fun a => by dsimp only; split_ifs <;> simp)
    A (s₀, DSt.init S) (Table.empty S) Rel.init
  have h2 := advCost_add C A (s₀, DSt.init S) (fun a => if a ∈ E then 1 else 0) (fun _ => 0)
  simp only [add_zero] at h2
  rw [h2] at h
  exact h

/-! ## Part 2.  A bound on the expected number of hits

### What a later state keeps of an earlier one -/

/-- the oracle and the charged token of an evaluation -/
def skel (e : Ev S) : S.ι × Tok := (e.o, e.charged)

/-- what a later state d' of a run keeps of an earlier state d -/
structure Ext (d d' : DSt S) : Prop where
  viol : d.viol = true → d'.viol = true
  vals : d.vals <+: d'.vals
  evs : d.evs.map skel <+: d'.evs.map skel
  nPlain : ∀ o, d.nPlain o ≤ d'.nPlain o

theorem Ext.refl (d : DSt S) : Ext d d := ⟨id, List.prefix_rfl, List.prefix_rfl, fun _ => le_rfl⟩

theorem Ext.trans {d₁ d₂ d₃ : DSt S} (h : Ext d₁ d₂) (h' : Ext d₂ d₃) : Ext d₁ d₃ :=
  ⟨fun x => h'.viol (h.viol x), h.vals.trans h'.vals, h.evs.trans h'.evs,
    fun o => (h.nPlain o).trans (h'.nPlain o)⟩

theorem ext_withT (d : DSt S) (T : Table S) : Ext d (withT d T) :=
  ⟨id, List.prefix_rfl, List.prefix_rfl, fun _ => le_rfl⟩

theorem ext_postPlain (d : DSt S) (o : S.ι) (T : Table S) : Ext d (postPlain d o T) := by
  refine ⟨id, List.prefix_rfl, List.prefix_rfl, fun o' => ?_⟩
  by_cases h : o' = o
  · subst h; simp [postPlain]
  · simp [postPlain, Function.update_of_ne h]

theorem ext_postFresh (d : DSt S) (v : Bits) : Ext d (postFresh d v) :=
  ⟨id, List.prefix_append _ _, List.prefix_rfl, fun _ => le_rfl⟩

theorem ext_postMarked (sp : Split S) (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Ext d (postMarked sp d o t us P r T) := by
  refine ⟨fun h => ?_, List.prefix_append _ _, ?_, fun _ => le_rfl⟩
  · simp [postMarked, h]
  · simp only [postMarked, List.map_append]
    exact List.prefix_append _ _

theorem skel_rel1 (shown : List Tok) (e : Ev S) : skel (rel1 shown e) = skel e := by
  by_cases h : Newly shown e
  · rw [rel1_of_newly h]; rfl
  · rw [rel1_of_not_newly h]

theorem ext_postReveal (d : DSt S) (ts : List Tok) : Ext d (postReveal true d ts) := by
  refine ⟨fun h => ?_, List.prefix_rfl, ?_, fun _ => le_rfl⟩
  · simp [postReveal, h]
  · simp only [postReveal, releaseAll_fst, List.map_map]
    have : (skel ∘ rel1 (d.shown ++ ts) : Ev S → S.ι × Tok) = skel := funext fun e => skel_rel1 _ e
    rw [this]

theorem run_ext {sp : Split S} {α : Type} (c : Step S sp α) :
    ∀ (d : DSt S) (y : α × DSt S), y ∈ (c.run true d).support → Ext d y.2 := by
  induction c with
  | pure a =>
    intro d y hy
    rw [run_pure, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact Ext.refl d
  | sample n k ih =>
    intro d y hy
    rw [run_sample, PMF.mem_support_bind_iff] at hy
    obtain ⟨r, _, hy⟩ := hy
    exact ih r d y hy
  | plain o q k ih =>
    intro d y hy
    rw [run_plain, PMF.mem_support_bind_iff] at hy
    obtain ⟨p, _, hy⟩ := hy
    exact (ext_postPlain d o p.2).trans (ih _ _ y hy)
  | fresh ℓ k ih =>
    intro d y hy
    rw [run_fresh, PMF.mem_support_bind_iff] at hy
    obtain ⟨u, _, hy⟩ := hy
    exact (ext_postFresh d _).trans (ih _ _ y hy)
  | marked o t us pt inj k ih =>
    intro d y hy
    rw [run_marked_I, PMF.mem_support_bind_iff] at hy
    obtain ⟨r, _, hy⟩ := hy
    exact (ext_postMarked sp d o t us _ r _).trans (ih _ _ _ y hy)
  | reveal ts k ih =>
    intro d y hy
    rw [run_reveal] at hy
    exact (ext_postReveal d ts).trans (ih _ _ y hy)

theorem interact_ext {sp : Split S} {Out In α : Type} (C : Chall S sp Out In) (A : Adv S Out In α) :
    ∀ (s : C.τ × DSt S) (x : α × (C.τ × DSt S)),
      x ∈ (interact (C.world true) A s).support → Ext s.2 x.2.2 := by
  induction A with
  | halt a =>
    intro s x hx
    rw [interact] at hx
    have hx' := (PMF.mem_support_pure_iff _ _).1 hx
    subst hx'; exact Ext.refl _
  | sample n k ih =>
    intro s x hx
    rw [interact] at hx
    obtain ⟨r, _, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    exact ih r s x hx
  | query o q k ih =>
    intro s x hx
    rw [interact] at hx
    obtain ⟨p, hp, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    obtain ⟨p', _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact (ext_withT s.2 p'.2).trans (ih _ _ x hx)
  | call m k ih =>
    intro s x hx
    rw [interact] at hx
    obtain ⟨p, hp, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact (run_ext _ _ y hy).trans (ih _ _ x hx)

/-! ### Hidden and public tokens: the law of the values -/

/-- what is public about a token: its length if it is hidden, its value if it is shown -/
inductive Slot : Type
  | hid (ℓ : ℕ) : Slot
  | pub (v : Bits) : Slot

/-- the value v fits the slot -/
def Slot.Ok : Slot → Bits → Prop
  | .hid ℓ, v => v.length = ℓ
  | .pub x, v => v = x

def Slot.draw : Slot → PMF Bits
  | .hid ℓ => (PMF.uniformOfFintype (Fin ℓ → Bool)).map List.ofFn
  | .pub v => PMF.pure v

/-- the law of the list of all values, given what is public: hidden ones are uniform and
independent -/
def law : List Slot → PMF (List Bits)
  | [] => PMF.pure []
  | s :: ss => s.draw.bind fun v => (law ss).map fun w => v :: w

/-- the value of token t in the list w -/
def gv (w : List Bits) (t : Tok) : Bits := w.getD t []

theorem E_hid (ℓ : ℕ) (F : Bits → ℝ≥0∞) :
    expect (Slot.hid ℓ).draw F =
      expect (PMF.uniformOfFintype (Fin ℓ → Bool)) fun u => F (List.ofFn u) := by
  rw [Slot.draw, expect_map]

theorem E_pub (v : Bits) (F : Bits → ℝ≥0∞) : expect (Slot.pub v).draw F = F v := by
  rw [Slot.draw, expect_pure]

theorem E_nil (F : List Bits → ℝ≥0∞) : expect (law []) F = F [] := by rw [law, expect_pure]

theorem E_cons (s : Slot) (ss : List Slot) (F : List Bits → ℝ≥0∞) :
    expect (law (s :: ss)) F = expect s.draw fun v => expect (law ss) fun w => F (v :: w) := by
  rw [law, expect_bind]
  exact expect_congr _ fun v => expect_map _ _ _

theorem E_snoc (ss : List Slot) (s : Slot) :
    ∀ F : List Bits → ℝ≥0∞, expect (law (ss ++ [s])) F =
      expect (law ss) fun w => expect s.draw fun v => F (w ++ [v]) := by
  induction ss with
  | nil =>
    intro F
    rw [List.nil_append, E_cons, E_nil]
    exact expect_congr _ fun v => E_nil _
  | cons s₀ ss ih =>
    intro F
    rw [List.cons_append, E_cons, E_cons]
    exact expect_congr _ fun v => ih _

/-- a hidden token may be drawn first -/
theorem E_fix (ℓ : ℕ) : ∀ (ss : List Slot) (i : ℕ) (F : List Bits → ℝ≥0∞),
    ss[i]? = some (Slot.hid ℓ) →
    expect (law ss) F = expect (PMF.uniformOfFintype (Fin ℓ → Bool)) fun u =>
      expect (law (ss.set i (Slot.pub (List.ofFn u)))) F := by
  intro ss
  induction ss with
  | nil => intro i F h; simp at h
  | cons s ss ih =>
    intro i F h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [E_cons, E_hid]
      refine expect_congr _ fun u => ?_
      rw [List.set_cons_zero, E_cons, E_pub]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      rw [E_cons]
      simp only [List.set_cons_succ, E_cons]
      exact (expect_congr _ fun v => ih i (fun w => F (v :: w)) h).trans (expect_comm _ _ _)

/-- drawing a hidden token once more does not change the law -/
theorem E_resample (ℓ : ℕ) :
    ∀ (ss : List Slot) (i : ℕ) (F : List Bits → ℝ≥0∞), ss[i]? = some (Slot.hid ℓ) →
    expect (law ss) F = expect (law ss) fun w =>
      expect (PMF.uniformOfFintype (Fin ℓ → Bool)) fun u => F (w.set i (List.ofFn u)) := by
  intro ss
  induction ss with
  | nil => intro i F h; simp at h
  | cons s ss ih =>
    intro i F h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [E_cons, E_cons, E_hid, E_hid]
      simp only [List.set_cons_zero]
      rw [expect_const]
      exact expect_comm _ _ _
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      rw [E_cons, E_cons]
      simp only [List.set_cons_succ]
      exact expect_congr _ fun v => ih i _ h

/-- w is a possible list of values -/
def Agree (ss : List Slot) (w : List Bits) : Prop := List.Forall₂ Slot.Ok ss w

theorem mem_support_draw (s : Slot) (v : Bits) : v ∈ s.draw.support ↔ s.Ok v := by
  cases s with
  | hid ℓ =>
    simp only [Slot.draw, PMF.mem_support_map_iff,
      PMF.mem_support_uniformOfFintype, true_and, Slot.Ok]
    constructor
    · rintro ⟨u, rfl⟩; simp
    · rintro rfl; exact ⟨fun i => v.get i, List.ofFn_get v⟩
  | pub x => simp [Slot.draw, Slot.Ok]

theorem mem_support_law :
    ∀ (ss : List Slot) (w : List Bits), w ∈ (law ss).support ↔ Agree ss w := by
  intro ss
  induction ss with
  | nil => intro w; simp [law, Agree]
  | cons s ss ih =>
    intro w
    simp only [law, PMF.mem_support_bind_iff, PMF.mem_support_map_iff, mem_support_draw, ih, Agree]
    constructor
    · rintro ⟨v, hv, w', hw', rfl⟩; exact List.Forall₂.cons hv hw'
    · intro h
      cases h with
      | cons hv hw' => exact ⟨_, hv, _, hw', rfl⟩

theorem exists_agree (ss : List Slot) : ∃ w, Agree ss w := by
  obtain ⟨w, hw⟩ := (law ss).support_nonempty
  exact ⟨w, (mem_support_law ss w).1 hw⟩

theorem Agree.length {ss : List Slot} {w : List Bits} (h : Agree ss w) : w.length = ss.length :=
  (List.Forall₂.length_eq h).symm

theorem Agree.ok :
    ∀ {ss : List Slot} {w : List Bits},
      Agree ss w → ∀ {i : ℕ} {s : Slot}, ss[i]? = some s → s.Ok (gv w i) := by
  intro ss w h
  induction h with
  | nil => intro i s hs; simp at hs
  | cons hv _ ih =>
    intro i s hs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs; simpa [gv] using hv
    | succ i =>
      simp only [List.getElem?_cons_succ] at hs
      simpa [gv] using ih hs

theorem agree_of_forall : ∀ {ss : List Slot} {w : List Bits}, w.length = ss.length →
    (∀ (i : ℕ) (s : Slot), ss[i]? = some s → s.Ok (gv w i)) → Agree ss w := by
  intro ss
  induction ss with
  | nil =>
    intro w hl _
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact List.Forall₂.nil
  | cons s ss ih =>
    intro w hl h
    cases w with
    | nil => simp at hl
    | cons v w =>
      refine List.Forall₂.cons (by simpa [gv] using h 0 s rfl)
        (ih (by simpa using hl) fun i s' hs' => ?_)
      simpa [gv] using h (i + 1) s' (by simpa using hs')

theorem agree_snoc_fwd {s : Slot} : ∀ {ss : List Slot} {w : List Bits}, Agree (ss ++ [s]) w →
    ∃ w' v, w = w' ++ [v] ∧ Agree ss w' ∧ s.Ok v := by
  intro ss
  induction ss with
  | nil =>
    intro w h
    cases h with
    | cons hv h' =>
      cases h'
      exact ⟨[], _, rfl, List.Forall₂.nil, hv⟩
  | cons s₀ ss ih =>
    intro w h
    cases h with
    | cons hv h' =>
      obtain ⟨w', v, rfl, hw', hv'⟩ := ih h'
      exact ⟨_ :: w', v, rfl, List.Forall₂.cons hv hw', hv'⟩

theorem agree_snoc {ss : List Slot} {s : Slot} {w' : List Bits} {v : Bits}
    (hw' : Agree ss w') (hv : s.Ok v) : Agree (ss ++ [s]) (w' ++ [v]) :=
  List.rel_append hw' (List.Forall₂.cons hv List.Forall₂.nil)

/-! ### Small tools -/

theorem gv_set_same {w : List Bits} {i : ℕ} (h : i < w.length) (v : Bits) :
    gv (w.set i v) i = v := by
  simp [gv, h]

theorem gv_set_ne {w : List Bits} {i j : ℕ} (h : i ≠ j) (v : Bits) : gv (w.set i v) j = gv w j := by
  simp [gv, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem gv_append_left {w : List Bits} {t : ℕ} (h : t < w.length) (z : List Bits) :
    gv (w ++ z) t = gv w t := by
  simp [gv, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gv_append_length (w : List Bits) (v : Bits) : gv (w ++ [v]) w.length = v := by
  simp [gv]

theorem expect_add_const_le {β : Type} (p : PMF β) (X : β → ℝ≥0∞) (c H : ℝ≥0∞)
    (h : ∀ b ∈ p.support, X b + c ≤ H) : expect p X + c ≤ H := by
  have e : expect p X + c = expect p fun b => X b + c := by rw [expect_add, expect_const]
  rw [e]
  exact expect_le_of_forall_le p h

theorem expect_list_sum {β γ : Type} (p : PMF β) (l : List γ) (f : γ → β → ℝ≥0∞) :
    expect p (fun b => (l.map fun c => f c b).sum) = (l.map fun c => expect p (f c)).sum := by
  induction l with
  | nil => simp [expect_zero]
  | cons c l ih => simp only [List.map_cons, List.sum_cons, expect_add, ih]

theorem list_sum_le_count {γ : Type} (l : List γ) (P : γ → Bool) (g : γ → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ b ∈ l, g b ≤ if P b then c else 0) :
    (l.map g).sum ≤ ((l.filter P).length : ℝ≥0∞) * c := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have hl := ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    rw [List.map_cons, List.sum_cons]
    by_cases hP : P b = true
    · rw [List.filter_cons_of_pos hP, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_comm]
      rw [if_pos hP] at hb
      exact add_le_add hl hb
    · rw [List.filter_cons_of_neg hP]
      rw [if_neg hP] at hb
      calc g b + (l.map g).sum ≤ 0 + (l.map g).sum := by gcongr
        _ = (l.map g).sum := zero_add _
        _ ≤ _ := hl

theorem ind_exists_le_sum {γ : Type} (l : List γ) (R : γ → Prop) :
    ind (∃ b ∈ l, R b) ≤ (l.map fun b => ind (R b)).sum := by
  induction l with
  | nil => rw [ind_neg (by simp)]; exact zero_le _
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases hb : R b
    · rw [ind_pos hb]
      exact le_add_right (ind_le_one _)
    · rw [ind_neg hb, zero_add]
      refine le_trans (ind_mono ?_) ih
      rintro ⟨b', hb', hR⟩
      rcases List.mem_cons.1 hb' with rfl | hb''
      · exact absurd hR hb
      · exact ⟨b', hb'', hR⟩

/-- One hidden coordinate. An event that, for every choice of the other values, holds for at most
one value of the hidden token t of L bits has probability at most 2^-L. -/
theorem E_one_le {ss : List Slot} {t L : ℕ} (ht : ss[t]? = some (Slot.hid L)) (G : List Bits → Prop)
    (hG : ∀ w : List Bits, w.length = ss.length → ∀ u u' : Fin L → Bool,
      G (w.set t (List.ofFn u)) → G (w.set t (List.ofFn u')) → u = u') :
    expect (law ss) (fun w => ind (G w)) ≤ 1 / 2 ^ L := by
  classical
  rw [E_resample L ss t _ ht]
  refine expect_le_of_forall_le _ fun w hw => ?_
  have hl := ((mem_support_law ss w).1 hw).length
  have h := pr_unif_le_of_cnt_le
    (C := Fin L → Bool) (P := fun u => G (w.set t (List.ofFn u))) (k := 1) (cnt_le_one (hG w hl))
  rw [pr_eq_expect] at h
  have e : (fun u : Fin L → Bool => ind (G (w.set t (List.ofFn u))))
      = fun u => if u ∈ {c : Fin L → Bool | G (w.set t (List.ofFn c))} then (1 : ℝ≥0∞) else 0 := by
    funext u
    by_cases hu : G (w.set t (List.ofFn u))
    · rw [ind_pos hu]; exact (if_pos (show u ∈ {c : Fin L → Bool | G (w.set t (List.ofFn c))} from hu)).symm
    · rw [ind_neg hu]; exact (if_neg (show u ∉ {c : Fin L → Bool | G (w.set t (List.ofFn c))} from hu)).symm
  rw [e]
  simpa using h

/-- all tokens of ts that are hidden are drawn, one after the other -/
def fixLaw : List Tok → List Slot → PMF (List Slot)
  | [], ss => PMF.pure ss
  | t :: ts, ss =>
      match ss[t]? with
      | some (Slot.hid ℓ) =>
          (PMF.uniformOfFintype (Fin ℓ → Bool)).bind fun u =>
            fixLaw ts (ss.set t (Slot.pub (List.ofFn u)))
      | _ => fixLaw ts ss

theorem E_fixLaw (F : List Bits → ℝ≥0∞) : ∀ (ts : List Tok) (ss : List Slot),
    expect (law ss) F = expect (fixLaw ts ss) fun ss' => expect (law ss') F := by
  intro ts
  induction ts with
  | nil => intro ss; rw [fixLaw, expect_pure]
  | cons t ts ih =>
    intro ss
    rw [fixLaw]
    split
    · rename_i ℓ h
      rw [expect_bind, E_fix ℓ ss t F h]
      exact expect_congr _ fun u => ih _
    · exact ih ss

/-- ss' arises from ss by drawing hidden tokens of ts -/
structure Fixed (ts : List Tok) (ss ss' : List Slot) : Prop where
  length : ss'.length = ss.length
  step : ∀ i, ss'[i]? = ss[i]? ∨ (i ∈ ts ∧ ∃ ℓ, ∃ u : Fin ℓ → Bool, ss[i]? = some (Slot.hid ℓ) ∧
    ss'[i]? = some (Slot.pub (List.ofFn u)))
  done : ∀ i ∈ ts, ∀ ℓ, ss'[i]? ≠ some (Slot.hid ℓ)

theorem fixLaw_support :
    ∀ (ts : List Tok) (ss ss' : List Slot), ss' ∈ (fixLaw ts ss).support → Fixed ts ss ss' := by
  intro ts
  induction ts with
  | nil =>
    intro ss ss' h
    rw [fixLaw, PMF.support_pure, Set.mem_singleton_iff] at h
    subst h
    exact ⟨rfl, fun i => Or.inl rfl, fun i hi => by simp at hi⟩
  | cons t ts ih =>
    intro ss ss' h
    rw [fixLaw] at h
    split at h
    · rename_i ℓ ht
      obtain ⟨u, _, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
      have hf := ih _ _ h
      have htl : t < ss.length := by
        by_contra hc
        rw [List.getElem?_eq_none (not_lt.1 hc)] at ht
        simp at ht
      refine ⟨by rw [hf.length, List.length_set], fun i => ?_, fun i hi ℓ' => ?_⟩
      · by_cases hit : t = i
        · subst hit
          refine Or.inr ⟨List.mem_cons_self, ℓ, u, ht, ?_⟩
          rcases hf.step t with h1 | ⟨_, ℓ', u', h1, _⟩
          · rw [h1, List.getElem?_set_self htl]
          · rw [List.getElem?_set_self htl] at h1; simp at h1
        · rcases hf.step i with h1 | ⟨hi, ℓ', u', h1, h2⟩
          · exact Or.inl (by rw [h1, List.getElem?_set_ne hit])
          · exact Or.inr
              ⟨List.mem_cons_of_mem _ hi, ℓ', u', by rw [← h1, List.getElem?_set_ne hit], h2⟩
      · rcases List.mem_cons.1 hi with rfl | hi'
        · rcases hf.step i with h1 | ⟨_, ℓ'', u', _, h2⟩
          · rw [h1, List.getElem?_set_self htl]; simp
          · rw [h2]; simp
        · exact hf.done i hi' ℓ'
    · rename_i hnot
      have hf := ih _ _ h
      refine ⟨hf.length, fun i => ?_, fun i hi ℓ' => ?_⟩
      · rcases hf.step i with h1 | ⟨hi, r⟩
        · exact Or.inl h1
        · exact Or.inr ⟨List.mem_cons_of_mem _ hi, r⟩
      · rcases List.mem_cons.1 hi with rfl | hi'
        · rcases hf.step i with h1 | ⟨_, ℓ'', u', _, h2⟩
          · rw [h1]; exact fun hc => hnot ℓ' hc
          · rw [h2]; simp
        · exact hf.done i hi' ℓ'

theorem Fixed.agree {ts : List Tok} {ss ss' : List Slot} (h : Fixed ts ss ss')
    {w : List Bits} (hw : Agree ss' w) :
    Agree ss w := by
  refine agree_of_forall (hw.length.trans h.length) fun i s hs => ?_
  rcases h.step i with h1 | ⟨_, ℓ, u, h1, h2⟩
  · exact hw.ok (h1.trans hs)
  · have := hw.ok h2
    rw [h1] at hs
    obtain rfl := Option.some.inj hs
    simp only [Slot.Ok] at this ⊢
    rw [this, List.length_ofFn]

theorem Fixed.pub {ts : List Tok} {ss ss' : List Slot} (h : Fixed ts ss ss') {i : ℕ} {v : Bits}
    (hs : ss[i]? = some (Slot.pub v)) : ss'[i]? = some (Slot.pub v) := by
  rcases h.step i with h1 | ⟨_, ℓ, u, h1, _⟩
  · exact h1.trans hs
  · rw [h1] at hs; simp at hs

theorem Fixed.hid {ts : List Tok} {ss ss' : List Slot} (h : Fixed ts ss ss') {i L : ℕ}
    (hs : ss'[i]? = some (Slot.hid L)) : ss[i]? = some (Slot.hid L) := by
  rcases h.step i with h1 | ⟨_, ℓ, u, _, h2⟩
  · exact h1.symm.trans hs
  · rw [h2] at hs; simp at hs

theorem Fixed.pub_of_mem {ts : List Tok} {ss ss' : List Slot} (h : Fixed ts ss ss') {i : ℕ}
    (hi : i ∈ ts) (hl : i < ss.length) :
    ∃ v, ss'[i]? = some (Slot.pub v) := by
  have hl' : i < ss'.length := by rw [h.length]; exact hl
  cases hs : ss'[i] with
  | hid ℓ => exact absurd (by rw [List.getElem?_eq_getElem hl', hs]) (h.done i hi ℓ)
  | pub v => exact ⟨v, by rw [List.getElem?_eq_getElem hl', hs]⟩

/-! ### The public state -/

/-- a marked evaluation as the public sees it: how its point is made of tokens, and the visible part
of the answer -/
structure SEv (S : OSpec) (sp : Split S) where
  o : S.ι
  charged : Tok
  others : List Tok
  pt : Bits → List Bits → S.Dom o
  inj : ∀ vs, Function.Injective fun v => pt v vs
  vis : sp.Vis o
  tail : Tok
  released : Bool

variable {sp : Split S}

def SEv.point (e : SEv S sp) (w : List Bits) : S.Dom e.o :=
  e.pt (gv w e.charged) (e.others.map (gv w))

def SEv.key (e : SEv S sp) (w : List Bits) : Pt S := ⟨e.o, e.point w⟩

def SEv.inst (e : SEv S sp) (w : List Bits) : Ev S :=
  ⟨e.o, e.point w, (sp.split e.o).symm (e.vis, fun i => (gv w e.tail).getD i false),
    e.charged, e.others, e.tail, e.released⟩

/-- what is public in mode I (while no rule is violated), with a log qs of all points that the
adversary has queried or the challenger has evaluated plainly -/
structure PSt (S : OSpec) (sp : Split S) where
  table : Table S
  slots : List Slot
  shown : List Tok
  evs : List (SEv S sp)
  nPlain : S.ι → ℕ
  qs : List (Pt S)

def PSt.inst (p : PSt S sp) (w : List Bits) : DSt S :=
  ⟨p.table, w, p.shown, p.evs.map fun e => e.inst w, p.nPlain, false⟩

def aCount (evs : List (SEv S sp)) (o : S.ι) : ℕ := (evs.filter fun e => decide (e.o = o)).length
def qCount (qs : List (Pt S)) (o : S.ι) : ℕ := (qs.filter fun k => decide (k.1 = o)).length

/-- the public state is well formed: the shown tokens are those with a public value, the tokens of
every evaluation exist, the charged token is not among the others, and the charged token of an
unreleased evaluation is not shown -/
structure Wf (p : PSt S sp) : Prop where
  shown : ∀ t, t ∈ p.shown ↔ ∃ v, p.slots[t]? = some (Slot.pub v)
  toks : ∀ e ∈ p.evs, e.charged < p.slots.length ∧ (∀ x ∈ e.others, x < p.slots.length) ∧
    e.tail < p.slots.length ∧ e.charged ∉ e.others
  unrel : ∀ e ∈ p.evs, e.released = false → e.charged ∉ p.shown

/-- well formed, and: every entry of the table is logged or is the point of a marked evaluation;
every marked evaluation is at an oracle of os; the charged tokens whose slot is `Slot.hid` are long
enough; the log has at most u o + nPlain o points of o -/
structure Valid (ℓ : S.ι → ℕ) (os : Finset S.ι) (u : S.ι → ℕ) (p : PSt S sp) :
    Prop extends Wf p where
  table : ∀ w,
    Agree p.slots w → ∀ k : Pt S, p.table k.1 k.2 ≠ none → k ∈ p.qs ∨ ∃ e ∈ p.evs, e.key w = k
  len : ∀ e ∈ p.evs, e.o ∈ os ∧ ∀ L, p.slots[e.charged]? = some (Slot.hid L) → ℓ e.o ≤ L
  count : ∀ o, qCount p.qs o ≤ u o + p.nPlain o

theorem map_gv_set {w : List Bits} {c : Tok} {l : List Tok} (h : c ∉ l) (v : Bits) :
    l.map (gv (w.set c v)) = l.map (gv w) :=
  List.map_congr_left fun x hx => gv_set_ne (fun hc => h (by rw [hc]; exact hx)) v

theorem map_gv_append {w : List Bits} {l : List Tok} (h : ∀ x ∈ l, x < w.length) (z : List Bits) :
    l.map (gv (w ++ z)) = l.map (gv w) :=
  List.map_congr_left fun x hx => gv_append_left (h x hx) z

theorem SEv.key_set (e : SEv S sp) {w : List Bits} {t : Tok} (h1 : t ≠ e.charged)
    (h2 : t ∉ e.others) (v : Bits) :
    e.key (w.set t v) = e.key w := by
  simp only [SEv.key, SEv.point, gv_set_ne h1, map_gv_set h2]

theorem SEv.inst_append (e : SEv S sp) {w : List Bits} (h1 : e.charged < w.length)
    (h2 : ∀ x ∈ e.others, x < w.length) (h3 : e.tail < w.length) (z : List Bits) :
    e.inst (w ++ z) = e.inst w := by
  simp only [SEv.inst, SEv.point, gv_append_left h1, gv_append_left h3, map_gv_append h2]

theorem SEv.key_append (e : SEv S sp) {w : List Bits} (h1 : e.charged < w.length)
    (h2 : ∀ x ∈ e.others, x < w.length) (z : List Bits) : e.key (w ++ z) = e.key w := by
  simp only [SEv.key, SEv.point, gv_append_left h1, map_gv_append h2]

/-- under the hypotheses below, a point that is injective in a hidden token of L bits meets a target
that does not depend on this token with probability at most 2^-L -/
theorem point_prob {ss : List Slot} {o : S.ι} (c : Tok) (others : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    (hno : c ∉ others) {L : ℕ} (ht : ss[c]? = some (Slot.hid L)) (k : List Bits → Pt S)
    (hk : ∀ w v, k (w.set c v) = k w) :
    expect (law ss) (fun w => ind ((⟨o, pt (gv w c) (others.map (gv w))⟩ : Pt S) = k w)) ≤
      1 / 2 ^ L := by
  have hc : c < ss.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (not_lt.1 hcon)] at ht
    simp at ht
  refine E_one_le ht _ fun w hl u u' h1 h2 => ?_
  rw [gv_set_same (hl ▸ hc), map_gv_set hno, hk] at h1 h2
  have h3 := h1.trans h2.symm
  have h4 : pt (List.ofFn u) (others.map (gv w)) = pt (List.ofFn u') (others.map (gv w)) :=
    eq_of_heq (Sigma.mk.inj_iff.1 h3).2
  exact List.ofFn_injective (inj _ h4)

theorem inv_pow_le {a b : ℕ} (h : a ≤ b) : (1 : ℝ≥0∞) / 2 ^ b ≤ 1 / 2 ^ a :=
  ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) h) 1

theorem Wf.hid {p : PSt S sp} (hv : Wf p) {t : Tok} (h1 : t < p.slots.length) (h2 : t ∉ p.shown) :
    ∃ L, p.slots[t]? = some (Slot.hid L) := by
  cases hs : p.slots[t] with
  | hid L => exact ⟨L, by rw [List.getElem?_eq_getElem h1, hs]⟩
  | pub v => exact absurd ((hv.shown t).2 ⟨v, by rw [List.getElem?_eq_getElem h1, hs]⟩) h2

theorem expect_ind_false {β : Type} (p : PMF β) (P : β → Prop) (h : ∀ b, ¬ P b) :
    expect p (fun b => ind (P b)) = 0 :=
  (expect_congr _ fun b => ind_neg (h b)).trans (expect_zero p)

/-- From a valid public state (`Valid`): a query or a plain evaluation is a hit with probability at
most (number of marked evaluations of o) / 2^ℓ. -/
theorem hitQ_bound {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) (k : Pt S) :
    expect (law p.slots) (fun w => hitQ (p.inst w).evs k) ≤
      (aCount p.evs k.1 : ℝ≥0∞) * (1 / 2 ^ ℓ k.1) := by
  have h1 : ∀ w,
      hitQ (p.inst w).evs k ≤ (p.evs.map fun e => ind (e.released = false ∧ e.key w = k)).sum := by
    intro w
    refine le_trans (ind_mono ?_)
      (ind_exists_le_sum p.evs fun e => e.released = false ∧ e.key w = k)
    rintro ⟨e', he', hr, hk⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact ⟨e, he, hr, hk⟩
  refine (expect_mono _ h1).trans ?_
  rw [expect_list_sum]
  refine list_sum_le_count _ _ _ _ fun e he => ?_
  by_cases ho : e.o = k.1
  · rw [if_pos (by simpa using ho)]
    by_cases hr : e.released = false
    · obtain ⟨L, hL⟩ := hv.hid (hv.toks e he).1 (hv.unrel e he hr)
      have hp := point_prob e.charged e.others e.pt e.inj (hv.toks e he).2.2.2 hL
        (fun _ => k) (fun _ _ => rfl)
      exact le_trans (expect_mono _ fun w => ind_mono fun hh => hh.2)
        (hp.trans (ho ▸ inv_pow_le ((hv.len e he).2 L hL)))
    · rw [expect_ind_false _ _ fun w hh => hr hh.1]; exact zero_le _
  · rw [if_neg (by simpa using ho), expect_ind_false _ _ fun w hh => ho (congrArg Sigma.fst hh.2)]

/-- Under `Valid` and the rules for t (below): a marked evaluation is a hit with probability at most
(logged points of o + marked evaluations of o) / 2^ℓ. -/
theorem hitM_bound {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) {o : S.ι} (t : Tok) (us : List Tok) (pt : Bits → List Bits → S.Dom o)
    (inj : ∀ vs, Function.Injective fun v => pt v vs) (hno : t ∉ us) {L : ℕ}
    (ht : p.slots[t]? = some (Slot.hid L)) (hL : ℓ o ≤ L)
    (hind : ∀ e ∈ p.evs, e.o = o → t ≠ e.charged ∧ t ∉ e.others) :
    expect (law p.slots)
        (fun w => hitM (p.inst w).table (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩) ≤
      ((qCount p.qs o + aCount p.evs o : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ o) := by
  have h1 : ∀ w ∈ (law p.slots).support,
      hitM (p.inst w).table (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩ ≤
        (p.qs.map fun x => ind ((⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) = x)).sum +
          (p.evs.map fun e => ind ((⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) = e.key w)).sum := by
    intro w hw
    have hw' := (mem_support_law _ _).1 hw
    by_cases hh : (p.inst w).table o (pt (gv w t) (us.map (gv w))) ≠ none ∨
        Unrel (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩
    · have hor : (⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) ∈ p.qs ∨
          ∃ e ∈ p.evs, e.key w = ⟨o, pt (gv w t) (us.map (gv w))⟩ := by
        rcases hh with hT | ⟨e', he', _, hk⟩
        · exact hv.table w hw' _ hT
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
          exact Or.inr ⟨e, he, hk⟩
      rcases hor with hq | ⟨e, he, hk⟩
      · refine le_add_right (le_trans ?_ (ind_exists_le_sum p.qs _))
        rw [ind_pos ⟨_, hq, rfl⟩]; exact ind_le_one _
      · refine le_add_left (le_trans ?_ (ind_exists_le_sum p.evs _))
        rw [ind_pos ⟨e, he, hk.symm⟩]; exact ind_le_one _
    · rw [hitM, ind_neg hh]; exact zero_le _
  refine (expect_mono_support _ h1).trans ?_
  rw [expect_add, expect_list_sum, expect_list_sum, Nat.cast_add, add_mul]
  refine add_le_add (list_sum_le_count _ _ _ _ fun x _ => ?_)
    (list_sum_le_count _ _ _ _ fun e he => ?_)
  · by_cases ho : x.1 = o
    · rw [if_pos (by simpa using ho)]
      exact (point_prob t us pt inj hno ht (fun _ => x) fun _ _ => rfl).trans (inv_pow_le hL)
    · rw [if_neg (by simpa using ho),
        expect_ind_false _ _ fun w hh => ho (congrArg Sigma.fst hh).symm]
  · by_cases ho : e.o = o
    · rw [if_pos (by simpa using ho)]
      exact (point_prob t us pt inj hno ht (fun w => e.key w)
        fun w v => e.key_set (hind e he ho).1 (hind e he ho).2 v).trans (inv_pow_le hL)
    · rw [if_neg (by simpa using ho),
        expect_ind_false _ _ fun w hh => ho (congrArg Sigma.fst hh).symm]

/-! ### The potential -/

/-- Σ over the oracles of os of a (b + a) / 2^ℓ, for `a` marked evaluations and `b` logged points -/
def pot (ℓ : S.ι → ℕ) (os : Finset S.ι) (a b : S.ι → ℕ) : ℝ≥0∞ :=
  ∑ o ∈ os, ((a o * (b o + a o) : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ o)

theorem sum_bump {ι : Type} [DecidableEq ι] (os : Finset ι) (f f' : ι → ℝ≥0∞) {o₀ : ι}
    (h₀ : o₀ ∈ os) (c : ℝ≥0∞) (h1 : c + f o₀ ≤ f' o₀) (h2 : ∀ o ∈ os, o ≠ o₀ → f o ≤ f' o) :
    c + ∑ o ∈ os, f o ≤ ∑ o ∈ os, f' o := by
  rw [← Finset.add_sum_erase os f h₀, ← Finset.add_sum_erase os f' h₀, ← add_assoc]
  exact add_le_add h1
    (Finset.sum_le_sum fun o ho => h2 o (Finset.mem_of_mem_erase ho) (Finset.ne_of_mem_erase ho))

theorem pot_bump_b (ℓ : S.ι → ℕ) (os : Finset S.ι) (a b : S.ι → ℕ) {o₀ : S.ι} (h₀ : o₀ ∈ os) :
    (a o₀ : ℝ≥0∞) * (1 / 2 ^ ℓ o₀) + pot ℓ os a b ≤
      pot ℓ os a (Function.update b o₀ (b o₀ + 1)) := by
  refine sum_bump os _ _ h₀ _ ?_ fun o _ hne => ?_
  · rw [Function.update_self, ← add_mul]
    gcongr
    exact_mod_cast (by nlinarith : a o₀ + a o₀ * (b o₀ + a o₀) ≤ a o₀ * (b o₀ + 1 + a o₀))
  · rw [Function.update_of_ne hne]

theorem pot_bump_a (ℓ : S.ι → ℕ) (os : Finset S.ι) (a b : S.ι → ℕ) {o₀ : S.ι} (h₀ : o₀ ∈ os) :
    ((b o₀ + a o₀ : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ o₀) + pot ℓ os a b ≤
      pot ℓ os (Function.update a o₀ (a o₀ + 1)) b := by
  refine sum_bump os _ _ h₀ _ ?_ fun o _ hne => ?_
  · rw [Function.update_self, ← add_mul]
    gcongr
    exact_mod_cast (by
      nlinarith : b o₀ + a o₀ + a o₀ * (b o₀ + a o₀) ≤ (a o₀ + 1) * (b o₀ + (a o₀ + 1)))
  · rw [Function.update_of_ne hne]

theorem qCount_cons (k : Pt S) (qs : List (Pt S)) :
    qCount (k :: qs) = Function.update (qCount qs) k.1 (qCount qs k.1 + 1) := by
  funext o
  by_cases h : o = k.1
  · subst h; simp [qCount]
  · rw [Function.update_of_ne h]
    simp [qCount, Ne.symm h]

theorem aCount_snoc (evs : List (SEv S sp)) (e : SEv S sp) :
    aCount (evs ++ [e]) = Function.update (aCount evs) e.o (aCount evs e.o + 1) := by
  funext o
  by_cases h : o = e.o
  · subst h; simp [aCount, List.filter_append]
  · rw [Function.update_of_ne h]
    simp [aCount, List.filter_append, Ne.symm h]

/-- the potential of a public state -/
def PSt.pot (ℓ : S.ι → ℕ) (os : Finset S.ι) (p : PSt S sp) : ℝ≥0∞ :=
  DeferTail.pot ℓ os (aCount p.evs) (qCount p.qs)

/-! ### What the hypothesis on the final states gives on the way -/

section Bound
variable (e M ℓ : S.ι → ℕ) (os : Finset S.ι)

/-- some d' with `Ext d d'` satisfies `DSt.Within e M ℓ os` -/
def EvW (d : DSt S) : Prop := ∃ d', Ext d d' ∧ d'.Within e M ℓ os

variable {e M ℓ os}

theorem EvW.mono {d d₁ : DSt S} (h : Ext d d₁) (h₁ : EvW e M ℓ os d₁) : EvW e M ℓ os d := by
  obtain ⟨d', h', hw⟩ := h₁
  exact ⟨d', h.trans h', hw⟩

theorem EvW.viol {d : DSt S} (h : EvW e M ℓ os d) : d.viol = false := by
  obtain ⟨d', h', hw⟩ := h
  by_contra hc
  have := h'.viol (by simpa using hc)
  rw [hw.1] at this
  simp at this

theorem EvW.ev {d : DSt S} (h : EvW e M ℓ os d) (v : Ev S) (hv : v ∈ d.evs) :
    v.o ∈ os ∧ (v.charged < d.vals.length → ℓ v.o ≤ (d.val v.charged).length) := by
  obtain ⟨d', h', hw⟩ := h
  have h1 : skel v ∈ d'.evs.map skel := h'.evs.subset (List.mem_map_of_mem hv)
  obtain ⟨v', hv', hs⟩ := List.mem_map.1 h1
  have ho : v'.o = v.o := congrArg Prod.fst hs
  have hc : v'.charged = v.charged := congrArg Prod.snd hs
  have h2 := hw.2.2.2 v' hv'
  rw [ho, hc] at h2
  refine ⟨h2.1, fun hl => ?_⟩
  obtain ⟨z, hz⟩ := h'.vals
  have : d'.val v.charged = d.val v.charged := by
    show gv d'.vals _ = gv d.vals _
    rw [← hz, gv_append_left hl]
  rw [← this]
  exact h2.2

theorem evw_of_safe {α : Type} {Q : α × DSt S → Prop} (hQ : ∀ y, Q y → EvW e M ℓ os y.2)
    (c : Step S sp α) (d : DSt S) (hs : ∀ y ∈ (c.run true d).support, Q y) : EvW e M ℓ os d := by
  obtain ⟨y, hy⟩ := (c.run true d).support_nonempty
  exact EvW.mono (run_ext c d y hy) (hQ y (hs y hy))

end Bound

/-! ### Reading the flags -/

theorem markedBad_false {d : DSt S} {o : S.ι} {t : Tok}
    {us : List Tok} (h : markedBad d o t us = false) :
    t < d.vals.length ∧ (∀ x ∈ us, x < d.vals.length) ∧ t ∉ us ∧ t ∉ d.shown ∧
    ∀ v ∈ d.evs, v.o = o → v.charged ≠ t ∧ t ∉ v.others := by
  simp only [markedBad, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le,
    List.any_eq_false, List.contains_eq_mem, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, not_and, not_or] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem closedUnder_true {shown : List Tok} {evs : List (Ev S)} (h : closedUnder shown evs = true) :
    ∀ v ∈ evs, v.released = true → v.tail ∈ shown ∧ ∀ x ∈ v.others, x ∈ shown := by
  intro v hv hr
  simp only [closedUnder, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rcases h v hv with h1 | h1
  · rw [hr] at h1; simp at h1
  · exact h1

theorem postReveal_viol {d : DSt S} {ts : List Tok} (h : (postReveal true d ts).viol = false) :
    closedUnder (d.shown ++ ts) (d.evs.map (rel1 (d.shown ++ ts))) = true ∧
    ∀ x ∈ ts, x < d.vals.length := by
  simp only [postReveal, releaseAll_fst, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not,
    Bool.not_false, List.any_eq_false, decide_eq_true_eq, not_le] at h
  exact ⟨h.1.2, h.2⟩

theorem lazy_support {T : Table S} {o : S.ι} {q : S.Dom o} {y : S.Rng o × Table S}
    (hy : y ∈ (lazyAnswer T o q).support) (k : Pt S) (hk : y.2 k.1 k.2 ≠ none) :
    T k.1 k.2 ≠ none ∨ k = ⟨o, q⟩ := by
  cases hT : T o q with
  | some r =>
    rw [lazyAnswer_some hT, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact Or.inl hk
  | none =>
    rw [lazyAnswer_none hT, PMF.mem_support_map_iff] at hy
    obtain ⟨r, _, rfl⟩ := hy
    by_cases hkq : k = ⟨o, q⟩
    · exact Or.inr hkq
    · left
      have hk' : (T.set o q r) k.1 k.2 ≠ none := hk
      rwa [set_ne T o q r k.1 k.2 hkq] at hk'

/-! ### The public state after each operation -/

/-- after a query or a plain evaluation at k -/
def PSt.log (p : PSt S sp) (k : Pt S) (T : Table S) (nP : S.ι → ℕ) : PSt S sp :=
  ⟨T, p.slots, p.shown, p.evs, nP, k :: p.qs⟩

theorem valid_log {ℓ : S.ι → ℕ} {os : Finset S.ι} {u u' : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) (k : Pt S) (T : Table S) (nP : S.ι → ℕ)
    (hT : ∀ k' : Pt S, T k'.1 k'.2 ≠ none → p.table k'.1 k'.2 ≠ none ∨ k' = k)
    (hc : ∀ o, qCount (k :: p.qs) o ≤ u' o + nP o) :
    Valid ℓ os u' (p.log k T nP) := by
  refine ⟨⟨hv.shown, hv.toks, hv.unrel⟩, fun w hw k' hk' => ?_, hv.len, hc⟩
  rcases hT k' hk' with h | rfl
  · rcases hv.table w hw k' h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · exact Or.inr h'
  · exact Or.inl List.mem_cons_self

theorem aCount_eq_zero {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) {o : S.ι} (ho : o ∉ os) : aCount p.evs o = 0 := by
  rw [aCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx hxo
  exact ho ((of_decide_eq_true hxo) ▸ (hv.len x hx).1)

theorem pot_log_le {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) (k : Pt S) (T : Table S) (nP : S.ι → ℕ) :
    (aCount p.evs k.1 : ℝ≥0∞) * (1 / 2 ^ ℓ k.1) + p.pot ℓ os ≤ (p.log k T nP).pot ℓ os := by
  show _ + pot ℓ os (aCount p.evs) (qCount p.qs) ≤ pot ℓ os (aCount p.evs) (qCount (k :: p.qs))
  rw [qCount_cons]
  by_cases ho : k.1 ∈ os
  · exact pot_bump_b ℓ os _ _ ho
  · rw [aCount_eq_zero hv ho, Nat.cast_zero, zero_mul, zero_add]
    refine le_of_eq (Finset.sum_congr rfl fun o' ho' => ?_)
    rw [Function.update_of_ne fun h => ho (by rw [← h]; exact ho')]

/-- after a new hidden token -/
def PSt.snoc (p : PSt S sp) (L : ℕ) : PSt S sp :=
  ⟨p.table, p.slots ++ [Slot.hid L], p.shown, p.evs, p.nPlain, p.qs⟩

theorem getElem?_snoc_pub (ss : List Slot) (L t : ℕ) (v : Bits) :
    (ss ++ [Slot.hid L])[t]? = some (Slot.pub v) ↔ ss[t]? = some (Slot.pub v) := by
  rcases lt_trichotomy t ss.length with h | h | h
  · rw [List.getElem?_append_left h]
  · subst h; simp
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem wf_snoc {p : PSt S sp} (hv : Wf p) (L : ℕ) : Wf (p.snoc L) := by
  refine ⟨fun t => ?_, fun x hx => ?_, hv.unrel⟩
  · exact (hv.shown t).trans (exists_congr fun v => (getElem?_snoc_pub _ _ _ _).symm)
  · obtain ⟨h1, h2, h3, h4⟩ := hv.toks x hx
    have hl : (p.snoc L).slots.length = p.slots.length + 1 := by simp [PSt.snoc]
    rw [hl]
    exact ⟨Nat.lt_succ_of_lt h1, fun y hy => Nat.lt_succ_of_lt (h2 y hy), Nat.lt_succ_of_lt h3, h4⟩

theorem valid_snoc {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) (L : ℕ) : Valid ℓ os u (p.snoc L) := by
  refine ⟨wf_snoc hv.toWf L, fun w hw k hk => ?_,
    fun x hx => ⟨(hv.len x hx).1, fun L' h => ?_⟩, hv.count⟩
  · obtain ⟨w', v, rfl, hw', _⟩ := agree_snoc_fwd hw
    rcases hv.table w' hw' k hk with h | ⟨x, hx, hk'⟩
    · exact Or.inl h
    · obtain ⟨h1, h2, _, _⟩ := hv.toks x hx
      refine Or.inr ⟨x, hx, ?_⟩
      rw [x.key_append (hw'.length ▸ h1) (fun y hy => hw'.length ▸ h2 y hy)]
      exact hk'
  · refine (hv.len x hx).2 L' ?_
    rwa [show (p.snoc L).slots = p.slots ++ [Slot.hid L] from rfl,
      List.getElem?_append_left (hv.toks x hx).1] at h

theorem inst_snoc {p : PSt S sp} (hv : Wf p)
    {w : List Bits} (hw : Agree p.slots w) (v : Bits) :
    (p.evs.map fun x => x.inst (w ++ [v])) = p.evs.map fun x => x.inst w :=
  List.map_congr_left fun x hx => by
    obtain ⟨h1, h2, h3, _⟩ := hv.toks x hx
    exact x.inst_append (hw.length ▸ h1) (fun y hy => hw.length ▸ h2 y hy) (hw.length ▸ h3) _

/-- the answer of an oracle is a visible part and, independently, a uniform tail -/
theorem E_split (sp : Split S) (o : S.ι) :
    ∃ μ : PMF (sp.Vis o), ∀ X : sp.Vis o × (Fin (sp.tl o) → Bool) → ℝ≥0∞,
      expect (PMF.uniformOfFintype (S.Rng o)) (fun r => X (sp.split o r)) =
        expect μ fun vis =>
          expect (PMF.uniformOfFintype (Fin (sp.tl o) → Bool)) fun u => X (vis, u) := by
  classical
  haveI : Finite (sp.Vis o) :=
    Finite.of_surjective (fun r => (sp.split o r).1) fun v =>
      ⟨(sp.split o).symm (v, fun _ => false), by simp⟩
  haveI : Fintype (sp.Vis o) := Fintype.ofFinite _
  haveI : Nonempty (sp.Vis o) := ⟨(sp.split o (Classical.arbitrary _)).1⟩
  refine ⟨PMF.uniformOfFintype (sp.Vis o), fun X => ?_⟩
  rw [← expect_prod, ← unif_prod, ← map_unif_equiv (sp.split o), expect_map]

theorem DSt.ext' {d d' : DSt S} (h1 : d.table = d'.table)
    (h2 : d.vals = d'.vals) (h3 : d.shown = d'.shown) (h4 : d.evs = d'.evs)
    (h5 : d.nPlain = d'.nPlain) (h6 : d.viol = d'.viol) : d = d' := by
  cases d; cases d'; simp_all

/-- after a marked evaluation x -/
def PSt.mark (p : PSt S sp) (x : SEv S sp) : PSt S sp :=
  ⟨p.table, p.slots ++ [Slot.hid (sp.tl x.o)], p.shown, p.evs ++ [x], p.nPlain, p.qs⟩

theorem wf_mark {p : PSt S sp} (hv : Wf p) (x : SEv S sp) (h1 : x.charged < p.slots.length)
    (h2 : ∀ y ∈ x.others, y < p.slots.length) (h3 : x.tail = p.slots.length)
    (h4 : x.charged ∉ x.others) (h5 : x.charged ∉ p.shown) : Wf (p.mark x) := by
  have hs := wf_snoc hv (sp.tl x.o)
  have hl : (p.mark x).slots.length = p.slots.length + 1 := by simp [PSt.mark]
  refine ⟨hs.shown, fun y hy => ?_, fun y hy hr => ?_⟩
  · rcases List.mem_append.1 hy with hy | hy
    · exact hs.toks y hy
    · obtain rfl := List.mem_singleton.1 hy
      rw [hl]
      exact ⟨Nat.lt_succ_of_lt h1, fun z hz => Nat.lt_succ_of_lt (h2 z hz),
        by rw [h3]; exact Nat.lt_succ_self _, h4⟩
  · rcases List.mem_append.1 hy with hy | hy
    · exact hs.unrel y hy hr
    · obtain rfl := List.mem_singleton.1 hy
      exact h5

theorem valid_mark {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
    (hv : Valid ℓ os u p) (x : SEv S sp) (h1 : x.charged < p.slots.length)
    (h2 : ∀ y ∈ x.others, y < p.slots.length) (h3 : x.tail = p.slots.length)
    (h4 : x.charged ∉ x.others) (h5 : x.charged ∉ p.shown) (h6 : x.o ∈ os)
    (h7 : ∀ L, p.slots[x.charged]? = some (Slot.hid L) → ℓ x.o ≤ L) : Valid ℓ os u (p.mark x) := by
  have hs := valid_snoc hv (sp.tl x.o)
  refine ⟨wf_mark hv.toWf x h1 h2 h3 h4 h5, fun w hw k hk => ?_, fun y hy => ?_, hs.count⟩
  · rcases hs.table w hw k hk with h | ⟨y, hy, hk'⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, List.mem_append_left _ hy, hk'⟩
  · rcases List.mem_append.1 hy with hy | hy
    · exact hs.len y hy
    · obtain rfl := List.mem_singleton.1 hy
      refine ⟨h6, fun L h => h7 L ?_⟩
      rwa [show (p.mark y).slots = p.slots ++ [Slot.hid (sp.tl y.o)] from rfl,
        List.getElem?_append_left h1] at h

theorem inst_mark {p : PSt S sp} (hv : Wf p) {w : List Bits} (hw : Agree p.slots w) (o : S.ι)
    (t : Tok) (us : List Tok) (pt : Bits → List Bits → S.Dom o)
    (inj : ∀ vs, Function.Injective fun v => pt v vs) (r : S.Rng o)
    (hb : markedBad (p.inst w) o t us = false) :
    postMarked sp (p.inst w) o t us
        (pt ((p.inst w).val t) (us.map (p.inst w).val)) r (p.inst w).table =
      (p.mark ⟨o, t, us, pt, inj, (sp.split o r).1, p.slots.length, false⟩).inst
        (w ++ [List.ofFn (sp.split o r).2]) := by
  obtain ⟨ht, hus, _, _, _⟩ := markedBad_false hb
  have ht' : t < w.length := ht
  have hus' : ∀ x ∈ us, x < w.length := hus
  have hfun : (fun i : Fin (sp.tl o) => (List.ofFn (sp.split o r).2).getD (i : ℕ) false) =
      (sp.split o r).2 := by
    funext i; simp
  have e2 : (⟨o, t, us, pt, inj, (sp.split o r).1, p.slots.length, false⟩ : SEv S sp).inst
        (w ++ [List.ofFn (sp.split o r).2]) =
      ⟨o, pt (gv w t) (us.map (gv w)), r, t, us, w.length, false⟩ := by
    simp only [SEv.inst, SEv.point]
    rw [gv_append_left ht', map_gv_append hus', ← hw.length, gv_append_length, hfun, Prod.mk.eta,
      Equiv.symm_apply_apply]
  refine DSt.ext' rfl rfl rfl ?_ rfl ?_
  · show (p.evs.map fun x => x.inst w) ++
        [⟨o, pt (gv w t) (us.map (gv w)), r, t, us, w.length, false⟩] =
      (p.evs ++ [(⟨o, t, us, pt, inj, (sp.split o r).1, p.slots.length, false⟩ : SEv S sp)]).map
        fun x => x.inst (w ++ [List.ofFn (sp.split o r).2])
    rw [List.map_append, inst_snoc hv hw, List.map_singleton, e2]
  · show (false || markedBad (p.inst w) o t us) = false
    rw [hb]; rfl

/-! the reveal -/

def SNewly (shown : List Tok) (x : SEv S sp) : Prop :=
  x.released = false ∧ shown.contains x.charged = true

def srel (shown : List Tok) (x : SEv S sp) : SEv S sp :=
  if !x.released && shown.contains x.charged then { x with released := true } else x

theorem srel_cases (shown : List Tok) (x : SEv S sp) :
    (¬ SNewly shown x ∧ srel shown x = x) ∨
    (SNewly shown x ∧ srel shown x = { x with released := true }) := by
  by_cases h : (!x.released && shown.contains x.charged) = true
  · right
    exact ⟨by simpa [SNewly] using h, by rw [srel, if_pos h]⟩
  · left
    exact ⟨by simpa [SNewly] using h, by rw [srel, if_neg h]⟩

theorem srel_inst (shown : List Tok) (x : SEv S sp) (w : List Bits) :
    rel1 shown (x.inst w) = (srel shown x).inst w := by
  rcases srel_cases shown x with ⟨hn, he⟩ | ⟨hn, he⟩
  · rw [he, rel1_of_not_newly (show ¬ Newly shown (x.inst w) from hn)]
  · rw [he, rel1_of_newly (show Newly shown (x.inst w) from hn)]
    rfl

theorem srel_key (shown : List Tok) (x : SEv S sp) (w : List Bits) :
    (srel shown x).key w = x.key w := by
  rcases srel_cases shown x with ⟨_, he⟩ | ⟨_, he⟩
  · rw [he]
  · rw [he]; rfl

theorem srel_toks (shown : List Tok) (x : SEv S sp) :
    (srel shown x).o = x.o ∧ (srel shown x).charged = x.charged ∧ (srel shown x).others = x.others ∧
      (srel shown x).tail = x.tail := by
  rcases srel_cases shown x with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he] <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem aCount_srel (shown : List Tok) (evs : List (SEv S sp)) :
    aCount (evs.map (srel shown)) = aCount evs := by
  funext o
  induction evs with
  | nil => rfl
  | cons x xs ih =>
    simp only [aCount] at ih ⊢
    rw [List.map_cons]
    by_cases h : x.o = o
    · rw [List.filter_cons_of_pos (by simpa [(srel_toks shown x).1] using h),
        List.filter_cons_of_pos (by simpa using h), List.length_cons, List.length_cons, ih]
    · rw [List.filter_cons_of_neg (by simpa [(srel_toks shown x).1] using h),
        List.filter_cons_of_neg (by simpa using h), ih]

def Slot.val0 : Slot → Bits
  | .hid _ => []
  | .pub v => v

theorem gv_val0 {ss : List Slot} {t : ℕ} {v : Bits} (h : ss[t]? = some (Slot.pub v)) :
    gv (ss.map Slot.val0) t = v := by
  simp [gv, List.getD_eq_getElem?_getD, List.getElem?_map, h, Slot.val0]

theorem SEv.inst_congr (x : SEv S sp) {w w₀ : List Bits} (h1 : gv w x.charged = gv w₀ x.charged)
    (h2 : ∀ y ∈ x.others, gv w y = gv w₀ y) (h3 : gv w x.tail = gv w₀ x.tail) :
    x.inst w = x.inst w₀ := by
  simp only [SEv.inst, SEv.point, h1, h3, List.map_congr_left h2]

theorem releaseAll_congr (shown : List Tok) (w w₀ : List Bits) :
    ∀ (evs : List (SEv S sp)) (T : Table S), (∀ x ∈ evs, SNewly shown x → x.inst w = x.inst w₀) →
      (releaseAll true shown (evs.map fun x => x.inst w) T).2 =
        (releaseAll true shown (evs.map fun x => x.inst w₀) T).2 := by
  intro evs
  induction evs with
  | nil => intro T _; rfl
  | cons x xs ih =>
    intro T h
    have hxs : ∀ y ∈ xs, SNewly shown y → y.inst w = y.inst w₀ := fun y hy =>
      h y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, List.map_cons]
    by_cases hn : SNewly shown x
    · rw [releaseAll_cons_newly true (show Newly shown (x.inst w) from hn),
        releaseAll_cons_newly true (show Newly shown (x.inst w₀) from hn)]
      show (releaseAll true shown _ (wr T (x.inst w))).2 =
        (releaseAll true shown _ (wr T (x.inst w₀))).2
      rw [h x List.mem_cons_self hn]
      exact ih _ hxs
    · rw [releaseAll_cons_not true (show ¬ Newly shown (x.inst w) from hn),
        releaseAll_cons_not true (show ¬ Newly shown (x.inst w₀) from hn)]
      exact ih _ hxs

/-- after a reveal of ts, when the hidden tokens of ts have been drawn (ss') -/
def PSt.reveal (p : PSt S sp) (ts : List Tok) (ss' : List Slot) : PSt S sp :=
  ⟨(releaseAll true (p.shown ++ ts) (p.evs.map fun x => x.inst (ss'.map Slot.val0)) p.table).2,
    ss', p.shown ++ ts, p.evs.map (srel (p.shown ++ ts)), p.nPlain, p.qs⟩

/-- the rules hold at a reveal of ts: what is public about it -/
structure RevOK (p : PSt S sp) (ts : List Tok) : Prop where
  closed : ∀ x ∈ p.evs, (srel (p.shown ++ ts) x).released = true →
    x.tail ∈ p.shown ++ ts ∧ ∀ y ∈ x.others, y ∈ p.shown ++ ts
  exist : ∀ t ∈ ts, t < p.slots.length

theorem revOK_of_viol {p : PSt S sp} {ts : List Tok} {w : List Bits} (hw : Agree p.slots w)
    (h : (postReveal true (p.inst w) ts).viol = false) : RevOK p ts := by
  obtain ⟨h1, h2⟩ := postReveal_viol h
  refine ⟨fun x hx hr => ?_, fun t ht => hw.length ▸ h2 t ht⟩
  have hm : rel1 (p.shown ++ ts) (x.inst w) ∈ (p.inst w).evs.map (rel1 ((p.inst w).shown ++ ts)) :=
    List.mem_map_of_mem (List.mem_map_of_mem hx)
  have := closedUnder_true h1 _ hm (by rw [srel_inst]; exact hr)
  rw [srel_inst] at this
  obtain ⟨_, _, ho, ht⟩ := srel_toks (p.shown ++ ts) x
  exact ⟨ht ▸ this.1, ho ▸ this.2⟩

section Reveal
variable {ℓ : S.ι → ℕ} {os : Finset S.ι} {u : S.ι → ℕ} {p : PSt S sp}
  {ts : List Tok} {ss' : List Slot}

theorem shown_pub (hv : Wf p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts) {t : Tok}
    (ht : t ∈ p.shown ++ ts) : ∃ v, ss'[t]? = some (Slot.pub v) := by
  rcases List.mem_append.1 ht with h | h
  · obtain ⟨v, hv'⟩ := (hv.shown t).1 h
    exact ⟨v, hf.pub hv'⟩
  · exact hf.pub_of_mem h (hr.exist t h)

theorem gv_eq_val0 (hv : Wf p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts) {w : List Bits}
    (hw : Agree ss' w) {t : Tok} (ht : t ∈ p.shown ++ ts) : gv w t = gv (ss'.map Slot.val0) t := by
  obtain ⟨v, h⟩ := shown_pub hv hf hr ht
  rw [gv_val0 h]
  exact hw.ok h

theorem newly_inst (hv : Wf p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts) {w : List Bits}
    (hw : Agree ss' w) (x : SEv S sp) (hx : x ∈ p.evs) (hn : SNewly (p.shown ++ ts) x) :
    x.inst w = x.inst (ss'.map Slot.val0) := by
  have hrel : (srel (p.shown ++ ts) x).released = true := by
    rcases srel_cases (p.shown ++ ts) x with ⟨h, _⟩ | ⟨_, he⟩
    · exact absurd hn h
    · rw [he]
  obtain ⟨h1, h2⟩ := hr.closed x hx hrel
  have hc : x.charged ∈ p.shown ++ ts := by simpa using hn.2
  exact x.inst_congr (gv_eq_val0 hv hf hr hw hc) (fun y hy => gv_eq_val0 hv hf hr hw (h2 y hy))
    (gv_eq_val0 hv hf hr hw h1)

theorem inst_reveal (hv : Wf p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts) {w : List Bits}
    (hw : Agree ss' w) (hviol : (postReveal true (p.inst w) ts).viol = false) :
    postReveal true (p.inst w) ts = (p.reveal ts ss').inst w := by
  refine DSt.ext' ?_ rfl rfl ?_ rfl hviol
  · exact releaseAll_congr _ _ _ _ _ fun x hx hn => newly_inst hv hf hr hw x hx hn
  · show (releaseAll true (p.shown ++ ts) (p.evs.map fun x => x.inst w) p.table).1
      = (p.evs.map (srel (p.shown ++ ts))).map fun x => x.inst w
    rw [releaseAll_fst, List.map_map, List.map_map]
    exact List.map_congr_left fun x _ => srel_inst _ x w

theorem wf_reveal (hv : Wf p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts) :
    Wf (p.reveal ts ss') := by
  refine ⟨fun t => ⟨fun ht => shown_pub hv hf hr ht, fun ⟨v, h⟩ => ?_⟩,
    fun y hy => ?_, fun y hy hrel => ?_⟩
  · rcases hf.step t with h1 | ⟨h1, _⟩
    · exact List.mem_append_left _ ((hv.shown t).2 ⟨v, h1.symm.trans h⟩)
    · exact List.mem_append_right _ h1
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    obtain ⟨_, hc, ho, ht⟩ := srel_toks (p.shown ++ ts) x
    rw [hc, ho, ht, show (p.reveal ts ss').slots.length = p.slots.length from hf.length]
    exact hv.toks x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    rcases srel_cases (p.shown ++ ts) x with ⟨hn, he⟩ | ⟨_, he⟩
    · rw [he] at hrel ⊢
      intro hc
      have hc' : x.charged ∈ p.shown ++ ts := hc
      exact hn ⟨hrel, by simpa using hc'⟩
    · rw [he] at hrel; simp at hrel

theorem valid_reveal (hv : Valid ℓ os u p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts) :
    Valid ℓ os u (p.reveal ts ss') := by
  refine ⟨wf_reveal hv.toWf hf hr, fun w hw k hk => ?_, fun y hy => ?_, hv.count⟩
  · have hT : (p.reveal ts ss').table
        = (releaseAll true (p.shown ++ ts) (p.evs.map fun x => x.inst w) p.table).2 :=
      (releaseAll_congr _ _ _ _ _ fun x hx hn => newly_inst hv.toWf hf hr hw x hx hn).symm
    rw [hT] at hk
    by_cases hex : ∃ x ∈ p.evs, SNewly (p.shown ++ ts) x ∧ x.key w = k
    · obtain ⟨x, hx, _, hk'⟩ := hex
      exact Or.inr ⟨srel _ x, List.mem_map_of_mem hx, by rw [srel_key]; exact hk'⟩
    · rw [releaseAll_snd_other _ _ k.1 k.2 _ fun e' he' hn' hk' => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
        exact hex ⟨x, hx, hn', hk'⟩] at hk
      rcases hv.table w (hf.agree hw) k hk with h | ⟨x, hx, hk'⟩
      · exact Or.inl h
      · exact Or.inr ⟨srel _ x, List.mem_map_of_mem hx, by rw [srel_key]; exact hk'⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    obtain ⟨ho, hc, _, _⟩ := srel_toks (p.shown ++ ts) x
    rw [ho, hc]
    exact ⟨(hv.len x hx).1, fun L h => (hv.len x hx).2 L (hf.hid h)⟩

end Reveal

/-! ### The bound for a step -/

theorem ok_hid {L : ℕ} {v : Bits} (h : (Slot.hid L).Ok v) :
    ∃ u : Fin L → Bool, List.ofFn u = v := by
  obtain rfl : v.length = L := h
  exact ⟨fun i => v.get i, List.ofFn_get v⟩

theorem count_bump_right {qs : List (Pt S)} (k : Pt S)
    {a b : S.ι → ℕ} (h : ∀ o, qCount qs o ≤ a o + b o) :
    ∀ o, qCount (k :: qs) o ≤ a o + Function.update b k.1 (b k.1 + 1) o := by
  intro o
  rw [qCount_cons]
  by_cases ho : o = k.1
  · subst ho
    rw [Function.update_self, Function.update_self]
    have := h k.1
    omega
  · rw [Function.update_of_ne ho, Function.update_of_ne ho]
    exact h o

theorem count_bump_left {qs : List (Pt S)} (k : Pt S)
    {a b : S.ι → ℕ} (h : ∀ o, qCount qs o ≤ a o + b o) :
    ∀ o, qCount (k :: qs) o ≤ Function.update a k.1 (a k.1 + 1) o + b o := by
  intro o
  rw [qCount_cons]
  by_cases ho : o = k.1
  · subst ho
    rw [Function.update_self, Function.update_self]
    have := h k.1
    omega
  · rw [Function.update_of_ne ho, Function.update_of_ne ho]
    exact h o

theorem inst_fresh {p : PSt S sp} (hv : Wf p)
    {w : List Bits} (hw : Agree p.slots w) (L : ℕ) (v : Bits) :
    postFresh (p.inst w) v = (p.snoc L).inst (w ++ [v]) :=
  DSt.ext' rfl rfl rfl (inst_snoc hv hw v).symm rfl rfl

section Main
variable {e M ℓ : S.ι → ℕ} {os : Finset S.ι}

theorem step_bound {α : Type} (u : S.ι → ℕ) (H : ℝ≥0∞) (K : α × DSt S → ℝ≥0∞) (Q : α × DSt S → Prop)
    (hQ : ∀ y, Q y → EvW e M ℓ os y.2)
    (hK : ∀ (a : α) (p : PSt S sp), Valid ℓ os u p → (∀ w, Agree p.slots w → Q (a, p.inst w)) →
      expect (law p.slots) (fun w => K (a, p.inst w)) + p.pot ℓ os ≤ H)
    (c : Step S sp α) :
    ∀ p : PSt S sp, Valid ℓ os u p →
      (∀ w, Agree p.slots w → ∀ y ∈ (c.run true (p.inst w)).support, Q y) →
      expect (law p.slots) (fun w => cost c (p.inst w) K) + p.pot ℓ os ≤ H := by
  induction c with
  | pure a =>
    intro p hv hs
    simp only [cost]
    exact hK a p hv fun w hw =>
      hs w hw _ (by rw [run_pure]; exact (PMF.mem_support_pure_iff _ _).2 rfl)
  | sample n k ih =>
    intro p hv hs
    simp only [cost]
    rw [expect_comm]
    refine expect_add_const_le _ _ _ _ fun r _ => ih r p hv fun w hw y hy => hs w hw y ?_
    rw [run_sample]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hy⟩
  | plain o q k ih =>
    intro p hv hs
    simp only [cost]
    have hcomm : expect (law p.slots) (fun w => expect (lazyAnswer (p.inst w).table o q) fun y =>
          cost (k y.1) (postPlain (p.inst w) o y.2) K)
        = expect (lazyAnswer p.table o q) fun y => expect (law p.slots) fun w =>
          cost (k y.1)
              ((p.log ⟨o, q⟩ y.2 (Function.update p.nPlain o (p.nPlain o + 1))).inst w) K :=
      expect_comm (law p.slots) (lazyAnswer p.table o q) fun w y =>
        cost (k y.1) (postPlain (p.inst w) o y.2) K
    rw [expect_add, hcomm, add_comm (expect (law p.slots) _) _, add_assoc]
    refine expect_add_const_le _ _ _ _ fun y hy => ?_
    refine le_trans (add_le_add le_rfl
      (le_trans (add_le_add (hitQ_bound hv ⟨o, q⟩) le_rfl)
        (pot_log_le hv ⟨o, q⟩ y.2 (Function.update p.nPlain o (p.nPlain o + 1)))))
      (ih y.1 (p.log ⟨o, q⟩ y.2 (Function.update p.nPlain o (p.nPlain o + 1))) ?_ ?_)
    · exact valid_log hv ⟨o, q⟩ y.2 _ (fun k' hk' => lazy_support hy k' hk')
        (count_bump_right ⟨o, q⟩ hv.count)
    · intro w hw z hz
      refine hs w hw z ?_
      rw [run_plain]
      exact (PMF.mem_support_bind_iff _ _ _).2 ⟨y, hy, hz⟩
  | fresh L k ih =>
    intro p hv hs
    simp only [cost]
    have key : expect (law p.slots) (fun w =>
          expect (PMF.uniformOfFintype (Fin L → Bool)) fun u' =>
            cost (k (p.inst w).vals.length) (postFresh (p.inst w) (List.ofFn u')) K) =
        expect (law (p.snoc L).slots) fun w' => cost (k p.slots.length) ((p.snoc L).inst w') K := by
      rw [show (p.snoc L).slots = p.slots ++ [Slot.hid L] from rfl, E_snoc]
      refine expect_congr_support _ fun w hw => ?_
      have hw' := (mem_support_law _ _).1 hw
      rw [E_hid]
      refine expect_congr _ fun u' => ?_
      rw [show (p.inst w).vals.length = p.slots.length from hw'.length, inst_fresh hv.toWf hw' L]
    rw [key]
    refine ih _ (p.snoc L) (valid_snoc hv L) fun w' hw' y hy => ?_
    obtain ⟨w, v, rfl, hw, hv'⟩ := agree_snoc_fwd hw'
    obtain ⟨u', rfl⟩ := ok_hid hv'
    refine hs w hw y ?_
    rw [run_fresh]
    refine (PMF.mem_support_bind_iff _ _ _).2 ⟨u', PMF.mem_support_uniformOfFintype u', ?_⟩
    rw [show (p.inst w).vals.length = p.slots.length from hw.length, inst_fresh hv.toWf hw L]
    exact hy
  | marked o t us pt inj k ih =>
    intro p hv hs
    have hsafe1 : ∀ w, Agree p.slots w →
        ∀ r : S.Rng o,
          ∀ y ∈ ((k (sp.split o r).1 (p.inst w).vals.length).run true
                (postMarked sp (p.inst w) o t us (pt ((p.inst w).val t) (us.map (p.inst w).val))
                  r (p.inst w).table)).support,
            Q y := by
      intro w hw r y hy
      refine hs w hw y ?_
      rw [run_marked_I]
      exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hy⟩
    have hevw := fun w hw r => evw_of_safe hQ _ _ (hsafe1 w hw r)
    have hbad : ∀ w, Agree p.slots w → markedBad (p.inst w) o t us = false := by
      intro w hw
      have h := (hevw w hw (Classical.arbitrary _)).viol
      have h' : (false || markedBad (p.inst w) o t us) = false := h
      simpa using h'
    obtain ⟨w₀, hw₀⟩ := exists_agree p.slots
    obtain ⟨ht, hus, hno, hsh, hind⟩ := markedBad_false (hbad w₀ hw₀)
    have ht₀ : t < w₀.length := ht
    have ht' : t < p.slots.length := hw₀.length ▸ ht₀
    have hus' : ∀ x ∈ us, x < p.slots.length := fun x hx => hw₀.length ▸ (hus x hx : x < w₀.length)
    obtain ⟨L, hL⟩ := hv.hid ht' hsh
    have hnew := (hevw w₀ hw₀ (Classical.arbitrary _)).ev
      ⟨o, pt ((p.inst w₀).val t) (us.map (p.inst w₀).val), Classical.arbitrary _,
        t, us, w₀.length, false⟩
      (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have ho : o ∈ os := hnew.1
    have hℓ : ℓ o ≤ L := by
      have h1 := hnew.2 (by
        show t < (w₀ ++ [_]).length
        rw [List.length_append]; exact Nat.lt_add_right _ ht₀)
      have h2 : (gv (w₀ ++ [List.ofFn (sp.split o (Classical.arbitrary _)).2]) t).length = L := by
        rw [gv_append_left ht₀]; exact hw₀.ok hL
      exact h2 ▸ h1
    have hind' : ∀ x ∈ p.evs, x.o = o → t ≠ x.charged ∧ t ∉ x.others := fun x hx hxo =>
      ⟨(hind (x.inst w₀) (List.mem_map_of_mem hx) hxo).1.symm,
        (hind (x.inst w₀) (List.mem_map_of_mem hx) hxo).2⟩
    simp only [cost]
    rw [expect_add]
    obtain ⟨μ, hμ⟩ := E_split sp o
    have key : expect (law p.slots) (fun w => expect (PMF.uniformOfFintype (S.Rng o)) fun r =>
          cost (k (sp.split o r).1 (p.inst w).vals.length)
            (postMarked sp (p.inst w) o t us
              (pt ((p.inst w).val t) (us.map (p.inst w).val)) r (p.inst w).table) K)
        = expect μ fun vis => expect (law (p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).slots) fun w' =>
          cost (k vis p.slots.length)
              ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst w') K := by
      calc _ = expect (law p.slots) fun w => expect (PMF.uniformOfFintype (S.Rng o)) fun r =>
              (fun z : sp.Vis o × (Fin (sp.tl o) → Bool) =>
                    cost (k z.1 p.slots.length)
                      ((p.mark ⟨o, t, us, pt, inj, z.1, p.slots.length, false⟩).inst
                        (w ++ [List.ofFn z.2])) K)
                  (sp.split o r) := by
            refine expect_congr_support _ fun w hw => expect_congr _ fun r => ?_
            have hw' := (mem_support_law _ _).1 hw
            rw [show (p.inst w).vals.length = p.slots.length from hw'.length,
              inst_mark hv.toWf hw' o t us pt inj r (hbad w hw')]
        _ = expect (law p.slots) fun w => expect μ fun vis =>
              expect (PMF.uniformOfFintype (Fin (sp.tl o) → Bool)) fun u' =>
                  cost (k vis p.slots.length)
                      ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst
                        (w ++ [List.ofFn u'])) K :=
            expect_congr _ fun w =>
              hμ fun z =>
                cost (k z.1 p.slots.length)
                  ((p.mark ⟨o, t, us, pt, inj, z.1, p.slots.length, false⟩).inst
                    (w ++ [List.ofFn z.2])) K
        _ = expect μ fun vis => expect (law p.slots) fun w =>
              expect (PMF.uniformOfFintype (Fin (sp.tl o) → Bool)) fun u' =>
                  cost (k vis p.slots.length)
                      ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst
                        (w ++ [List.ofFn u'])) K :=
            expect_comm _ _ _
        _ = _ := by
            refine expect_congr _ fun vis => ?_
            rw [show (p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).slots
              = p.slots ++ [Slot.hid (sp.tl o)] from rfl, E_snoc]
            exact expect_congr _ fun w => (E_hid (sp.tl o) fun v => cost (k vis p.slots.length)
              ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst (w ++ [v])) K).symm
    rw [key, add_comm (expect (law p.slots) _) _, add_assoc]
    refine expect_add_const_le _ _ _ _ fun vis _ => ?_
    have hpot : ((qCount p.qs o + aCount p.evs o : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ o) + p.pot ℓ os
        ≤ (p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).pot ℓ os := by
      show _ ≤ pot ℓ os
          (aCount (p.evs ++ [(⟨o, t, us, pt, inj, vis, p.slots.length, false⟩ : SEv S sp)]))
          (qCount p.qs)
      rw [aCount_snoc]
      exact pot_bump_a ℓ os _ _ ho
    refine le_trans
      (add_le_add le_rfl
        (le_trans (add_le_add (hitM_bound hv t us pt inj hno hL hℓ hind') le_rfl) hpot))
      (ih vis _ _ ?_ ?_)
    · exact valid_mark hv _ ht' hus' rfl hno hsh ho fun L' hL' => by
        rw [hL] at hL'
        obtain rfl : L = L' := by simpa using hL'
        exact hℓ
    · intro w' hw' y hy
      obtain ⟨w, v, rfl, hw, hv'⟩ := agree_snoc_fwd hw'
      obtain ⟨u', rfl⟩ := ok_hid hv'
      have hr : sp.split o ((sp.split o).symm (vis, u')) = (vis, u') := Equiv.apply_symm_apply _ _
      refine hsafe1 w hw ((sp.split o).symm (vis, u')) y ?_
      rw [show (p.inst w).vals.length = p.slots.length from hw.length,
        inst_mark hv.toWf hw o t us pt inj _ (hbad w hw), hr]
      exact hy
  | reveal ts k ih =>
    intro p hv hs
    simp only [cost]
    have hsafe1 : ∀ w, Agree p.slots w → ∀ y ∈ ((k (ts.map (p.inst w).val)).run true
        (postReveal true (p.inst w) ts)).support, Q y := by
      intro w hw y hy
      refine hs w hw y ?_
      rw [run_reveal]; exact hy
    have hviol : ∀ w, Agree p.slots w → (postReveal true (p.inst w) ts).viol = false :=
      fun w hw => (evw_of_safe hQ _ _ (hsafe1 w hw)).viol
    obtain ⟨w₀, hw₀⟩ := exists_agree p.slots
    have hr : RevOK p ts := revOK_of_viol hw₀ (hviol w₀ hw₀)
    rw [E_fixLaw _ ts p.slots]
    refine expect_add_const_le _ _ _ _ fun ss' hss' => ?_
    have hf := fixLaw_support ts p.slots ss' hss'
    have hmap : ∀ w,
        Agree ss' w → ts.map (p.inst w).val = ts.map (gv (ss'.map Slot.val0)) := fun w hw =>
      List.map_congr_left fun t ht => gv_eq_val0 hv.toWf hf hr hw (List.mem_append_right _ ht)
    have key : expect (law ss')
          (fun w => cost (k (ts.map (p.inst w).val)) (postReveal true (p.inst w) ts) K) =
        expect (law (p.reveal ts ss').slots) fun w =>
          cost (k (ts.map (gv (ss'.map Slot.val0)))) ((p.reveal ts ss').inst w) K := by
      refine expect_congr_support _ fun w hw => ?_
      have hw' := (mem_support_law _ _).1 hw
      rw [inst_reveal hv.toWf hf hr hw' (hviol w (hf.agree hw')), hmap w hw']
    have hpot : p.pot ℓ os = (p.reveal ts ss').pot ℓ os := by
      show pot ℓ os (aCount p.evs) _ = pot ℓ os (aCount (p.evs.map (srel (p.shown ++ ts)))) _
      rw [aCount_srel]
      rfl
    rw [key, hpot]
    refine ih _ (p.reveal ts ss') (valid_reveal hv hf hr) fun w hw y hy => ?_
    refine hsafe1 w (hf.agree hw) y ?_
    rw [inst_reveal hv.toWf hf hr hw (hviol w (hf.agree hw)), hmap w hw]
    exact hy

/-! ### The bound for a run, and `defer` -/

theorem aCount_inst (evs : List (SEv S sp)) (w : List Bits) (o : S.ι) :
    ((evs.map fun x => x.inst w).filter fun v => decide (v.o = o)).length = aCount evs o := by
  rw [List.filter_map, List.length_map]
  rfl

theorem adv_bound {Out In α : Type} (C : Chall S sp Out In) (t : S.ι → ℕ) (A : Adv S Out In α) :
    ∀ (τ : C.τ) (p : PSt S sp) (u t' : S.ι → ℕ) (N : ℕ), A.Bounded t' N → Valid ℓ os u p →
      (∀ o, u o + t' o ≤ t o) →
      (∀ w, Agree p.slots w → ∀ x ∈ (interact (C.world true) A (τ, p.inst w)).support,
        x.2.2.Within e M ℓ os) →
      expect (law p.slots) (fun w => advCost C A (τ, p.inst w) fun _ => 0) + p.pot ℓ os
        ≤ ∑ o ∈ os, (M o : ℝ≥0∞) * (t o + e o + M o : ℕ) / 2 ^ ℓ o := by
  induction A with
  | halt a =>
    intro τ p u t' N _ hv hb hs
    simp only [advCost]
    rw [expect_zero, zero_add]
    obtain ⟨w, hw⟩ := exists_agree p.slots
    have hW : (p.inst w).Within e M ℓ os :=
      hs w hw (a, (τ, p.inst w)) (by rw [interact]; exact (PMF.mem_support_pure_iff _ _).2 rfl)
    refine Finset.sum_le_sum fun o _ => ?_
    have h1 : aCount p.evs o ≤ M o := by
      rw [← aCount_inst p.evs w o]; exact hW.2.2.1 o
    have h2 : qCount p.qs o ≤ t o + e o := by
      have := hv.count o
      have h3 : p.nPlain o ≤ e o := hW.2.1 o
      have := hb o
      omega
    rw [mul_one_div, ← Nat.cast_mul]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast Nat.mul_le_mul h1 (Nat.add_le_add h2 h1)
  | sample n k ih =>
    intro τ p u t' N hB hv hb hs
    simp only [advCost]
    rw [expect_comm]
    refine expect_add_const_le _ _ _ _ fun r _ =>
      ih r τ p u t' N (hB r) hv hb fun w hw x hx => hs w hw x ?_
    rw [interact]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hx⟩
  | query o q k ih =>
    intro τ p u t' N hB hv hb hs
    obtain ⟨hpos, hB'⟩ := hB
    simp only [advCost]
    have hcomm : expect (law p.slots) (fun w => expect (lazyAnswer (p.inst w).table o q) fun y =>
          advCost C (k y.1) (τ, withT (p.inst w) y.2) fun _ => 0)
        = expect (lazyAnswer p.table o q) fun y => expect (law p.slots) fun w =>
          advCost C (k y.1) (τ, (p.log ⟨o, q⟩ y.2 p.nPlain).inst w) fun _ => 0 :=
      expect_comm (law p.slots) (lazyAnswer p.table o q) fun w y =>
        advCost C (k y.1) (τ, withT (p.inst w) y.2) fun _ => 0
    rw [expect_add, hcomm, add_comm (expect (law p.slots) _) _, add_assoc]
    refine expect_add_const_le _ _ _ _ fun y hy => ?_
    refine le_trans
      (add_le_add le_rfl
        (le_trans (add_le_add (hitQ_bound hv ⟨o, q⟩) le_rfl) (pot_log_le hv ⟨o, q⟩ y.2 p.nPlain)))
      (ih y.1 τ (p.log ⟨o, q⟩ y.2 p.nPlain) (Function.update u o (u o + 1))
        (Function.update t' o (t' o - 1)) N (hB' y.1) ?_ ?_ ?_)
    · exact valid_log hv ⟨o, q⟩ y.2 _ (fun k' hk' => lazy_support hy k' hk')
        (count_bump_left ⟨o, q⟩ hv.count)
    · intro o'
      by_cases ho : o' = o
      · subst ho
        rw [Function.update_self, Function.update_self]
        have := hb o'
        omega
      · rw [Function.update_of_ne ho, Function.update_of_ne ho]
        exact hb o'
    · intro w hw x hx
      refine hs w hw x ?_
      rw [interact]
      exact (PMF.mem_support_bind_iff _ _ _).2
        ⟨(y.1, (τ, withT (p.inst w) y.2)), (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩, hx⟩
  | call m k ih =>
    intro τ p u t' N hB hv hb hs
    cases N with
    | zero => exact absurd hB (by simp [Adv.Bounded])
    | succ N =>
      simp only [advCost]
      refine step_bound (e := e) (M := M) u _ (fun y => advCost C (k y.1.1) (y.1.2, y.2) fun _ => 0)
        (fun y =>
          ∀ x ∈ (interact (C.world true) (k y.1.1) (y.1.2, y.2)).support, x.2.2.Within e M ℓ os)
        (fun y hy => ?_) (fun a p' hv' hq' => ?_) (C.step τ m)
        p hv fun w hw y hy x hx => hs w hw x ?_
      · obtain ⟨x, hx⟩ := (interact (C.world true) (k y.1.1) (y.1.2, y.2)).support_nonempty
        exact ⟨x.2.2, interact_ext C _ _ x hx, hy x hx⟩
      · exact ih a.1 a.2 p' u t' N (hB a.1) hv' hb hq'
      · rw [interact]
        exact (PMF.mem_support_bind_iff _ _ _).2
          ⟨(y.1.1, (y.1.2, y.2)), (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩, hx⟩

end Main

/-- Deferred programming, in the form of Spec.defer. -/
theorem defer : Spec.defer := by
  intro S sp Out In α C s₀ A t e M ℓ N os hB hW
  refine (tv_le_hits C s₀ A).trans ?_
  have hv : Valid ℓ os (fun _ => 0) (⟨Table.empty S, [], [], [], fun _ => 0, []⟩ : PSt S sp) :=
    ⟨⟨fun t => by simp, fun x hx => by simp at hx, fun x hx => by simp at hx⟩,
      fun w _ k hk => absurd rfl hk, fun x hx => by simp at hx, fun o => by simp [qCount]⟩
  have h := adv_bound (e := e) (M := M) C t A s₀
    ⟨Table.empty S, [], [], [], fun _ => 0, []⟩ (fun _ => 0) t N hB hv
    (fun o => by simp) (fun w hw x hx => by
      cases hw
      exact hW x hx)
  rw [E_nil] at h
  exact le_trans (le_add_right le_rfl) h

end DeferTail
end Rom
