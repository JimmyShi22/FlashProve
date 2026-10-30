-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/LifeStar.lean: the lifetime theorem for the first encoding and its copies, with
batches. Proof of the statement of Compile/Batch/SpecLifeStar.lean (words of this library:
lean/GLOSSARY.md).

The mathematics is in Compile/Batch/Life.lean (theorem `lifetime`, game 1, "the general game"). This
file only translates:
 * `interact_pre`, `interact_post`: `StarWB` samples the randomness of the encodings at "setup", the
   general game at the start;
 * `toPlay`: oracle answers and placements are coins of the general game's adversary;
 * `nice_pre`, `nice_post`: admissibility (`LifeAdmB`), with `hb1` (`qT + m * qpar ≤ b`), `hb2`
   (`qch + s1 * qon ≤ b`) (`nice_post`: with bounds on the loads so far in their place), gives the
   three conditions of the general theorem: allowed calls, loads within the budget, and the bound on
   the sum of the errors ("three conditions", in this sense: the first two are hypotheses of
   `lifetime` on the adversary, `hok`, `hfit`; the third bounds its right-hand side).

Notation: in Compile/Batch/SpecLifeStar.lean: `StarWB S m`: the experiment with m copies, for
arbitrary distributions of the three kinds of sessions; `LifeB S L m i`: the real lifetime
experiment on the index i; `simWorldB`: see its docstring; `LifeAdmB ok s1 B c flag n` (the same
file): one setup, first; then at most s1 batches on each copy, at most n in all, each with at most maxBatchSize
requests, all allowed; c counts the batches on each copy; flag: a `Bool`: `false` is asked at
"setup", `true` at a batch and after "setup"; `b`, `qT`, `qpar`, `qch`, `qon`: natural numbers, the
arguments of `BatchProtocol.Reads` (Iop/Batch.lean); `Nice t ld B`: the three conditions together (its
docstring, below).
-/
import Compile.Batch.SpecLifeStar
import Compile.Batch.Life
import Compile.LifeStar

noncomputable section

namespace Compile.BatchLife.Star

open Prob Iop Rom Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {S : OSpec} {L : BatchProtocol I X} {m : ℕ}

section Laws
variable (sT : L.EncodingRandomness → PMF (Sess L.offline)) (sL : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)) (sB : L.EncodingRandomness → BLaw L)

/-- Sessions of Link with the first encoding, on the copies of a list. -/
def seqL (r₀ : L.EncodingRandomness) : List L.EncodingRandomness → PMF (List (Sess L.link))
  | [] => PMF.pure []
  | r :: l => (sL r₀ r).bind fun s => (seqL r₀ l).map fun t => s :: t

/-- The copies may all be sampled before the first session of Link. -/
theorem linksGB_bind {γ : Type} (r₀ : L.EncodingRandomness) :
    ∀ (n : ℕ) (F : List L.EncodingRandomness → List (Sess L.link) → PMF γ),
      ((linksGB sL r₀ n).bind fun ls => F (ls.map Prod.fst) (ls.map Prod.snd)) =
        (unif (Fin n → L.EncodingRandomness)).bind fun g =>
          (seqL sL r₀ (List.ofFn g)).bind fun t => F (List.ofFn g) t
  | 0, F => by
      simp only [linksGB, PMF.pure_bind, List.map_nil, List.ofFn_zero, seqL, PMF.bind_const]
  | n + 1, F => by
      rw [unif_succ_bind]
      simp only [linksGB, PMF.bind_bind, PMF.bind_map, Function.comp_def, List.map_cons,
        List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, seqL]
      refine congrArg _ (funext fun r => ?_)
      rw [Prob.bind_comm (unif (Fin n → L.EncodingRandomness))]
      refine congrArg _ (funext fun s => ?_)
      exact linksGB_bind r₀ n fun l t => F (r :: l) (s :: t)

/-- The sessions of the general game that belong to sT, sL, sB. Encoding 0 is the first encoding. -/
def starO (r : Fin (m + 1) → L.EncodingRandomness) : ∀ c : Call (Fin (m + 1)) X L.maxBatchSize, PMF (Ans L c)
  | .test e => sT (r e)
  | .link e e' => sL (r e) (r e')
  | .bat e J xs rest => sB (r e) J xs rest

end Laws

variable {α : Type}

/-- One call "link" for each copy of a list; go on with the list of the answers. -/
def linksP :
    List (Fin m) → (List (Sess L.link) → Adversary L (Fin (m + 1)) α) → Adversary L (Fin (m + 1)) α
  | [], g => g []
  | j :: js, g => .call (.link 0 j.succ) fun (s : Sess L.link) => linksP js fun t => g (s :: t)

/-- The adversary of the general game that belongs to an adversary of `StarWB`. "Setup" becomes a
Test on the first encoding and a Link for each copy. The answers of the random oracles, by lazy
sampling from the table T, and the placements are its own coins. -/
def toPlay (m : ℕ) : Adv S (LifeOutB X) (LifeInB L) α → Table S → Adversary L (Fin (m + 1)) α
  | .halt a, _ => .done a
  | .sample n k, T => .draw (Fin (n + 1)) (unif (Fin (n + 1))) fun r => toPlay m (k r) T
  | .query o q k, T => .draw (S.Rng o × Table S) (lazyAnswer T o q) fun p => toPlay m (k p.1) p.2
  | .call (.inl ()) k, T => .call (.test 0) fun (a : Sess L.offline) =>
      linksP (List.finRange m) fun t => toPlay m (k (.inl (a, t))) T
  | .call (.inr (j, xs)) k, T =>
      if h : j < m then
        .draw (Equiv.Perm (Fin L.maxBatchSize)) (unif (Equiv.Perm (Fin L.maxBatchSize))) fun σ =>
          .call (.bat (⟨j, h⟩ : Fin m).succ (slotsOf σ xs.length) (ownAt σ xs) fun _ => none)
              fun (a : BSess L.onlineBatch (slotsOf σ xs.length)) =>
            toPlay m (k (.inr (some (slotList σ xs.length, ⟨slotsOf σ xs.length, a⟩)))) T
      else toPlay m (k (.inr none)) T

section Translate
variable (sT : L.EncodingRandomness → PMF (Sess L.offline)) (sL : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)) (sB : L.EncodingRandomness → BLaw L)

theorem run_linksP (r : Fin (m + 1) → L.EncodingRandomness) :
    ∀ (js : List (Fin m)) (g : List (Sess L.link) → Adversary L (Fin (m + 1)) α),
      (linksP js g).run (starO sT sL sB r) =
        (seqL sL (r 0) (js.map fun j => r j.succ)).bind fun t => (g t).run (starO sT sL sB r)
  | [], g => by simp only [linksP, List.map_nil, seqL, PMF.pure_bind]
  | j :: js, g => by
      simp only [linksP, Play.run_call, List.map_cons, seqL, PMF.bind_bind,
        PMF.bind_map, Function.comp_def]
      refine congrArg _ (funext fun s => ?_)
      exact run_linksP r js fun t => g (s :: t)

variable {ok : X → Prop} {s1 : ℕ}

/-- After "setup", under `LifeAdmB`: `StarWB`, with the randomness of the copies in its state, is
the general game. -/
theorem interact_post (r : Fin (m + 1) → L.EncodingRandomness) (B : Adv S (LifeOutB X) (LifeInB L) α) :
    ∀ (T : Table S) (c : ℕ → ℕ) (n : ℕ), LifeAdmB ok s1 B c true n →
      (interact (StarWB sT sL sB S m) B
          (some (List.ofFn fun j : Fin m => r j.succ), T)).map Prod.fst =
        (toPlay m B T).run (starO sT sL sB r) := by
  induction B with
  | halt a => intro T c n _; simp only [interact, PMF.pure_map, toPlay, Play.run_done]
  | sample n' k ih =>
    intro T c n h
    simp only [interact, PMF.map_bind, toPlay, Play.run_draw]
    exact congrArg _ (funext fun r' => ih r' T c n (h r'))
  | query o q k ih =>
    intro T c n h
    simp only [interact, StarWB, PMF.map_bind, PMF.bind_map,
      Function.comp_def, toPlay, Play.run_draw]
    exact congrArg _ (funext fun p => ih p.1 p.2 c n (h p.1))
  | call mm k ih =>
    intro T c n h
    rcases mm with ⟨⟩ | ⟨j, xs⟩
    · exact absurd h.1 (by simp)
    · cases n with
      | zero => exact h.elim
      | succ n =>
        obtain ⟨-, -, -, -, h4⟩ := h
        by_cases hj : j < m
        · simp only [interact, StarWB, Option.bind_some, List.getElem?_ofFn, hj, dif_pos,
            PMF.map_bind, PMF.bind_map, Function.comp_def, toPlay, Play.run_call,
            Play.run_draw, placeB, PMF.bind_bind]
          refine congrArg _ (funext fun σ => ?_)
          exact congrArg _ (funext fun o => ih _ T _ n (h4 _))
        · simp only [interact, StarWB, Option.bind_some, List.getElem?_ofFn, hj, dif_neg,
            not_false_eq_true, PMF.pure_bind, toPlay]
          exact ih _ T _ n (h4 _)

/-- Before "setup", under `LifeAdmB`: `StarWB` is the general game, in which the randomness of all
encodings is sampled at the start. -/
theorem interact_pre (B : Adv S (LifeOutB X) (LifeInB L) α) : ∀ (T : Table S) (c : ℕ → ℕ) (n : ℕ),
    LifeAdmB ok s1 B c false n →
    (interact (StarWB sT sL sB S m) B (none, T)).map Prod.fst
      = (unif (Fin (m + 1) → L.EncodingRandomness)).bind fun r => (toPlay m B T).run (starO sT sL sB r) := by
  induction B with
  | halt a =>
    intro T c n _; simp only [interact, PMF.pure_map, toPlay, Play.run_done, PMF.bind_const]
  | sample n' k ih =>
    intro T c n h
    simp only [interact, PMF.map_bind, toPlay, Play.run_draw]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun r' => ih r' T c n (h r'))
  | query o q k ih =>
    intro T c n h
    simp only [interact, StarWB, PMF.map_bind, PMF.bind_map,
      Function.comp_def, toPlay, Play.run_draw]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun p => ih p.1 p.2 c n (h p.1))
  | call mm k ih =>
    intro T c n h
    rcases mm with ⟨⟩ | ⟨j, xs⟩
    · obtain ⟨-, h2⟩ := h
      rw [unif_succ_bind]
      simp only [interact, StarWB, PMF.map_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def,
        toPlay, Play.run_call, run_linksP, starO, Fin.cons_zero, Fin.cons_succ]
      refine congrArg _ (funext fun r₀ => ?_)
      rw [Prob.bind_comm (unif (Fin m → L.EncodingRandomness))]
      refine congrArg _ (funext fun a => ?_)
      refine (linksGB_bind sL r₀ m fun l t =>
        (interact (StarWB sT sL sB S m) (k (.inl (a, t))) (some l, T)).map Prod.fst).trans ?_
      refine congrArg _ (funext fun g => ?_)
      rw [← List.ofFn_eq_map]
      refine congrArg _ (funext fun t => ?_)
      have h3 :=
        interact_post sT sL sB (Fin.cons r₀ g : Fin (m + 1) → L.EncodingRandomness) (k (.inl (a, t))) T c n (h2 _)
      simp only [Fin.cons_succ] at h3
      exact h3
    · cases n with
      | zero => exact h.elim
      | succ n => exact absurd h.1 (by simp)

end Translate

/-! ## Admissible adversaries of `StarWB`, with `hb1`, `hb2`, keep the three conditions `Nice` -/

section Nice
variable (Ryes : I → X → Prop) (i : I) (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞)

/-- The three conditions together: the calls are allowed, all encodings being encodings of i; from
the loads ld on, no encoding is loaded beyond b; the errors of the sessions add up to at most B. -/
def Nice (t : Adversary L (Fin (m + 1)) α) (ld : Fin (m + 1) → ℕ) (B : ℝ≥0∞) : Prop :=
  t.Calls (Allowed Ryes fun _ => i) ∧ t.Fits (load qT qpar qch qon) b ld ∧ t.cost (err zT zL zO) ≤ B

local notation "NICE" => Nice Ryes i b qT qpar qch qon zT zL zO

variable {Ryes i b qT qpar qch qon zT zL zO}

theorem nice_draw {β : Type} {d : PMF β} {k : β → Adversary L (Fin (m + 1)) α}
    {ld : Fin (m + 1) → ℕ} {B : ℝ≥0∞} (h : ∀ y, NICE (k y) ld B) : NICE (.draw β d k) ld B :=
  ⟨fun y => (h y).1, fun y => (h y).2.1, by rw [Play.cost_draw]; exact iSup_le fun y => (h y).2.2⟩

theorem nice_call {c : Call (Fin (m + 1)) X L.maxBatchSize} {k : Ans L c → Adversary L (Fin (m + 1)) α}
    {ld : Fin (m + 1) → ℕ} {B : ℝ≥0∞} (hc : Allowed Ryes (fun _ => i) c)
    (h : ∀ a, NICE (k a) (fun e => ld e + load qT qpar qch qon c e) B) :
    NICE (.call c k) ld (err zT zL zO c + B) :=
  ⟨⟨hc, fun a => (h a).1⟩, fun a => (h a).2.1, by
    rw [Play.cost_call]; exact add_le_add le_rfl (iSup_le fun a => (h a).2.2)⟩

theorem Nice.mono {t : Adversary L (Fin (m + 1)) α} {ld : Fin (m + 1) → ℕ} {B B' : ℝ≥0∞}
    (h : NICE t ld B) (hB : B ≤ B') :
    NICE t ld B' := ⟨h.1, h.2.1, h.2.2.trans hB⟩

/-- One Link for each copy of a list without repetitions: qpar more on the first encoding for each,
qch more on each of these copies. -/
theorem nice_linksP : ∀ js : List (Fin m), js.Nodup → ∀ (ld : Fin (m + 1) → ℕ)
    (g : List (Sess L.link) → Adversary L (Fin (m + 1)) α) (B : ℝ≥0∞),
    (∀ (ld' : Fin (m + 1) → ℕ) (t : List (Sess L.link)), ld' 0 ≤ ld 0 + js.length * qpar →
      (∀ j : Fin m, ld' j.succ ≤ ld j.succ + if j ∈ js then qch else 0) → NICE (g t) ld' B) →
    NICE (linksP js g) ld (js.length * zL + B)
  | [], _, ld, g, B, h => by
      have h1 := h ld [] (by simp) (by simp)
      simpa [linksP] using h1
  | j :: js, hnd, ld, g, B, h => by
      have hnd' := List.nodup_cons.1 hnd
      have h1 : NICE (linksP (j :: js) g) ld
          (err zT zL zO (.link 0 j.succ : Call (Fin (m + 1)) X L.maxBatchSize) + (js.length * zL + B)) := by
        refine nice_call rfl fun s =>
          nice_linksP js hnd'.2 _ _ B fun ld' t h0 hj => h ld' (s :: t) ?_ fun j' => ?_
        · refine h0.trans (le_of_eq ?_)
          simp only [load, if_true, (Fin.succ_ne_zero j).symm, if_false, List.length_cons]
          ring
        · refine (hj j').trans ?_
          by_cases hjj : j' = j
          · subst hjj
            simp [load, Fin.succ_ne_zero, hnd'.1]
          · simp [load, Fin.succ_ne_zero, hjj]
      refine h1.mono (le_of_eq ?_)
      simp only [err, List.length_cons]
      push_cast
      ring

variable {s1 : ℕ}

/-- `Nice` after "setup", under the hypotheses below. -/
theorem nice_post (B : Adv S (LifeOutB X) (LifeInB L) α) :
    ∀ (T : Table S) (c : ℕ → ℕ) (n : ℕ) (ld : Fin (m + 1) → ℕ), LifeAdmB (Ryes i) s1 B c true n →
      ld 0 ≤ b → (∀ j : Fin m, ld j.succ + (s1 - c j) * qon ≤ b) →
      NICE (toPlay m B T) ld (n * (L.maxBatchSize * zO)) := by
  induction B with
  | halt a =>
    intro T c n ld _ h0 hl
    exact ⟨trivial,
      fun e => Fin.cases h0 (fun j => le_trans (Nat.le_add_right _ _) (hl j)) e,
      zero_le _⟩
  | sample n' k ih =>
    intro T c n ld h h0 hl
    exact nice_draw fun r => ih r T c n ld (h r) h0 hl
  | query o q k ih =>
    intro T c n ld h h0 hl
    exact nice_draw fun p => ih p.1 p.2 c n ld (h p.1) h0 hl
  | call mm k ih =>
    intro T c n ld h h0 hl
    rcases mm with ⟨⟩ | ⟨j, xs⟩
    · exact absurd h.1 (by simp)
    · cases n with
      | zero => exact h.elim
      | succ n =>
        obtain ⟨-, h2, hlen, h3, h4⟩ := h
        have hz : (L.maxBatchSize : ℝ≥0∞) * zO + (n : ℝ≥0∞) * (L.maxBatchSize * zO) =
            ((n + 1 : ℕ) : ℝ≥0∞) * (L.maxBatchSize * zO) := by
          push_cast
          ring
        by_cases hj : j < m
        · simp only [toPlay, dif_pos hj]
          rw [← hz]
          refine nice_draw fun σ =>
            Nice.mono (nice_call
                (c := .bat (⟨j, hj⟩ : Fin m).succ (slotsOf σ xs.length) (ownAt σ xs) fun _ => none)
                ⟨fun j' => h3 _ (List.getElem_mem _), fun _ _ hh => by cases hh⟩
                fun o => ih _ T _ n _ (h4 _) ?_ fun j' => ?_)
              (add_le_add
                (mul_le_mul' (Nat.cast_le.2 ((card_slotsOf_le σ _).trans hlen)) le_rfl) le_rfl)
          · simpa [load, (Fin.succ_ne_zero _).symm] using h0
          · by_cases hjj : j' = ⟨j, hj⟩
            · subst hjj
              have h5 := hl ⟨j, hj⟩
              have e1 : s1 - c j = (s1 - (c j + 1)) + 1 := by omega
              simp only [e1, Nat.add_mul, one_mul] at h5
              simp only [load, if_true, Function.update_self]
              omega
            · have hne : (j' : ℕ) ≠ j := fun hh => hjj (Fin.ext hh)
              have hs : j'.succ ≠ (⟨j, hj⟩ : Fin m).succ := fun hh => hjj (Fin.succ_injective _ hh)
              simp only [load, if_neg hs, Nat.add_zero, Function.update_of_ne hne]
              exact hl j'
        · simp only [toPlay, dif_neg hj]
          refine (ih _ T _ n ld (h4 _) h0 fun j' => ?_).mono (by rw [← hz]; exact le_add_self)
          have hne : (j' : ℕ) ≠ j := fun hh => hj (hh ▸ j'.2)
          rw [Function.update_of_ne hne]
          exact hl j'

/-- `Nice` from the start, under `hb1`, `hb2` and `LifeAdmB`. -/
theorem nice_pre (hb1 : qT + m * qpar ≤ b) (hb2 : qch + s1 * qon ≤ b)
    (B : Adv S (LifeOutB X) (LifeInB L) α) :
    ∀ (T : Table S) (c : ℕ → ℕ) (n : ℕ), LifeAdmB (Ryes i) s1 B c false n →
      NICE (toPlay m B T) (fun _ => 0) (zT + m * zL + n * (L.maxBatchSize * zO)) := by
  induction B with
  | halt a => intro T c n _; exact ⟨trivial, fun _ => Nat.zero_le _, zero_le _⟩
  | sample n' k ih => intro T c n h; exact nice_draw fun r => ih r T c n (h r)
  | query o q k ih => intro T c n h; exact nice_draw fun p => ih p.1 p.2 c n (h p.1)
  | call mm k ih =>
    intro T c n h
    rcases mm with ⟨⟩ | ⟨j, xs⟩
    · obtain ⟨-, h2⟩ := h
      have h1 : NICE (toPlay m (.call (.inl ()) k) T) (fun _ => 0)
          (err zT zL zO (.test 0 : Call (Fin (m + 1)) X L.maxBatchSize) +
            (((List.finRange m).length : ℕ) * zL + n * (L.maxBatchSize * zO))) := by
        refine nice_call trivial fun a =>
            nice_linksP _ (List.nodup_finRange m) _ _ _ fun ld' t h0 hj =>
          nice_post _ T c n ld' (h2 _) ?_ fun j => ?_
        · refine h0.trans (le_trans (le_of_eq ?_) hb1)
          simp [load]
        · have h5 := hj j
          have h6 : (s1 - c j) * qon ≤ s1 * qon := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
          simp only [load, Fin.succ_ne_zero, if_false, List.mem_finRange, if_true] at h5
          omega
      refine h1.mono (le_of_eq ?_)
      simp only [err, List.length_finRange]
      ring
    · cases n with
      | zero => exact h.elim
      | succ n => exact absurd h.1 (by simp)

end Nice

theorem realO_eq (i : I) (r : Fin (m + 1) → L.EncodingRandomness) :
    realO L (fun _ => i) r =
      starO (fun r => sess L.honestOfflineProver (i, r) ()) (fun r r' => sess L.honestLinkProver (i, r, r') ())
        (fun r J xs rest => bsess L.honestOnlineBatchProver (i, r) (vec J xs rest) J) r :=
  funext fun c => by cases c <;> rfl

theorem simO_eq (Sm : Sims L) (i₀ : I) (r : Fin (m + 1) → L.EncodingRandomness) :
    simO L Sm (fun e => L.encodeIndex i₀ (r e)) =
      starO (fun r => simSess L.offline Sm.T () (L.encodeIndex i₀ r))
        (fun r r' => simSess L.link Sm.Lk () (L.encodeIndex i₀ r, L.encodeIndex i₀ r'))
        (fun r J xs _ => simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i₀ r)) r :=
  funext fun c => by cases c <;> rfl

/-- The lifetime theorem for the first encoding and its m copies, with batches and an explicit
simulator (hypotheses below).
(the conclusion: `tv` of `(interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst` and
`(interact (simWorldB S L m Sm i₀) B (none, Table.empty S)).map Prod.fst`:
`≤ zT + m * zL + n * (L.maxBatchSize * zO)`) -/
theorem life_star {Ryes : I → X → Prop} {b qT qpar qch qon s1 : ℕ} {zT zL zO : ℝ≥0∞} (hW : L.Wired)
    (hR : L.Reads b qT qpar qch qon) {Sm : Sims L} (hS : Sm.Good Ryes zT zL zO)
    (hb1 : qT + m * qpar ≤ b) (hb2 : qch + s1 * qon ≤ b) (i i₀ : I)
    (B : Adv S (LifeOutB X) (LifeInB L) α) (n : ℕ)
    (hB : LifeAdmB (Ryes i) s1 B (fun _ => 0) false n) :
    tv ((interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst)
        ((interact (simWorldB S L m Sm i₀) B (none, Table.empty S)).map Prod.fst) ≤
      zT + m * zL + n * (L.maxBatchSize * zO) := by
  obtain ⟨h1, h2, h3⟩ := nice_pre (zT := zT) (zL := zL) (zO := zO) hb1 hb2 B (Table.empty S) _ n hB
  have h4 := (lifetime hW hR hS (fun _ => i) i₀ (toPlay m B (Table.empty S)) h1 h2).trans h3
  unfold real ideal at h4
  simp only [realO_eq, simO_eq] at h4
  have eL : (interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst = _ :=
    interact_pre _ _ _ B _ _ n hB
  have eS : (interact (simWorldB S L m Sm i₀) B (none, Table.empty S)).map Prod.fst = _ :=
    interact_pre _ _ _ B _ _ n hB
  rw [eL, eS]
  exact h4

end Compile.BatchLife.Star

namespace Compile.BatchLife

open Prob Iop Rom

theorem lifeStarBWith :
    Spec.lifeStarBWith := fun _ _ _ _ _ _ _ _ hW hR _ hS hb1 hb2 i i₀ _ B n hB =>
  Star.life_star hW hR hS hb1 hb2 i i₀ B n hB

end Compile.BatchLife
