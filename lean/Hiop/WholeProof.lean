-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/WholeProof.lean: honest-verifier zero knowledge of the whole object. Proofs of the statements
of Hiop/Whole.lean.

The mathematics (replace each run by its simulator, which still reads the true encodings; then see
environment and simulators as one algorithm that reads a table with independent rows, at most b
places in each row) is `Compile.Lifetime.lifetime_abstract` with `rows_law` and `Play.within_plug`
(Compile/Life.lean), as for `Compile.BatchLife.lifetime` (Compile/Batch/Life.lean). That theorem is
about a game in which the encoding randomness of all encodings is drawn at the start. This file
adds:
 Part 0: one entry of a uniform tuple may be drawn anew (`unif_resample`);
 Part 1: the real side and the simulator of the theorem are the same host for two families of laws
         of runs (`Laws`, `Laws.host`);
 Part 2: the game with all randomness drawn at the start, with single reads of an encoding as a
         further kind of call (`WCall`), and the environment as an adversary of that game
         (`toPlay`, `whole`);
 Part 3: for an environment within its bounds, drawing when asked is drawing at the start
         (`run_eq`: also c ≤ B.nenc; `view_eq`);
 Part 4: the lifetime theorem with single reads (`lifetimeW`), for any real side each of whose runs
         is near the simulated run on the true encodings (exactly: `Laws.Near`; of a batch under
         `∀ j, ok (xs j)` and `∀ j x, rest j = some x → ok x`: its field `B`; `near_real`: under
         `hW : L.Wired` and `hS : Sm.Good Ryes zT zL zO` the real side of Hiop/Whole.lean is, at ok
         := Ryes i) (not all hypotheses are named here: see `lifetimeW`);
 Part 5: an environment within its bounds makes allowed calls, keeps every encoding within the
         budget (under `Inv`; `fits_toPlay` and `cost_toPlay` also under c ≤ B.nenc), and the
         errors of its runs add up to at most the error of the statement (`calls_toPlay`,
         `fits_toPlay`, `cost_toPlay`);
 Part 6: the theorems (`hvzk_whole`, `hvzk_whole_hiding`, `hvzk_view`; `tv_view_le`: for any such
         real side, under the hypotheses of its statement; it is also used in
         Hiop/WholeTrueProof.lean).

Limits: for what is not said, see the head of Hiop/Whole.lean (there above all: "Which statement is
which", and the numbered differences 1 to 7).

Terms: lean/GLOSSARY.md.
-/
import Hiop.Whole
import Compile.Batch.Life

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

/-! ## Part 0. One entry of a uniform tuple may be drawn anew -/

theorem unif_resample {ι R γ : Type} [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    (k : ι) (G : (ι → R) → PMF γ) :
    ((unif R).bind fun r => (unif (ι → R)).bind fun t => G (Function.update t k r)) =
      (unif (ι → R)).bind G := by
  have key : ∀ F : (ι → R) → PMF γ, (unif (ι → R)).bind F =
      (unif R).bind fun r =>
        (unif ({j // j ≠ k} → R)).bind fun w => F ((Equiv.funSplitAt k R).symm (r, w)) := by
    intro F
    rw [← map_unif_equiv (Equiv.funSplitAt k R).symm, PMF.bind_map,
      unif_prod, bind_bind_eq_prod_bind]
    rfl
  have hupd : ∀ (r r' : R) (w : {j // j ≠ k} → R),
      Function.update ((Equiv.funSplitAt k R).symm (r', w)) k r =
        (Equiv.funSplitAt k R).symm (r, w) := by
    intro r r' w
    funext j
    by_cases hj : j = k
    · subst hj
      simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [key G]
  refine congrArg _ (funext fun r => ?_)
  rw [key]
  simp only [hupd, PMF.bind_const]

variable {I X : Type} {L : BatchProtocol I X} {α : Type}

/-! ## Part 1. One host for two families of laws -/

/-- The laws of what is shown of the three kinds of runs, and the symbols of an encoded index, as
functions of the encoding randomness. -/
structure Laws (L : BatchProtocol I X) where
  T : L.EncodingRandomness → PMF (Sess L.offline)
  Lk : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)
  B : L.EncodingRandomness → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J)
  y : L.EncodingRandomness → Fin L.wordLength → L.Symbol

/-- The host that draws the randomness of an encoded index when it is asked for. -/
def Laws.host (W : Laws L) : Host L where
  σ := ℕ × (ℕ → L.EncodingRandomness)
  off := (unif L.EncodingRandomness).bind fun r => (W.T r).map fun a => (a, (0, fun _ => r))
  fresh := fun s =>
    (unif L.EncodingRandomness).bind fun r =>
      (W.Lk (s.2 0) r).map fun a => (a, (s.1 + 1, Function.update s.2 (s.1 + 1) r))
  session := fun s e J xs rest => (W.B (s.2 e) J xs rest).map fun a => (a, s)
  read := fun s e p => PMF.pure (W.y (s.2 e) p, s)

def realLaws (L : BatchProtocol I X) (i : I) : Laws L where
  T := fun r => sess L.honestOfflineProver (i, r) ()
  Lk := fun r r' => sess L.honestLinkProver (i, r, r') ()
  B := fun r J xs rest => bsess L.honestOnlineBatchProver (i, r) (vec J xs rest) J
  y := fun r p => L.encodeIndex i r p

def simLaws (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) : Laws L where
  T := fun r => simSess L.offline Sm.T () (L.encodeIndex i₀ r)
  Lk := fun r r' => simSess L.link Sm.Lk () (L.encodeIndex i₀ r, L.encodeIndex i₀ r')
  B := fun r J xs _ => simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i₀ r)
  y := fun r p => L.encodeIndex i₀ r p

theorem realHost_eq (i : I) : realHost L i = (realLaws L i).host := rfl
theorem simHost_eq (Sm : Sims L) (i₀ : I) : (simWhole L Sm i₀).host = (simLaws L Sm i₀).host := rfl

section HostEqs
variable (W : Laws L)
theorem view_host (E : Sess L.offline → Env L α) :
    W.host.view E =
      (unif L.EncodingRandomness).bind fun r => (W.T r).bind fun a => (E a).run W.host (0, fun _ => r) := by
  show ((unif L.EncodingRandomness).bind fun r => (W.T r).map fun a => (a, ((0, fun _ => r) : ℕ × (ℕ → L.EncodingRandomness)))).bind
      (fun p => (E p.1).run W.host p.2) = _
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
theorem run_stop (a : α) (s : ℕ × (ℕ → L.EncodingRandomness)) : (Env.stop a : Env L α).run W.host s = PMF.pure a :=
  rfl
theorem run_draw (β : Type) (d : PMF β) (k : β → Env L α) (s : ℕ × (ℕ → L.EncodingRandomness)) :
    (Env.draw β d k).run W.host s = d.bind fun y => (k y).run W.host s := rfl
theorem run_fresh (k : Sess L.link → Env L α) (c : ℕ) (f : ℕ → L.EncodingRandomness) :
    (Env.fresh k).run W.host (c, f) =
      (unif L.EncodingRandomness).bind fun r =>
        (W.Lk (f 0) r).bind fun a => (k a).run W.host (c + 1, Function.update f (c + 1) r) := by
  show ((unif L.EncodingRandomness).bind fun r =>
        (W.Lk (f 0) r).map fun a =>
          (a, ((c + 1, Function.update f (c + 1) r) : ℕ × (ℕ → L.EncodingRandomness)))).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
theorem run_session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X)
    (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) (k : BSess L.onlineBatch J → Env L α) (s : ℕ × (ℕ → L.EncodingRandomness)) :
    (Env.session e J xs rest k).run W.host s =
      (W.B (s.2 e) J xs rest).bind fun a => (k a).run W.host s := by
  show ((W.B (s.2 e) J xs rest).map fun a => (a, s)).bind (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem run_read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → Env L α) (s : ℕ × (ℕ → L.EncodingRandomness)) :
    (Env.read e p k).run W.host s = (k (W.y (s.2 e) p)).run W.host s := by
  show (PMF.pure (W.y (s.2 e) p, s)).bind (fun q => (k q.1).run W.host q.2) = _
  rw [PMF.pure_bind]
end HostEqs

/-! ## Part 2. The game with all randomness drawn at the start -/

/-- The calls: those of Compile.BatchLife, and single reads of an encoding. -/
abbrev WCall (ι X : Type) (N n : ℕ) : Type := Call ι X N ⊕ (ι × Fin n)

def WAns (L : BatchProtocol I X) {ι : Type} : WCall ι X L.maxBatchSize L.wordLength → Type
  | .inl c => Ans L c
  | .inr _ => L.Symbol

/-- The answers, for the encoding randomness r e of the encoding e. -/
def Laws.O (W : Laws L) {ι : Type} (r : ι → L.EncodingRandomness) : ∀ c : WCall ι X L.maxBatchSize L.wordLength, PMF (WAns L c)
  | .inl (.test e) => W.T (r e)
  | .inl (.link e e') => W.Lk (r e) (r e')
  | .inl (.bat e J xs rest) => W.B (r e) J xs rest
  | .inr (e, p) => PMF.pure (W.y (r e) p)

/-- The name of the encoded index number e among M + 1 names. -/
def nm (M e : ℕ) : Fin (M + 1) := ⟨min e M, Nat.lt_succ_of_le (Nat.min_le_right e M)⟩

theorem nm_val {M e : ℕ} (h : e ≤ M) : ((nm M e : Fin (M + 1)) : ℕ) = e := Nat.min_eq_left h
theorem nm_coe {M : ℕ} (e : Fin (M + 1)) : nm M e = e := Fin.ext (nm_val (Nat.le_of_lt_succ e.2))
theorem nm_inj {M e e' : ℕ} (h : e ≤ M) (h' : e' ≤ M) : nm M e = nm M e' ↔ e = e' :=
  ⟨fun hh => by rw [← nm_val h, ← nm_val h', hh], fun hh => by rw [hh]⟩

/-- The environment, when c further encoded indices exist, as an adversary of that game. -/
def toPlay (M : ℕ) : Env L α → ℕ → Play (WCall (Fin (M + 1)) X L.maxBatchSize L.wordLength) (WAns L) α
  | .stop a, _ => .done a
  | .fresh k, c => .call (.inl (.link (nm M 0) (nm M (c + 1)))) fun (a : Sess L.link) => toPlay M (k a) (c + 1)
  | .session e J xs rest k, c => .call (.inl (.bat (nm M e) J xs rest)) fun (a : BSess L.onlineBatch J) => toPlay M (k a) c
  | .read e p k, c => .call (.inr (nm M e, p)) fun (y : L.Symbol) => toPlay M (k y) c
  | .draw β d k, c => .draw β d fun y => toPlay M (k y) c

/-- With the offline phase in front. -/
def whole (M : ℕ) (E : Sess L.offline → Env L α) : Play (WCall (Fin (M + 1)) X L.maxBatchSize L.wordLength) (WAns L) α :=
  .call (.inl (.test (nm M 0))) fun (a : Sess L.offline) => toPlay M (E a) 0

/-! ## Part 3. For an environment within its bounds, drawing when asked is drawing at the start -/

/-- The encodings 0, .., c have the randomness f, the later ones that of the tuple. -/
def merge {M : ℕ} {R : Type} (c : ℕ) (f : ℕ → R) (tab : Fin (M + 1) → R) : Fin (M + 1) → R :=
  fun e => if (e : ℕ) ≤ c then f e else tab e

theorem merge_nm {M : ℕ} {R : Type} {c e : ℕ} (f : ℕ → R) (tab : Fin (M + 1) → R)
    (he : e ≤ c) (hc : c ≤ M) :
    merge c f tab (nm M e) = f e := by
  unfold merge
  rw [nm_val (he.trans hc), if_pos he]

theorem merge_update {M : ℕ} {R : Type} {c : ℕ} (f : ℕ → R) (tab : Fin (M + 1) → R)
    (r : R) (hc : c + 1 ≤ M) :
    merge c f (Function.update tab (nm M (c + 1)) r) =
      merge (c + 1) (Function.update f (c + 1) r) tab := by
  funext e
  have hv : ((nm M (c + 1) : Fin (M + 1)) : ℕ) = c + 1 := nm_val hc
  unfold merge
  by_cases h1 : (e : ℕ) ≤ c
  · have h3 : (e : ℕ) ≠ c + 1 := by omega
    rw [if_pos h1, if_pos (Nat.le_succ_of_le h1), Function.update_of_ne h3]
  · by_cases h2 : (e : ℕ) = c + 1
    · have he : e = nm M (c + 1) := Fin.ext (h2.trans hv.symm)
      rw [if_neg h1, if_pos (le_of_eq h2), h2, Function.update_self, he, Function.update_self]
    · have he : e ≠ nm M (c + 1) := fun hh => h2 (by rw [hh, hv])
      have h4 : ¬ (e : ℕ) ≤ c + 1 := by omega
      rw [if_neg h1, if_neg h4, Function.update_of_ne he]

theorem merge_zero {M : ℕ} {R : Type} (tab : Fin (M + 1) → R) (r : R) :
    Function.update tab (nm M 0) r = merge 0 (fun _ => r) tab := by
  funext e
  unfold merge
  by_cases h : (e : ℕ) ≤ 0
  · have he : e = nm M 0 := Fin.ext ((Nat.le_zero.1 h).trans (nm_val (Nat.zero_le M)).symm)
    rw [if_pos h, he, Function.update_self]
  · have he : e ≠ nm M 0 := fun hh => h (by rw [hh, nm_val (Nat.zero_le M)])
    rw [if_neg h, Function.update_of_ne he]

theorem run_eq (W : Laws L) {B : Bounds} {ok : X → Prop} (t : Env L α) :
    ∀ (c : ℕ) (f : ℕ → L.EncodingRandomness) (us ur : ℕ → ℕ), t.Adm B ok c us ur → c ≤ B.nenc →
      t.run W.host (c, f) =
        (unif (Fin (B.nenc + 1) → L.EncodingRandomness)).bind fun tab =>
          (toPlay B.nenc t c).run (W.O (merge c f tab)) := by
  induction t with
  | stop a =>
    intro c f us ur _ _
    simp only [run_stop, toPlay, Play.run_done, PMF.bind_const]
  | draw β d k ih =>
    intro c f us ur h hc
    simp only [run_draw, toPlay, Play.run_draw]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun y => ih y c f us ur (h y) hc)
  | session e J xs rest k ih =>
    intro c f us ur h hc
    obtain ⟨he, -, -, -, -, h6⟩ := h
    simp only [run_session, toPlay, Play.run_call, Laws.O, merge_nm f _ he hc]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ ur (h6 a) hc)
  | read e p k ih =>
    intro c f us ur h hc
    obtain ⟨he, -, h3⟩ := h
    simp only [run_read, toPlay, Play.run_call, Laws.O, merge_nm f _ he hc, PMF.pure_bind]
    exact ih _ c f us _ (h3 _) hc
  | fresh k ih =>
    intro c f us ur h hc
    obtain ⟨hlt, h2⟩ := h
    simp only [run_fresh, toPlay, Play.run_call, Laws.O]
    rw [← unif_resample (nm B.nenc (c + 1))]
    refine congrArg _ (funext fun r => ?_)
    have h0 : ∀ tab : Fin (B.nenc + 1) → L.EncodingRandomness,
        merge (c + 1) (Function.update f (c + 1) r) tab (nm B.nenc 0) = f 0 := fun tab => by
      rw [merge_nm _ _ (Nat.zero_le _) hlt, Function.update_of_ne (Nat.succ_ne_zero c).symm]
    have h1 : ∀ tab : Fin (B.nenc + 1) → L.EncodingRandomness,
        merge (c + 1) (Function.update f (c + 1) r) tab (nm B.nenc (c + 1)) = r := fun tab => by
      rw [merge_nm _ _ le_rfl hlt, Function.update_self]
    simp only [merge_update f _ r hlt, h0, h1]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a (c + 1) _ us ur (h2 a) hlt)

theorem view_eq (W : Laws L) {B : Bounds} {ok : X → Prop} {us ur : ℕ → ℕ}
    (E : Sess L.offline → Env L α) (hE : ∀ a, (E a).Adm B ok 0 us ur) :
    W.host.view E =
      (unif (Fin (B.nenc + 1) → L.EncodingRandomness)).bind fun tab => (whole B.nenc E).run (W.O tab) := by
  unfold whole
  simp only [view_host, Play.run_call, Laws.O]
  rw [← unif_resample (nm B.nenc 0)]
  refine congrArg _ (funext fun r => ?_)
  simp only [merge_zero, merge_nm (fun _ => r) _ le_rfl (Nat.zero_le B.nenc)]
  rw [Prob.bind_comm]
  exact congrArg _ (funext fun a => run_eq W (E a) 0 _ us ur (hE a) (Nat.zero_le _))

/-! ## Part 4. The lifetime theorem with single reads -/

section Life
variable {ι : Type}

/-- A call is allowed: all instances of a batch, those of the hidden slots included, are ok. -/
def okW (ok : X → Prop) {N n : ℕ} : WCall ι X N n → Prop
  | .inl (.bat _ _ xs rest) => (∀ j, ok (xs j)) ∧ ∀ j x, rest j = some x → ok x
  | _ => True

def errW (zT zL zO : ℝ≥0∞) {N n : ℕ} : WCall ι X N n → ℝ≥0∞
  | .inl c => err zT zL zO c
  | .inr _ => 0

def loadW [DecidableEq ι] (qT qpar qch qon : ℕ) {N n : ℕ} : WCall ι X N n → ι → ℕ
  | .inl c => load qT qpar qch qon c
  | .inr (e, _) => fun a => if a = e then 1 else 0

/-- The simulated runs, and the single reads, as algorithms that read the table whose row e is the
encoding e. -/
def simRW (L : BatchProtocol I X) (Sm : Sims L) :
    ∀ c : WCall ι X L.maxBatchSize L.wordLength, Reader (ι × Fin L.wordLength) (fun _ => L.Symbol) (WAns L c)
  | .inl c => simR L Sm c
  | .inr (e, p) => .read (e, p) fun y => .done y

theorem run_simRW (Sm : Sims L) (j : I) (r : ι → L.EncodingRandomness) (c : WCall ι X L.maxBatchSize L.wordLength) :
    (simRW L Sm c).run (fun p => L.encodeIndex j (r p.1) p.2) = (simLaws L Sm j).O r c := by
  rcases c with c | ⟨e, p⟩
  · refine (run_simR L Sm (fun e => L.encodeIndex j (r e)) c).trans ?_
    cases c <;> rfl
  · rfl

variable [DecidableEq ι]

theorem adds_simRW {b qT qpar qch qon : ℕ} (hR : L.Reads b qT qpar qch qon)
    (Sm : Sims L) (c : WCall ι X L.maxBatchSize L.wordLength) :
    Adds (simRW L Sm c) (loadW qT qpar qch qon c) := by
  rcases c with c | ⟨e, p⟩
  · exact adds_simR hR Sm c
  · intro S y a
    show rowCard (insert (e, p) S) a ≤ rowCard S a + if a = e then 1 else 0
    unfold rowCard
    by_cases h : a = e
    · rw [if_pos h, Finset.filter_insert]
      split_ifs
      · exact Finset.card_insert_le _ _
      · exact Nat.le_succ _
    · rw [if_neg h, Finset.filter_insert, if_neg (fun hh : e = a => h hh.symm)]
      exact le_rfl

variable [Fintype ι]

/-- What the theorem needs of the real side: its symbols are those of the encodings of i, and each
of its runs is near the simulated run on the true encodings, for every value of the encoding
randomness (of a batch under `∀ j, ok (xs j)` and `∀ j x, rest j = some x → ok x`: field `B` below).
-/
structure Laws.Near (W : Laws L) (Sm : Sims L) (i : I) (ok : X → Prop) (zT zL zO : ℝ≥0∞) :
    Prop where
  y  : ∀ r p, W.y r p = L.encodeIndex i r p
  T  : ∀ r, tv (W.T r) (simSess L.offline Sm.T () (L.encodeIndex i r)) ≤ zT
  Lk : ∀ r r', tv (W.Lk r r') (simSess L.link Sm.Lk () (L.encodeIndex i r, L.encodeIndex i r')) ≤ zL
  B  : ∀ r J xs rest, (∀ j, ok (xs j)) → (∀ j x, rest j = some x → ok x) →
    tv (W.B r J xs rest) (simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i r)) ≤ J.card * zO

theorem lifetimeW {ok : X → Prop} {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞}
    (hR : L.Reads b qT qpar qch qon) {Sm : Sims L} {W : Laws L} {i : I}
    (hN : W.Near Sm i ok zT zL zO) (i₀ : I) (t : Play (WCall ι X L.maxBatchSize L.wordLength) (WAns L) α)
    (hok : t.Calls (okW ok)) (hfit : t.Fits (loadW qT qpar qch qon) b fun _ => 0) :
    tv ((unif (ι → L.EncodingRandomness)).bind fun r => t.run (W.O r))
        ((unif (ι → L.EncodingRandomness)).bind fun r => t.run ((simLaws L Sm i₀).O r)) ≤
      t.cost (errW zT zL zO) := by
  have h := lifetime_abstract (unif (ι → L.EncodingRandomness))
    (fun r => fun p : ι × Fin L.wordLength => L.encodeIndex i (r p.1) p.2)
    ((unif (ι → L.EncodingRandomness)).map fun r => fun p : ι × Fin L.wordLength => L.encodeIndex i₀ (r p.1) p.2) (fun r => W.O r)
    (simRW L Sm) (okW ok) (errW zT zL zO) (fun T => ∀ e, rowCard T e ≤ b) ?_ ?_ t hok ?_
  · rw [PMF.bind_map] at h
    have e1 : ∀ r : ι → L.EncodingRandomness,
        (t.run fun c => (simRW L Sm c).run fun p : ι × Fin L.wordLength => L.encodeIndex i₀ (r p.1) p.2) =
          t.run ((simLaws L Sm i₀).O r) :=
      fun r => congrArg t.run (funext fun c => run_simRW Sm i₀ r c)
    simp only [← e1]
    exact h
  · intro r c hc
    rw [run_simRW Sm i r c]
    rcases c with (e | ⟨e, e'⟩ | ⟨e, J, xs, rest⟩) | ⟨e, p⟩
    · exact hN.T (r e)
    · exact hN.Lk (r e) (r e')
    · exact hN.B (r e) J xs rest hc.1 hc.2
    · show tv (PMF.pure (W.y (r e) p)) (PMF.pure (L.encodeIndex i (r e) p)) ≤ 0
      rw [hN.y, tv_self]
  · exact fun S hSb =>
      rows_law (fun _ r => L.encodeIndex i r) (fun _ r => L.encodeIndex i₀ r) b
        (fun _ T hT => hR.hidE T hT i i₀) S hSb
  · exact Play.within_plug (adds_simRW hR Sm) t (fun _ => 0) ∅ (fun e => by rw [rowCard_empty]) hfit

/-- Under `hW` and `hS`: the real side of Hiop/Whole.lean is near good simulators. -/
theorem near_real {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞} (hW : L.Wired) {Sm : Sims L}
    (hS : Sm.Good Ryes zT zL zO) (i : I) :
    (realLaws L i).Near Sm i (Ryes i) zT zL zO where
  y := fun _ _ => rfl
  T := fun r => by
    have h1 := tv_sess_le L.honestOfflineProver Sm.T (i, r) () (hS.goodT (i, r) ())
    rw [hW.extT] at h1
    exact h1
  Lk := fun r r' => by
    have h1 := tv_sess_le L.honestLinkProver Sm.Lk (i, r, r') () (hS.goodL (i, r, r') ())
    rw [hW.extL] at h1
    exact h1
  B := fun r J xs rest h1 h2 => by
    have h3 := tv_bsess_le L.honestOnlineBatchProver Sm.B (i, r) (vec J xs rest) J xs
      (hS.goodB (i, r) (vec J xs rest) (valid_vec J xs rest h1 h2) J xs (vec_of_mem J xs rest))
    rw [hW.extB] at h3
    exact h3

end Life

/-! ## Part 5. An environment within its bounds -/

section Nice
variable {B : Bounds} {ok : X → Prop}

theorem calls_toPlay (t : Env L α) :
    ∀ (c : ℕ) (us ur : ℕ → ℕ), t.Adm B ok c us ur → (toPlay B.nenc t c).Calls (okW ok) := by
  induction t with
  | stop a => intro c us ur _; exact trivial
  | draw β d k ih => intro c us ur h; exact fun y => ih y c us ur (h y)
  | session e J xs rest k ih =>
    intro c us ur h
    exact ⟨⟨h.2.2.2.1, h.2.2.2.2.1⟩, fun a => ih a c _ ur (h.2.2.2.2.2 a)⟩
  | read e p k ih => intro c us ur h; exact ⟨trivial, fun y => ih y c us _ (h.2.2 y)⟩
  | fresh k ih => intro c us ur h; exact ⟨trivial, fun a => ih a (c + 1) us ur (h.2 a)⟩

/-- What the encoded index j may still be asked for fits beside the load that it carries. -/
def Inv (B : Bounds) (b qpar qch qon c : ℕ) (us ur : ℕ → ℕ) (ld : Fin (B.nenc + 1) → ℕ) : Prop :=
  ∀ j, j ≤ B.nenc →
    ld (nm B.nenc j) + (if j = 0 then (B.nenc - c) * qpar else if c < j then qch else 0) +
        (B.sess j - us j) * qon + (B.reads j - ur j) ≤ b

theorem fits_toPlay {b qT qpar qch qon : ℕ} (t : Env L α) :
    ∀ (c : ℕ) (us ur : ℕ → ℕ) (ld : Fin (B.nenc + 1) → ℕ), t.Adm B ok c us ur → c ≤ B.nenc →
      Inv B b qpar qch qon c us ur ld → (toPlay B.nenc t c).Fits (loadW qT qpar qch qon) b ld := by
  induction t with
  | stop a =>
    intro c us ur ld _ _ hI e
    have h := hI e (Nat.le_of_lt_succ e.2)
    rw [nm_coe] at h
    omega
  | draw β d k ih => intro c us ur ld h hc hI; exact fun y => ih y c us ur ld (h y) hc hI
  | session e J xs rest k ih =>
    intro c us ur ld h hc hI a
    obtain ⟨he, hs, -, -, -, h6⟩ := h
    refine ih a c _ ur _ (h6 a) hc fun j hj => ?_
    have h := hI j hj
    show ld (nm B.nenc j) + (if nm B.nenc j = nm B.nenc e then qon else 0) + _ + _ + _ ≤ b
    by_cases hje : j = e
    · subst hje
      have e1 : (B.sess j - us j) * qon = (B.sess j - (us j + 1)) * qon + qon := by
        have : B.sess j - us j = (B.sess j - (us j + 1)) + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul]
      rw [if_pos rfl, Function.update_self]
      omega
    · rw [if_neg (fun hh => hje ((nm_inj hj (he.trans hc)).1 hh)), Function.update_of_ne hje]
      omega
  | read e p k ih =>
    intro c us ur ld h hc hI y
    obtain ⟨he, hs, h3⟩ := h
    refine ih y c us _ _ (h3 y) hc fun j hj => ?_
    have h := hI j hj
    show ld (nm B.nenc j) + (if nm B.nenc j = nm B.nenc e then 1 else 0) + _ + _ + _ ≤ b
    by_cases hje : j = e
    · subst hje
      rw [if_pos rfl, Function.update_self]
      omega
    · rw [if_neg (fun hh => hje ((nm_inj hj (he.trans hc)).1 hh)), Function.update_of_ne hje]
      omega
  | fresh k ih =>
    intro c us ur ld h hc hI a
    obtain ⟨hlt, h2⟩ := h
    refine ih a (c + 1) us ur _ (h2 a) hlt fun j hj => ?_
    have h := hI j hj
    show ld (nm B.nenc j) +
        ((if nm B.nenc j = nm B.nenc 0 then qpar else 0) +
          if nm B.nenc j = nm B.nenc (c + 1) then qch else 0) +
        _ + _ + _ ≤ b
    have e1 : (B.nenc - c) * qpar = (B.nenc - (c + 1)) * qpar + qpar := by
      have : B.nenc - c = (B.nenc - (c + 1)) + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, if_neg (fun hh => Nat.succ_ne_zero c ((nm_inj hj hlt).1 hh).symm), if_pos rfl]
      rw [if_pos rfl] at h
      omega
    · rw [if_neg (fun hh => hj0 ((nm_inj hj (Nat.zero_le _)).1 hh)), if_neg hj0]
      rw [if_neg hj0] at h
      by_cases hj1 : j = c + 1
      · subst hj1
        rw [if_pos rfl, if_neg (Nat.lt_irrefl _)]
        rw [if_pos (Nat.lt_succ_self c)] at h
        omega
      · rw [if_neg (fun hh => hj1 ((nm_inj hj hlt).1 hh))]
        by_cases hj2 : c < j
        · rw [if_pos hj2] at h
          rw [if_pos (by omega)]
          omega
        · rw [if_neg hj2] at h
          rw [if_neg (by omega)]
          omega

/-- The sessions that may still be asked for. -/
def left (B : Bounds) (us : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range (B.nenc + 1), (B.sess j - us j)

theorem left_step {us : ℕ → ℕ} {e : ℕ} (he : e ≤ B.nenc) (h : us e < B.sess e) :
    left B us = left B (Function.update us e (us e + 1)) + 1 := by
  have hmem : e ∈ Finset.range (B.nenc + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le he)
  unfold left
  rw [← Finset.add_sum_erase _ (fun j => B.sess j - us j) hmem,
    ← Finset.add_sum_erase _ (fun j => B.sess j - Function.update us e (us e + 1) j) hmem]
  have h1 : ∑ j ∈ (Finset.range (B.nenc + 1)).erase e,
        (B.sess j - Function.update us e (us e + 1) j) =
      ∑ j ∈ (Finset.range (B.nenc + 1)).erase e, (B.sess j - us j) :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h1]
  simp only [Function.update_self]
  omega

theorem cost_toPlay {zT zL zO : ℝ≥0∞} (t : Env L α) :
    ∀ (c : ℕ) (us ur : ℕ → ℕ), t.Adm B ok c us ur → c ≤ B.nenc →
      (toPlay B.nenc t c).cost (errW zT zL zO) ≤
        ((B.nenc - c : ℕ) : ℝ≥0∞) * zL + (left B us : ℝ≥0∞) * (B.shown * zO) := by
  induction t with
  | stop a => intro c us ur _ _; exact zero_le _
  | draw β d k ih =>
    intro c us ur h hc
    simp only [toPlay, Play.cost_draw]
    exact iSup_le fun y => ih y c us ur (h y) hc
  | session e J xs rest k ih =>
    intro c us ur h hc
    obtain ⟨he, hs, hJ, -, -, h6⟩ := h
    simp only [toPlay, Play.cost_call]
    have h1 : (⨆ a, (toPlay B.nenc (k a) c).cost (errW zT zL zO)) ≤
        ((B.nenc - c : ℕ) : ℝ≥0∞) * zL +
          (left B (Function.update us e (us e + 1)) : ℝ≥0∞) * (B.shown * zO) :=
      iSup_le fun a => ih a c _ ur (h6 a) hc
    have h2 : errW zT zL zO
          (.inl (.bat (nm B.nenc e) J xs rest) : WCall (Fin (B.nenc + 1)) X L.maxBatchSize L.wordLength) ≤
        B.shown * zO :=
      mul_le_mul' (Nat.cast_le.2 hJ) le_rfl
    refine (add_le_add h2 h1).trans (le_of_eq ?_)
    rw [left_step (he.trans hc) hs]
    push_cast
    ring
  | read e p k ih =>
    intro c us ur h hc
    simp only [toPlay, Play.cost_call]
    have h1 : (⨆ y, (toPlay B.nenc (k y) c).cost (errW zT zL zO)) ≤
        ((B.nenc - c : ℕ) : ℝ≥0∞) * zL + (left B us : ℝ≥0∞) * (B.shown * zO) :=
      iSup_le fun y => ih y c us _ (h.2.2 y) hc
    refine (add_le_add (le_refl _) h1).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | fresh k ih =>
    intro c us ur h hc
    obtain ⟨hlt, h2⟩ := h
    simp only [toPlay, Play.cost_call]
    have h1 : (⨆ a, (toPlay B.nenc (k a) (c + 1)).cost (errW zT zL zO))
        ≤ ((B.nenc - (c + 1) : ℕ) : ℝ≥0∞) * zL + (left B us : ℝ≥0∞) * (B.shown * zO) :=
      iSup_le fun a => ih a (c + 1) us ur (h2 a) hlt
    refine (add_le_add (le_refl _) h1).trans (le_of_eq ?_)
    show zL + _ = _
    have e1 : B.nenc - c = (B.nenc - (c + 1)) + 1 := by omega
    rw [e1]
    push_cast
    ring

end Nice

/-! ## Part 6. The theorems -/

/-- The theorem for any real side that is near the simulated runs. (not all hypotheses are named
here: see the statement below) -/
theorem tv_view_le {ok : X → Prop} {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞}
    (hR : L.Reads b qT qpar qch qon) {Sm : Sims L} {W : Laws L} {i : I}
    (hN : W.Near Sm i ok zT zL zO) {B : Bounds} (hB : B.Fits b qT qpar qch qon) (i₀ : I)
    (E : Sess L.offline → Env L α) (hE : ∀ a, (E a).Adm B ok 0 (fun _ => 0) fun _ => 0) :
    tv (W.host.view E) ((simWhole L Sm i₀).host.view E) ≤ B.err zT zL zO := by
  rw [simHost_eq, view_eq _ E hE, view_eq _ E hE]
  refine (lifetimeW hR hN i₀ (whole B.nenc E)
    ⟨trivial, fun a => calls_toPlay (E a) 0 _ _ (hE a)⟩ ?_).trans ?_
  · intro a
    refine fits_toPlay (E a) 0 _ _ _ (hE a) (Nat.zero_le _) fun j hj => ?_
    show 0 + (if nm B.nenc j = nm B.nenc 0 then qT else 0) + _ + _ + _ ≤ b
    by_cases hj0 : j = 0
    · subst hj0
      have h := hB.1
      rw [if_pos rfl, if_pos rfl]
      simp only [Nat.sub_zero]
      omega
    · have h := hB.2 j (Nat.pos_of_ne_zero hj0) hj
      rw [if_neg (fun hh => hj0 ((nm_inj hj (Nat.zero_le _)).1 hh)),
        if_neg hj0, if_pos (Nat.pos_of_ne_zero hj0)]
      simp only [Nat.sub_zero]
      omega
  · unfold whole
    rw [Play.cost_call]
    have h1 : (⨆ a, (toPlay B.nenc (E a) 0).cost (errW zT zL zO)) ≤
        ((B.nenc - 0 : ℕ) : ℝ≥0∞) * zL + (left B (fun _ => 0) : ℝ≥0∞) * (B.shown * zO) :=
      iSup_le fun a => cost_toPlay (E a) 0 _ _ (hE a) (Nat.zero_le _)
    refine (add_le_add (le_refl _) h1).trans (le_of_eq ?_)
    show zT + _ = _
    unfold Bounds.err Bounds.total left
    simp only [Nat.sub_zero]
    ring

theorem hvzk_whole : Spec.hvzk_whole := fun _ _ _ _ _ _ _ _ _ _ _ _ hW hR _ hS _ hB i₀ i _ E hE =>
  tv_view_le hR (near_real hW hS i) hB i₀ E hE

theorem hvzk_whole_hiding : Spec.hvzk_whole_hiding := by
  intro I X L Ryes b qT qpar qch qon zT zL zO hW hR hH
  obtain ⟨Sm, hS⟩ := exists_sims hH
  exact ⟨Sm, fun B hB i₀ => hvzk_whole I X L Ryes b qT qpar qch qon zT zL zO hW hR Sm hS B hB i₀⟩

theorem hvzk_view : Spec.hvzk_view := by
  intro I X L Ryes B S z h i Ω ν F n hF
  exact h i _ _ fun a ω => hF ω a

end Hiop
