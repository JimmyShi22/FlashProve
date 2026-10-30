-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/FormProof.lean: proof of `Spec.form_laws` of Hiop/Seeded/Form.lean.

The proof follows Hiop/RecWholeProof.lean: replace each run by its simulated run, which still reads
the true encodings; then see environment and simulated runs as one algorithm that reads a table with
independent rows, each row with one free place for the out-of-domain (OOD) sample
(Hiop/RecWholeKit.lean, which is called as it stands).
What is new. There a row's randomness is (committer's randomness, seed), all rows are drawn at the
start, and so the seed has to be uniform and independent of what was shown. Here the environment
names the seeds on its way. The cure: A ROW IS NAMED BY (number of the encoded index, seed), and its
randomness is the committer's randomness alone. There is one independent row for EVERY such pair,
all drawn at the start. The environment names one seed for each number, so of all the rows with that
number it only ever touches one: naming a seed is choosing which row is read. The law of a row at
its free place and any b word places does not depend on the index: that is the premise `HidE` at the
row's own seed, with no averaging.
Rows whose seed is not in Gs are never touched by an admissible environment. For the comparison of
tables they are filled with encodings of i₀ on both sides (`idxS`).
 Part 0: a simulated run (`RunSim`) as an algorithm that reads a table;
 Part 1: the simulator of the theorem is the host of a family of laws;
 Part 2: the game with all randomness drawn at the start (`FCall`, `LawsF.O`); the environment as an
   adversary of that game (`toPlayF`, `wholeF`), which keeps the seeds that it has named;
 Part 3: for an environment within its bounds, drawing when asked is drawing at the start
   (`runF_eq`, `viewF_eq`);
 Part 4: the row law, the simulated runs as readers of the table (`simRF`), their loads, the
   lifetime theorem (`lifetimeF`, by `lifetimeD`);
 Part 5: an environment within its bounds makes allowed calls, keeps every row within the budget,
   and its errors add up to at most the error of the statement;
 Part 6: the theorem; an environment that draws coins before it names the first seed (`PreF`).

Limits: see the head of Hiop/Seeded/Whole.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Form
import Hiop.RecWholeProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime Compile.BatchLife Hiop.Free
open scoped ENNReal
open scoped Classical

variable {I X : Type} {L : HolographicProtocol I X} {F : Form X} {α : Type}

/-! ## Part 0. A simulated run as an algorithm that reads a table -/

section Run
variable {Pos Sym Out P : Type}

/-- The simulated run as an algorithm that reads a table: position q of the word(s) is the place
loc q. -/
def RunSim.reader (R : RunSim Pos Sym Out) (loc : Pos → P) : Reader P (fun _ => Sym) Out :=
  .draw R.Aux R.μ fun a =>
    readK loc (R.reads a).toList (fun _ => none) fun ans =>
      .draw Out (R.out a ans) fun o => .done o

open Classical in
theorem run_reader (R : RunSim Pos Sym Out) (loc : Pos → P) (f : P → Sym) (str : Pos → Sym)
    (h : ∀ q, str q = f (loc q)) : (R.reader loc).run f = R.law str := by
  unfold RunSim.reader RunSim.law
  rw [Reader.run_draw]
  congr 1
  funext a
  rw [run_readK, Reader.run_draw]
  have h1 : (fun q => if q ∈ (R.reads a).toList then some (f (loc q)) else none) =
      fun p => if p ∈ R.reads a then some (str p) else none := by
    funext q
    by_cases hq : q ∈ R.reads a <;> simp [hq, h]
  rw [h1]
  exact PMF.bind_pure _

/-- It reads the places of its positions and no others. -/
theorem within_reader [DecidableEq P] (R : RunSim Pos Sym Out) (loc : Pos → P)
    {good : Finset P → Prop} (S : Finset P) (h : ∀ a, good (S ∪ (R.reads a).image loc)) :
    (R.reader loc).Within good S := by
  intro a
  refine within_readK loc _ _ _ S fun acc' o => ?_
  have h1 : ((R.reads a).toList.map loc).toFinset = (R.reads a).image loc := by
    ext p
    simp
  show good _
  rw [h1]
  exact h a

end Run

/-! ## Part 1. The simulator's host is the host of a family of laws -/

theorem simHostF_eq (Sm : SimsF L F) (i₀ : I) :
    (simWholeF L F Sm i₀).host = (simLawsF L F Sm i₀).host := rfl

section HostEqs
variable (W : LawsF L F)
abbrev StS (L : HolographicProtocol I X) : Type := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)

theorem viewF_host (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α) :
    W.host.view s₀ E =
      (unif L.EncodingRandomness).bind fun r => (E (W.rc (r, s₀))).run W.host (0, fun _ => (r, s₀)) := by
  show ((unif L.EncodingRandomness).map fun r => (W.rc (r, s₀), ((0, fun _ => (r, s₀)) : StS L))).bind
      (fun p => (E p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runF_stop (a : α) (st : StS L) :
    (EnvF.stop a : EnvF L F α).run W.host st = PMF.pure a := rfl
theorem runF_draw (β : Type) (d : PMF β) (k : β → EnvF L F α) (st : StS L) :
    (EnvF.draw β d k).run W.host st = d.bind fun y => (k y).run W.host st := rfl
theorem runF_fresh (s : L.OutOfDomainSeed) (k : L.Rec → EnvF L F α) (c : ℕ) (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) :
    (EnvF.fresh s k).run W.host (c, f) =
      (unif L.EncodingRandomness).bind fun r =>
        (k (W.rc (r, s))).run W.host (c + 1, Function.update f (c + 1) (r, s)) := by
  show ((unif L.EncodingRandomness).map fun r =>
        (W.rc (r, s), ((c + 1, Function.update f (c + 1) (r, s)) : StS L))).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runF_test (e : ℕ) (k : F.RT → EnvF L F α) (st : StS L) :
    (EnvF.test e k).run W.host st = (W.T e (st.2 e)).bind fun a => (k a).run W.host st := by
  show ((W.T e (st.2 e)).map fun a => (a, st)).bind (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runF_link (e : ℕ) (k : F.RL → EnvF L F α) (st : StS L) :
    (EnvF.link e k).run W.host st =
      (W.Lk e (st.2 0) (st.2 e)).bind fun a => (k a).run W.host st := by
  show ((W.Lk e (st.2 0) (st.2 e)).map fun a => (a, st)).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runF_session (e : ℕ) (q : F.QB) (h : F.HB q) (k : F.RB q → EnvF L F α) (st : StS L) :
    (EnvF.session e q h k).run W.host st =
      (W.B e (st.2 e) q h).bind fun a => (k a).run W.host st := by
  show ((W.B e (st.2 e) q h).map fun a => (a, st)).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runF_read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → EnvF L F α) (st : StS L) :
    (EnvF.read e p k).run W.host st = (k (W.y (st.2 e) p)).run W.host st := by
  show (PMF.pure (W.y (st.2 e) p, st)).bind (fun q => (k q.1).run W.host q.2) = _
  rw [PMF.pure_bind]
end HostEqs

/-! ## Part 2. The game with all randomness drawn at the start -/

/-- The calls. a, a' name rows of the table; e is the number of the encoded index, which is handed
on to the law of the run and to its simulator. -/
inductive FCall (ι : Type) {X : Type} (F : Form X) (n : ℕ) : Type
  /-- show the OOD sample of the row a -/
  | rcd (a : ι) : FCall ι F n
  | test (a : ι) (e : ℕ) : FCall ι F n
  | link (a a' : ι) (e : ℕ) : FCall ι F n
  | bat (a : ι) (e : ℕ) (q : F.QB) (h : F.HB q) : FCall ι F n
  | read (a : ι) (p : Fin n) : FCall ι F n

def FAns (L : HolographicProtocol I X) (F : Form X) {ι : Type} : FCall ι F L.wordLength → Type
  | .rcd _ => L.Rec
  | .test _ _ => F.RT
  | .link _ _ _ => F.RL
  | .bat _ _ q _ => F.RB q
  | .read _ _ => L.Symbol

/-- The answers, when the row a has the seed sd a and the committer's randomness r a. -/
def LawsF.O (W : LawsF L F) {ι : Type} (sd : ι → L.OutOfDomainSeed) (r : ι → L.EncodingRandomness) :
    ∀ c : FCall ι F L.wordLength, PMF (FAns L F c)
  | .rcd a => PMF.pure (W.rc (r a, sd a))
  | .test a e => W.T e (r a, sd a)
  | .link a a' e => W.Lk e (r a, sd a) (r a', sd a')
  | .bat a e q h => W.B e (r a, sd a) q h
  | .read a p => PMF.pure (W.y (r a, sd a) p)

/-- The names of the rows: (name of an encoded index among M + 1 names, seed). -/
abbrev Row (L : HolographicProtocol I X) (M : ℕ) : Type := Fin (M + 1) × L.OutOfDomainSeed

/-- The environment, when c further encoded indices exist and g e is the seed that was named for the
encoded index e, as an adversary of that game. -/
def toPlayF (M : ℕ) : EnvF L F α → ℕ → (ℕ → L.OutOfDomainSeed) → Play (FCall (Row L M) F L.wordLength) (FAns L F) α
  | .stop a, _, _ => .done a
  | .fresh s k, c, g =>
    .call (.rcd (nm M (c + 1), s)) fun (a : L.Rec) =>
      toPlayF M (k a) (c + 1) (Function.update g (c + 1) s)
  | .test e k, c, g =>
    .call (.test (nm M e, g e) e) fun (a : F.RT) => toPlayF M (k a) c g
  | .link e k, c, g =>
    .call (.link (nm M 0, g 0) (nm M e, g e) e) fun (a : F.RL) => toPlayF M (k a) c g
  | .session e q h k, c, g =>
    .call (.bat (nm M e, g e) e q h) fun (a : F.RB q) => toPlayF M (k a) c g
  | .read e p k, c, g => .call (.read (nm M e, g e) p) fun (y : L.Symbol) => toPlayF M (k y) c g
  | .draw β d k, c, g => .draw β d fun y => toPlayF M (k y) c g

/-- With the first OOD sample in front. -/
def wholeF (M : ℕ) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α) :
    Play (FCall (Row L M) F L.wordLength) (FAns L F) α :=
  .call (.rcd (nm M 0, s₀)) fun (a : L.Rec) => toPlayF M (E a) 0 fun _ => s₀

/-! ## Part 3. Drawing when asked is drawing at the start -/

/-- For e = 0, .., c the row (e, seed of e) has the randomness that f says; all other rows have that
of the tuple. -/
def mergeS {M : ℕ} (c : ℕ) (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) (tab : Row L M → L.EncodingRandomness) : Row L M → L.EncodingRandomness :=
  fun x => if (x.1 : ℕ) ≤ c ∧ x.2 = (f x.1).2 then (f x.1).1 else tab x

theorem mergeS_nm {M c e : ℕ} (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) (tab : Row L M → L.EncodingRandomness)
    (he : e ≤ c) (hc : c ≤ M) :
    mergeS c f tab (nm M e, (f e).2) = (f e).1 := by
  have hv : ((nm M e : Fin (M + 1)) : ℕ) = e := nm_val (he.trans hc)
  show (if ((nm M e : Fin (M + 1)) : ℕ) ≤ c ∧ (f e).2 = (f ((nm M e : Fin (M + 1)) : ℕ)).2
    then (f ((nm M e : Fin (M + 1)) : ℕ)).1 else tab (nm M e, (f e).2)) = (f e).1
  rw [hv, if_pos ⟨he, rfl⟩]

theorem mergeS_update {M c : ℕ} (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) (tab : Row L M → L.EncodingRandomness)
    (r : L.EncodingRandomness) (s : L.OutOfDomainSeed) (hc : c + 1 ≤ M) :
    mergeS c f (Function.update tab (nm M (c + 1), s) r) =
      mergeS (c + 1) (Function.update f (c + 1) (r, s)) tab := by
  funext x
  obtain ⟨x1, x2⟩ := x
  have hv : ((nm M (c + 1) : Fin (M + 1)) : ℕ) = c + 1 := nm_val hc
  show (if (x1 : ℕ) ≤ c ∧ x2 = (f x1).2 then (f x1).1
      else Function.update tab (nm M (c + 1), s) r (x1, x2)) =
    if (x1 : ℕ) ≤ c + 1 ∧ x2 = (Function.update f (c + 1) (r, s) x1).2
      then (Function.update f (c + 1) (r, s) x1).1 else tab (x1, x2)
  by_cases h2 : (x1 : ℕ) = c + 1
  · have h1 : ¬ ((x1 : ℕ) ≤ c ∧ x2 = (f x1).2) := fun h => by
      have h0 := h.1
      omega
    have he : x1 = nm M (c + 1) := Fin.ext (h2.trans hv.symm)
    rw [if_neg h1, h2, Function.update_self]
    by_cases h3 : x2 = s
    · rw [if_pos ⟨le_rfl, h3⟩, he, h3, Function.update_self]
    · have hne : (x1, x2) ≠ (nm M (c + 1), s) := fun hh => h3 (congrArg Prod.snd hh)
      rw [Function.update_of_ne hne, if_neg fun h => h3 h.2]
  · have hne : (x1, x2) ≠ (nm M (c + 1), s) := fun hh => h2 (by
      have h0 : x1 = nm M (c + 1) := congrArg Prod.fst hh
      rw [h0, hv])
    rw [Function.update_of_ne hne, Function.update_of_ne h2]
    by_cases h4 : (x1 : ℕ) ≤ c ∧ x2 = (f x1).2
    · rw [if_pos h4, if_pos ⟨Nat.le_succ_of_le h4.1, h4.2⟩]
    · rw [if_neg h4, if_neg fun h => h4 ⟨by have h0 := h.1; omega, h.2⟩]

theorem mergeS_zero {M : ℕ} (tab : Row L M → L.EncodingRandomness) (r : L.EncodingRandomness) (s : L.OutOfDomainSeed) :
    Function.update tab (nm M 0, s) r = mergeS 0 (fun _ => (r, s)) tab := by
  funext x
  obtain ⟨x1, x2⟩ := x
  show Function.update tab (nm M 0, s) r (x1, x2) =
    if (x1 : ℕ) ≤ 0 ∧ x2 = s then r else tab (x1, x2)
  by_cases h : (x1 : ℕ) ≤ 0 ∧ x2 = s
  · have he : x1 = nm M 0 := Fin.ext ((Nat.le_zero.1 h.1).trans (nm_val (Nat.zero_le M)).symm)
    rw [if_pos h, he, h.2, Function.update_self]
  · have hne : (x1, x2) ≠ (nm M 0, s) := fun hh => h ⟨by
      have h0 : x1 = nm M 0 := congrArg Prod.fst hh
      rw [h0, nm_val (Nat.zero_le M)], congrArg Prod.snd hh⟩
    rw [if_neg h, Function.update_of_ne hne]

/-- the seeds of a state after one more encoded index -/
theorem snd_update (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) (k : ℕ) (r : L.EncodingRandomness) (s : L.OutOfDomainSeed) :
    (fun e => (Function.update f k (r, s) e).2) = Function.update (fun e => (f e).2) k s := by
  funext e
  by_cases h : e = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem runF_eq (W : LawsF L F) {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop}
    (t : EnvF L F α) :
    ∀ (c : ℕ) (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) (u : UsedR), t.Adm B Gs ok c u → c ≤ B.nenc →
      t.run W.host (c, f) =
        (unif (Row L B.nenc → L.EncodingRandomness)).bind fun tab =>
          (toPlayF B.nenc t c fun e => (f e).2).run (W.O Prod.snd (mergeS c f tab)) := by
  induction t with
  | stop a =>
    intro c f u _ _
    simp only [runF_stop, toPlayF, Play.run_done, PMF.bind_const]
  | draw β d k ih =>
    intro c f u h hc
    simp only [runF_draw, toPlayF, Play.run_draw]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun y => ih y c f u (h y) hc)
  | test e k ih =>
    intro c f u h hc
    obtain ⟨he, -, h3⟩ := h
    simp only [runF_test, toPlayF, Play.run_call, LawsF.O, mergeS_nm f _ he hc, Prod.mk.eta]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ (h3 a) hc)
  | link e k ih =>
    intro c f u h hc
    obtain ⟨-, he, -, h3⟩ := h
    simp only [runF_link, toPlayF, Play.run_call, LawsF.O,
      mergeS_nm f _ he hc, mergeS_nm f _ (Nat.zero_le c) hc, Prod.mk.eta]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ (h3 a) hc)
  | session e q hq k ih =>
    intro c f u h hc
    obtain ⟨he, -, -, -, h6⟩ := h
    simp only [runF_session, toPlayF, Play.run_call, LawsF.O, mergeS_nm f _ he hc, Prod.mk.eta]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ (h6 a) hc)
  | read e p k ih =>
    intro c f u h hc
    obtain ⟨he, -, h3⟩ := h
    simp only [runF_read, toPlayF, Play.run_call, LawsF.O, mergeS_nm f _ he hc, Prod.mk.eta,
      PMF.pure_bind]
    exact ih _ c f _ (h3 _) hc
  | fresh s k ih =>
    intro c f u h hc
    obtain ⟨-, hlt, h2⟩ := h
    simp only [runF_fresh, toPlayF, Play.run_call, LawsF.O, PMF.pure_bind]
    rw [← unif_resample (nm B.nenc (c + 1), s)]
    refine congrArg _ (funext fun r => ?_)
    have h1 : ∀ tab : Row L B.nenc → L.EncodingRandomness,
        mergeS (c + 1) (Function.update f (c + 1) (r, s)) tab (nm B.nenc (c + 1), s) = r :=
      fun tab => by
        have h0 := mergeS_nm (Function.update f (c + 1) (r, s)) tab (le_refl (c + 1)) hlt
        rw [Function.update_self] at h0
        exact h0
    simp only [mergeS_update f _ r s hlt, h1, ← snd_update f (c + 1) r s]
    exact ih _ (c + 1) _ u (h2 _) hlt

theorem viewF_eq (W : LawsF L F) {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {u : UsedR}
    (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α) (hE : ∀ a, (E a).Adm B Gs ok 0 u) :
    W.host.view s₀ E =
      (unif (Row L B.nenc → L.EncodingRandomness)).bind fun tab =>
        (wholeF B.nenc s₀ E).run (W.O Prod.snd tab) := by
  unfold wholeF
  simp only [viewF_host, Play.run_call, LawsF.O, PMF.pure_bind]
  rw [← unif_resample (nm B.nenc 0, s₀)]
  refine congrArg _ (funext fun r => ?_)
  have h1 : ∀ tab : Row L B.nenc → L.EncodingRandomness,
      mergeS 0 (fun _ => (r, s₀)) tab (nm B.nenc 0, s₀) = r := fun tab =>
    mergeS_nm (fun _ => (r, s₀)) tab le_rfl (Nat.zero_le B.nenc)
  simp only [mergeS_zero, h1]
  exact runF_eq W (E _) 0 _ u (hE _) (Nat.zero_le _)

/-! ## Part 4. The row law, the simulated runs as readers, the lifetime theorem -/

/-- At a seed of Gs the law of (OOD sample, any b positions) of an encoded index does not depend on
the index: `HidE`, with the seed written beside the answer. -/
theorem row_lawS {Gs : L.OutOfDomainSeed → Prop} {b : ℕ} (hR : HidE L Gs b)
    (T : Finset (Fin L.wordLength)) (hT : T.card ≤ b) (s : L.OutOfDomainSeed) (hs : Gs s) (i i₀ : I) :
    (unif L.EncodingRandomness).map (fun r => (L.recOf i r s, fun p : T => L.encodeIndex i r p)) =
      (unif L.EncodingRandomness).map (fun r => (L.recOf i₀ r s, fun p : T => L.encodeIndex i₀ r p)) := by
  have h := congrArg (PMF.map (Prod.map (fun a : L.OutOfDomainAnswer => ((s, a) : L.Rec)) id))
    (hR T hT s hs i i₀)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

section Life
variable {ι : Type}

/-- A call is allowed: the rows that it names have seeds in Gs, and all instances of a batch are in
the relation. -/
def okF (Gs : L.OutOfDomainSeed → Prop) (sd : ι → L.OutOfDomainSeed) (ok : X → Prop) : FCall ι F L.wordLength → Prop
  | .rcd a => Gs (sd a)
  | .test a _ => Gs (sd a)
  | .link a a' _ => Gs (sd a) ∧ Gs (sd a')
  | .bat a _ q h => Gs (sd a) ∧ F.okB ok q h
  | .read a _ => Gs (sd a)

def errF (zT zL zO : ℝ≥0∞) {n : ℕ} : FCall ι F n → ℝ≥0∞
  | .test _ _ => zT
  | .link _ _ _ => zL
  | .bat _ _ q _ => F.wt q * zO
  | _ => 0

/-- the word places that a call may read in row x. The OOD sample costs nothing. -/
def loadF [DecidableEq ι] (qT qpar qch qon : ℕ) {n : ℕ} : FCall ι F n → ι → ℕ
  | .rcd _, _ => 0
  | .test a _, x => if x = a then qT else 0
  | .link a a' _, x => (if x = a then qpar else 0) + if x = a' then qch else 0
  | .bat a _ _ _, x => if x = a then qon else 0
  | .read a _, x => if x = a then 1 else 0

/-- the table: row a holds an encoding of the index idx a, and at its free place the OOD sample of
that encoding at the row's seed -/
def tabS (L : HolographicProtocol I X) (idx : ι → I) (sd : ι → L.OutOfDomainSeed) (r : ι → L.EncodingRandomness) :
    ∀ p, Sy ι (Fin L.wordLength) L.Rec L.Symbol p :=
  Free.tab (fun a => L.recOf (idx a) (r a) (sd a)) fun a => L.encodeIndex (idx a) (r a)

/-- The simulated runs as algorithms that read the table: first the OOD sample(s), at the free
place(s); then the word places. -/
def simRF (L : HolographicProtocol I X) (F : Form X) (Sm : SimsF L F) :
    ∀ c : FCall ι F L.wordLength, Reader (ι × Option (Fin L.wordLength)) (Sy ι (Fin L.wordLength) L.Rec L.Symbol) (FAns L F c)
  | .rcd a => .read (a, none) fun (x : L.Rec) => .done x
  | .test a e => .read (a, none) fun (x : L.Rec) => up ((Sm.T e x).reader fun p => (a, p))
  | .link a a' e => .read (a, none) fun (x : L.Rec) => .read (a', none) fun (x' : L.Rec) =>
      up ((Sm.Lk e (x, x')).reader (Sum.elim (fun p => (a, p)) fun p => (a', p)))
  | .bat a e q _ => .read (a, none) fun (x : L.Rec) => up ((Sm.B e q x).reader fun p => (a, p))
  | .read a p => up (.read (a, p) fun y => .done y)

/-- The simulated runs on encodings of the indices idx a. -/
def simOF (L : HolographicProtocol I X) (F : Form X) (Sm : SimsF L F) (idx : ι → I) (sd : ι → L.OutOfDomainSeed)
    (r : ι → L.EncodingRandomness) : ∀ c : FCall ι F L.wordLength, PMF (FAns L F c)
  | .rcd a => PMF.pure (L.recOf (idx a) (r a) (sd a))
  | .test a e => (Sm.T e (L.recOf (idx a) (r a) (sd a))).law (L.encodeIndex (idx a) (r a))
  | .link a a' e =>
    (Sm.Lk e (L.recOf (idx a) (r a) (sd a), L.recOf (idx a') (r a') (sd a'))).law
      (Sum.elim (L.encodeIndex (idx a) (r a)) (L.encodeIndex (idx a') (r a')))
  | .bat a e q _ => (Sm.B e q (L.recOf (idx a) (r a) (sd a))).law (L.encodeIndex (idx a) (r a))
  | .read a p => PMF.pure (L.encodeIndex (idx a) (r a) p)

theorem run_simRF (Sm : SimsF L F) (idx : ι → I) (sd : ι → L.OutOfDomainSeed) (r : ι → L.EncodingRandomness)
    (c : FCall ι F L.wordLength) :
    (simRF L F Sm c).run (tabS L idx sd r) = simOF L F Sm idx sd r c := by
  cases c with
  | rcd a => rfl
  | test a e =>
    show (up ((Sm.T e (L.recOf (idx a) (r a) (sd a))).reader fun p => (a, p))).run
        (tabS L idx sd r) = _
    rw [run_up]
    exact run_reader _ _ _ (L.encodeIndex (idx a) (r a)) fun _ => rfl
  | link a a' e =>
    show (up ((Sm.Lk e (L.recOf (idx a) (r a) (sd a), L.recOf (idx a') (r a') (sd a'))).reader
            (Sum.elim (fun p => (a, p)) fun p => (a', p)))).run (tabS L idx sd r) = _
    rw [run_up]
    exact run_reader _ _ _ (Sum.elim (L.encodeIndex (idx a) (r a)) (L.encodeIndex (idx a') (r a'))) fun q => by
      cases q <;> rfl
  | bat a e q h =>
    show (up ((Sm.B e q (L.recOf (idx a) (r a) (sd a))).reader fun p => (a, p))).run
        (tabS L idx sd r) = _
    rw [run_up]
    exact run_reader _ _ _ (L.encodeIndex (idx a) (r a)) fun _ => rfl
  | read a p => rfl

/-- On encodings of one index these are the answers of the simulator's laws. -/
theorem simOF_const (Sm : SimsF L F) (j : I) (sd : ι → L.OutOfDomainSeed) (r : ι → L.EncodingRandomness)
    (c : FCall ι F L.wordLength) :
    simOF L F Sm (fun _ => j) sd r c = (simLawsF L F Sm j).O sd r c := by
  cases c <;> rfl

/-- Which index a row holds on the real side of the comparison of tables: i where the row's seed is
in Gs, and i₀ in the rows that no allowed call names. -/
def idxS (Gs : L.OutOfDomainSeed → Prop) (sd : ι → L.OutOfDomainSeed) (i i₀ : I) : ι → I :=
  fun a => if Gs (sd a) then i else i₀

theorem idxS_good {Gs : L.OutOfDomainSeed → Prop} {sd : ι → L.OutOfDomainSeed} (i i₀ : I) {a : ι} (h : Gs (sd a)) :
    idxS Gs sd i i₀ a = i := if_pos h

theorem idxS_bad {Gs : L.OutOfDomainSeed → Prop} {sd : ι → L.OutOfDomainSeed} (i i₀ : I) {a : ι} (h : ¬ Gs (sd a)) :
    idxS Gs sd i i₀ a = i₀ := if_neg h

variable [DecidableEq ι]

theorem adds_simRF {qT qpar qch qon : ℕ} {Sm : SimsF L F} (hC : Sm.Counts qT qpar qch qon)
    (c : FCall ι F L.wordLength) :
    AddsF (simRF L F Sm c) (loadF qT qpar qch qon c) := by
  cases c with
  | rcd e =>
    intro S x a
    show rowCard (wp (insert (e, none) S)) a ≤ rowCard (wp S) a + 0
    rw [wp_insert_free]
    exact le_rfl
  | test e m =>
    exact addsF_free e fun x =>
      addsF_up fun S =>
        within_reader (Sm.T m x) _ S fun ρ a =>
          (rowCard_union_image_le S _ _ a).trans
            (Nat.add_le_add_left (card_filter_const_le _ e a (hC.cntT m x ρ)) _)
  | bat e m q h =>
    exact addsF_free e fun x =>
      addsF_up fun S =>
        within_reader (Sm.B m q x) _ S fun ρ a =>
          (rowCard_union_image_le S _ _ a).trans
            (Nat.add_le_add_left (card_filter_const_le _ e a (hC.cntB m q x ρ)) _)
  | link e e' m =>
    refine addsF_free e fun x =>
        addsF_free e' fun x' =>
          addsF_up fun S => within_reader (Sm.Lk m (x, x')) _ S fun ρ a =>
      (rowCard_union_image_le S _ _ a).trans (Nat.add_le_add_left ?_ _)
    have hsub : (((Sm.Lk m (x, x')).reads ρ).filter fun q =>
          ((Sum.elim (fun p => (e, p)) fun p => (e', p) : Fin L.wordLength ⊕ Fin L.wordLength → ι × Fin L.wordLength) q).1 = a)
        ⊆ ((((Sm.Lk m (x, x')).reads ρ).filter fun p => p.isLeft).filter fun _ => e = a)
          ∪ ((((Sm.Lk m (x, x')).reads ρ).filter fun p => p.isRight).filter fun _ => e' = a) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      cases q with
      | inl p =>
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hq1, rfl⟩, hq2⟩)
      | inr p =>
        exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hq1, rfl⟩, hq2⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (card_filter_const_le _ e a (hC.cntLp m (x, x') ρ))
          (card_filter_const_le _ e' a (hC.cntLc m (x, x') ρ))))
  | read e p =>
    refine addsF_up fun S y a => ?_
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

/-- The law of the table on a set of places with at most b word places in each row is the same for
the real side's indices and for i₀. -/
theorem table_lawF {Gs : L.OutOfDomainSeed → Prop} {b : ℕ}
    (hR : HidE L Gs b) (sd : ι → L.OutOfDomainSeed) (i i₀ : I)
    (S : Finset (ι × Option (Fin L.wordLength))) (hS : ∀ e, rowCard (wp S) e ≤ b) :
    ((unif (ι → L.EncodingRandomness)).map fun r => tabS L (idxS Gs sd i i₀) sd r).map (res S) =
      ((unif (ι → L.EncodingRandomness)).map fun r => tabS L (fun _ => i₀) sd r).map (res S) :=
  rows_lawF (ι := ι) (Q := Fin L.wordLength) (F := L.Rec) (Sg := L.Symbol) (R := L.EncodingRandomness)
    (fun a r => L.recOf (idxS Gs sd i i₀ a) r (sd a)) (fun a r => L.recOf i₀ r (sd a))
    (fun a r => L.encodeIndex (idxS Gs sd i i₀ a) r) (fun _ r => L.encodeIndex i₀ r) b
    (fun a T hT => by
      dsimp only
      by_cases h : Gs (sd a)
      · rw [idxS_good i i₀ h]
        exact row_lawS hR T hT (sd a) h i i₀
      · rw [idxS_bad i i₀ h]) S hS

theorem lifetimeF {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞}
    (hR : HidE L Gs b) {Sm : SimsF L F} (hC : Sm.Counts qT qpar qch qon) {W : LawsF L F} {i : I}
    (hN : W.Near Sm Gs i ok zT zL zO) (i₀ : I) (sd : ι → L.OutOfDomainSeed)
    (t : Play (FCall ι F L.wordLength) (FAns L F) α)
    (hok : t.Calls (okF Gs sd ok)) (hfit : t.Fits (loadF qT qpar qch qon) b fun _ => 0) :
    tv ((unif (ι → L.EncodingRandomness)).bind fun r => t.run (W.O sd r))
        ((unif (ι → L.EncodingRandomness)).bind fun r => t.run ((simLawsF L F Sm i₀).O sd r)) ≤
      t.cost (errF zT zL zO) := by
  have h := lifetimeD (unif (ι → L.EncodingRandomness)) (fun r => tabS L (idxS Gs sd i i₀) sd r)
    ((unif (ι → L.EncodingRandomness)).map fun r => tabS L (fun _ => i₀) sd r) (fun r => W.O sd r) (simRF L F Sm)
    (okF Gs sd ok) (errF zT zL zO) (fun T => ∀ e, rowCard (wp T) e ≤ b) ?_ ?_ t hok ?_
  · rw [PMF.bind_map] at h
    have e1 : ∀ r : ι → L.EncodingRandomness,
        (t.run fun c => (simRF L F Sm c).run (tabS L (fun _ => i₀) sd r)) =
          t.run ((simLawsF L F Sm i₀).O sd r) :=
      fun r => congrArg t.run (funext fun c => by rw [run_simRF, simOF_const])
    simp only [← e1]
    exact h
  · intro r c hc
    rw [run_simRF Sm (idxS Gs sd i i₀) sd r c]
    cases c with
    | rcd a =>
      show tv (PMF.pure (W.rc (r a, sd a)))
        (PMF.pure (L.recOf (idxS Gs sd i i₀ a) (r a) (sd a))) ≤ 0
      rw [hN.rc, idxS_good i i₀ hc, tv_self]
    | test a e =>
      show tv (W.T e (r a, sd a))
        ((Sm.T e (L.recOf (idxS Gs sd i i₀ a) (r a) (sd a))).law
          (L.encodeIndex (idxS Gs sd i i₀ a) (r a))) ≤ zT
      rw [idxS_good i i₀ hc]
      exact hN.T e (r a, sd a) hc
    | link a a' e =>
      show tv (W.Lk e (r a, sd a) (r a', sd a'))
        ((Sm.Lk e (L.recOf (idxS Gs sd i i₀ a) (r a) (sd a),
            L.recOf (idxS Gs sd i i₀ a') (r a') (sd a'))).law
          (Sum.elim (L.encodeIndex (idxS Gs sd i i₀ a) (r a)) (L.encodeIndex (idxS Gs sd i i₀ a') (r a')))) ≤ zL
      rw [idxS_good i i₀ hc.1, idxS_good i i₀ hc.2]
      exact hN.Lk e (r a, sd a) (r a', sd a') hc.1 hc.2
    | bat a e q h =>
      show tv (W.B e (r a, sd a) q h)
        ((Sm.B e q (L.recOf (idxS Gs sd i i₀ a) (r a) (sd a))).law
          (L.encodeIndex (idxS Gs sd i i₀ a) (r a))) ≤ F.wt q * zO
      rw [idxS_good i i₀ hc.1]
      exact hN.B e (r a, sd a) q h hc.1 hc.2
    | read a p =>
      show tv (PMF.pure (W.y (r a, sd a) p))
        (PMF.pure (L.encodeIndex (idxS Gs sd i i₀ a) (r a) p)) ≤ 0
      rw [hN.y, idxS_good i i₀ hc, tv_self]
  · exact fun S hSb => table_lawF hR sd i i₀ S hSb
  · exact within_plugF (adds_simRF hC) t (fun _ => 0) ∅
      (fun e => by rw [wp_empty, rowCard_empty]) hfit

end Life

/-! ## Part 5. An environment within its bounds -/

section Nice
variable {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop}

theorem good_update {g : ℕ → L.OutOfDomainSeed} {c : ℕ} {s : L.OutOfDomainSeed} (hg : ∀ e, e ≤ c → Gs (g e))
    (hs : Gs s) : ∀ e, e ≤ c + 1 → Gs (Function.update g (c + 1) s e) := by
  intro e he
  by_cases h : e = c + 1
  · rw [h, Function.update_self]
    exact hs
  · rw [Function.update_of_ne h]
    exact hg e (by omega)

theorem calls_toPlayF (t : EnvF L F α) :
    ∀ (c : ℕ) (g : ℕ → L.OutOfDomainSeed) (u : UsedR), t.Adm B Gs ok c u → (∀ e, e ≤ c → Gs (g e)) →
      (toPlayF B.nenc t c g).Calls (okF Gs Prod.snd ok) := by
  induction t with
  | stop a => intro c g u _ _; exact trivial
  | draw β d k ih => intro c g u h hg; exact fun y => ih y c g u (h y) hg
  | fresh s k ih =>
    intro c g u h hg
    exact ⟨h.1, fun a => ih a (c + 1) _ u (h.2.2 a) (good_update hg h.1)⟩
  | test e k ih => intro c g u h hg; exact ⟨hg e h.1, fun a => ih a c g _ (h.2.2 a) hg⟩
  | link e k ih =>
    intro c g u h hg
    exact ⟨⟨hg 0 (Nat.zero_le c), hg e h.2.1⟩, fun a => ih a c g _ (h.2.2.2 a) hg⟩
  | session e q hq k ih =>
    intro c g u h hg
    exact ⟨⟨hg e h.1, h.2.2.2.1⟩, fun a => ih a c g _ (h.2.2.2.2 a) hg⟩
  | read e p k ih => intro c g u h hg; exact ⟨hg e h.1, fun y => ih y c g _ (h.2.2 y) hg⟩

/-- What the encoded index j may still be asked for fits beside the load that any of its rows
carries. (Only the row of the seed that was named for j ever carries a load.) -/
def InvF (L : HolographicProtocol I X) (B : BoundsR) (b qT qpar qch qon : ℕ) (u : UsedR)
    (ld : Row L B.nenc → ℕ) : Prop :=
  ∀ j, j ≤ B.nenc → ∀ s : L.OutOfDomainSeed,
    ld (nm B.nenc j, s) + (B.tests j - u.tests j) * qT +
        (if j = 0 then leftR B B.links u.links * qpar else 0) + (B.links j - u.links j) * qch +
        (B.sess j - u.sess j) * qon + (B.reads j - u.reads j) ≤ b

theorem ite_le (p : Prop) [Decidable p] (q : ℕ) : (if p then q else 0) ≤ q := by
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le q

/-- a row is loaded only if its number is the call's -/
theorem row_ne {M j e : ℕ} {s s' : L.OutOfDomainSeed} (hj : j ≤ M) (he : e ≤ M) (h : j ≠ e) :
    ((nm M j, s) : Row L M) ≠ (nm M e, s') :=
  fun hh => h ((nm_inj hj he).1 (congrArg Prod.fst hh))

theorem fits_toPlayF {b qT qpar qch qon : ℕ} (t : EnvF L F α) :
    ∀ (c : ℕ) (g : ℕ → L.OutOfDomainSeed) (u : UsedR) (ld : Row L B.nenc → ℕ), t.Adm B Gs ok c u →
      c ≤ B.nenc → InvF L B b qT qpar qch qon u ld →
        (toPlayF B.nenc t c g).Fits (loadF qT qpar qch qon) b ld := by
  induction t with
  | stop a =>
    intro c g u ld _ _ hI x
    obtain ⟨x1, x2⟩ := x
    have h := hI x1 (Nat.le_of_lt_succ x1.2) x2
    rw [nm_coe] at h
    omega
  | draw β d k ih => intro c g u ld h hc hI; exact fun y => ih y c g u ld (h y) hc hI
  | fresh s k ih =>
    intro c g u ld h hc hI a
    exact ih a (c + 1) _ u _ (h.2.2 a) h.2.1 fun j hj s' => hI j hj s'
  | test e k ih =>
    intro c g u ld h hc hI a
    obtain ⟨he, hs, h3⟩ := h
    refine ih a c g _ _ (h3 a) hc fun j hj s => ?_
    have h := hI j hj s
    show ld (nm B.nenc j, s) + (if (nm B.nenc j, s) = (nm B.nenc e, g e) then qT else 0) +
        (B.tests j - bump u.tests e j) * qT + _ + _ + _ + _ ≤ b
    dsimp only
    by_cases hje : j = e
    · subst hje
      have e1 := sub_step qT hs
      have e2 := ite_le (((nm B.nenc j, s) : Row L B.nenc) = (nm B.nenc j, g j)) qT
      rw [bump_self]
      omega
    · rw [if_neg (row_ne hj (he.trans hc) hje), bump_ne _ hje]
      omega
  | link e k ih =>
    intro c g u ld h hc hI a
    obtain ⟨h1e, he, hs, h3⟩ := h
    refine ih a c g _ _ (h3 a) hc fun j hj s => ?_
    have h := hI j hj s
    have e0 : leftR B B.links u.links * qpar = leftR B B.links (bump u.links e) * qpar + qpar := by
      rw [leftR_step (he.trans hc) hs, Nat.add_mul, Nat.one_mul]
    show ld (nm B.nenc j, s) +
        ((if (nm B.nenc j, s) = (nm B.nenc 0, g 0) then qpar else 0) +
          if (nm B.nenc j, s) = (nm B.nenc e, g e) then qch else 0) +
        _ + (if j = 0 then leftR B B.links (bump u.links e) * qpar else 0) +
        (B.links j - bump u.links e j) * qch + _ + _ ≤ b
    dsimp only
    by_cases hj0 : j = 0
    · subst hj0
      have hne : (0 : ℕ) ≠ e := by omega
      rw [if_neg (row_ne hj (he.trans hc) hne), if_pos rfl, bump_ne _ hne]
      rw [if_pos rfl] at h
      split_ifs <;> omega
    · rw [if_neg (row_ne hj (Nat.zero_le _) hj0), if_neg hj0]
      rw [if_neg hj0] at h
      by_cases hje : j = e
      · subst hje
        have e1 := sub_step qch hs
        rw [bump_self]
        split_ifs <;> omega
      · rw [if_neg (row_ne hj (he.trans hc) hje), bump_ne _ hje]
        omega
  | session e q hq k ih =>
    intro c g u ld h hc hI a
    obtain ⟨he, hs, -, -, h6⟩ := h
    refine ih a c g _ _ (h6 a) hc fun j hj s => ?_
    have h := hI j hj s
    show ld (nm B.nenc j, s) + (if (nm B.nenc j, s) = (nm B.nenc e, g e) then qon else 0) +
        _ + _ + _ + (B.sess j - bump u.sess e j) * qon + _ ≤ b
    dsimp only
    by_cases hje : j = e
    · subst hje
      have e1 := sub_step qon hs
      have e2 := ite_le (((nm B.nenc j, s) : Row L B.nenc) = (nm B.nenc j, g j)) qon
      rw [bump_self]
      omega
    · rw [if_neg (row_ne hj (he.trans hc) hje), bump_ne _ hje]
      omega
  | read e p k ih =>
    intro c g u ld h hc hI y
    obtain ⟨he, hs, h3⟩ := h
    refine ih y c g _ _ (h3 y) hc fun j hj s => ?_
    have h := hI j hj s
    show ld (nm B.nenc j, s) + (if (nm B.nenc j, s) = (nm B.nenc e, g e) then 1 else 0) +
        _ + _ + _ + _ + (B.reads j - bump u.reads e j) ≤ b
    dsimp only
    by_cases hje : j = e
    · subst hje
      have e2 := ite_le (((nm B.nenc j, s) : Row L B.nenc) = (nm B.nenc j, g j)) 1
      rw [bump_self]
      omega
    · rw [if_neg (row_ne hj (he.trans hc) hje), bump_ne _ hje]
      omega

theorem cost_toPlayF {zT zL zO : ℝ≥0∞} (t : EnvF L F α) :
    ∀ (c : ℕ) (g : ℕ → L.OutOfDomainSeed) (u : UsedR), t.Adm B Gs ok c u → c ≤ B.nenc →
      (toPlayF B.nenc t c g).cost (errF zT zL zO) ≤
        (leftR B B.tests u.tests : ℝ≥0∞) * zT + (leftR B B.links u.links : ℝ≥0∞) * zL +
          (leftR B B.sess u.sess : ℝ≥0∞) * (B.shown * zO) := by
  induction t with
  | stop a => intro c g u _ _; exact zero_le _
  | draw β d k ih =>
    intro c g u h hc
    simp only [toPlayF, Play.cost_draw]
    exact iSup_le fun y => ih y c g u (h y) hc
  | fresh s k ih =>
    intro c g u h hc
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun a => ih a (c + 1) _ u (h.2.2 a) h.2.1)).trans
      (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | read e p k ih =>
    intro c g u h hc
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun y => ih y c g _ (h.2.2 y) hc)).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | test e k ih =>
    intro c g u h hc
    obtain ⟨he, hs, h3⟩ := h
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun a => ih a c g _ (h3 a) hc)).trans (le_of_eq ?_)
    show zT + ((leftR B B.tests (bump u.tests e) : ℝ≥0∞) * zT + _ + _) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring
  | link e k ih =>
    intro c g u h hc
    obtain ⟨-, he, hs, h3⟩ := h
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun a => ih a c g _ (h3 a) hc)).trans (le_of_eq ?_)
    show zL + (_ + (leftR B B.links (bump u.links e) : ℝ≥0∞) * zL + _) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring
  | session e q hq k ih =>
    intro c g u h hc
    obtain ⟨he, hs, hJ, -, h6⟩ := h
    simp only [toPlayF, Play.cost_call]
    have h2 : errF zT zL zO
        (.bat (nm B.nenc e, g e) e q hq : FCall (Row L B.nenc) F L.wordLength) ≤ B.shown * zO :=
      mul_le_mul' (Nat.cast_le.2 hJ) le_rfl
    refine (add_le_add h2 (iSup_le fun a => ih a c g _ (h6 a) hc)).trans (le_of_eq ?_)
    show (B.shown : ℝ≥0∞) * zO +
        (_ + _ + (leftR B B.sess (bump u.sess e) : ℝ≥0∞) * (B.shown * zO)) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring

end Nice

/-! ## Part 6. The theorem -/

/-- For given laws of runs. (not all hypotheses are named here: see `Spec.form_laws`) -/
theorem form_laws : Spec.form_laws := by
  intro I X L F Gs ok b qT qpar qch qon zT zL zO hR Sm hC W i hN B hB i₀ α s₀ E h0 hE
  rw [simHostF_eq, viewF_eq _ s₀ E hE, viewF_eq _ s₀ E hE]
  refine (lifetimeF hR hC hN i₀ Prod.snd (wholeF B.nenc s₀ E)
    ⟨h0, fun a => calls_toPlayF (E a) 0 _ _ (hE a) fun _ _ => h0⟩ ?_).trans ?_
  · intro a
    refine fits_toPlayF (E a) 0 _ _ _ (hE a) (Nat.zero_le _) fun j hj s => ?_
    have h := hB j hj
    show 0 + 0 + (B.tests j - 0) * qT + (if j = 0 then leftR B B.links (fun _ => 0) * qpar else 0) +
        (B.links j - 0) * qch + (B.sess j - 0) * qon + (B.reads j - 0) ≤ b
    rw [leftR_zero]
    simp only [Nat.sub_zero]
    omega
  · unfold wholeF
    rw [Play.cost_call]
    refine (add_le_add (le_refl _)
        (iSup_le fun a => cost_toPlayF (E a) 0 _ _ (hE a) (Nat.zero_le _))).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) +
        ((leftR B B.tests (fun _ => 0) : ℝ≥0∞) * zT + (leftR B B.links (fun _ => 0) : ℝ≥0∞) * zL +
          (leftR B B.sess (fun _ => 0) : ℝ≥0∞) * (B.shown * zO)) = _
    rw [zero_add, leftR_zero, leftR_zero, leftR_zero]
    rfl

/-- An environment before the first encoded index: it draws coins, and then names the first seed, or
stops. -/
inductive PreF (L : HolographicProtocol I X) (F : Form X) (α : Type) : Type 1
  | stop (a : α) : PreF L F α
  | first (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α) : PreF L F α
  | draw (β : Type) (d : PMF β) (k : β → PreF L F α) : PreF L F α

def PreF.run (H : HostF L F) : PreF L F α → PMF α
  | .stop a => PMF.pure a
  | .first s₀ E => H.view s₀ E
  | .draw _ d k => d.bind fun y => (k y).run H

def PreF.Adm (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) : PreF L F α → Prop
  | .stop _ => True
  | .first s₀ E => Gs s₀ ∧ ∀ a, (E a).Adm B Gs ok 0 UsedR.zero
  | .draw _ _ k => ∀ y, (k y).Adm B Gs ok

/-- The same bound for an environment that draws coins before it names the first seed. -/
theorem ViewNearF.pre {H : HostF L F} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {B : BoundsR}
    {S : SimulatorF L F} {z : ℝ≥0∞} (h : ViewNearF H Gs ok B S z) (t : PreF L F α)
    (ht : t.Adm B Gs ok) : tv (t.run H) (t.run S.host) ≤ z := by
  induction t with
  | stop a =>
    show tv (PMF.pure a) (PMF.pure a) ≤ z
    rw [tv_self]
    exact zero_le z
  | first s₀ E => exact h α s₀ E ht.1 ht.2
  | draw β d k ih => exact tv_bind_right_le_of_forall d _ _ fun y _ => ih y (ht y)

end Hiop.Seeded

#print axioms Hiop.Seeded.form_laws
#print axioms Hiop.Seeded.ViewNearF.pre
