-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Life.lean: the tools of the lifetime theorem, for any finite set of encodings of one hidden
index (words of this library: lean/GLOSSARY.md). The theorem, with batches and coalitions, is
`lifetime` of Compile/Batch/Life.lean; for the first encoding and its copies:
Compile/Batch/LifeStar.lean.

The lemma on adaptive queries is Prob.Reader.law_eq of Prob/Linear.lean.

The simulators (`SimOf`) read at the verifier's positions, which are a function of instance and
verifier randomness. The abstract form of the theorem ("lifetime_abstract") allows simulators
that choose their positions adaptively.

# The method

Step 1: each session is replaced by its simulator, which still reads the true encodings. Here this
is an induction on the tree of the adversary ("Play.tv_run_le"), with the encoding randomness fixed;
no sequence of hybrid games is needed. Step 2: adversary and simulators together are one algorithm
that reads a table, whose rows are the encodings ("Play.plug"). It reads at most b places in each
row, b the budget of `Play.Fits` ("Play.within_plug"). The rows are independent, so the law of the
table on such a set of places
does not depend on the index ("rows_law"), and the lemma on adaptive queries applies once, to all
rows together.

Notation: `qT`, `qpar`, `qch`, `qon`: natural numbers; in `load qT qpar qch qon c a`: the query
complexity of the session that a call c starts to encoding a (a test; a link, at the parent and at
the child; an online session).
-/

import Prob.Linear
import Iop.InteractiveOracleProof

set_option autoImplicit false

noncomputable section

namespace Compile.Lifetime

open Prob Iop
open scoped ENNReal

/-! ## Part 1. Adversaries that make calls -/

/-- An adversary that makes calls, as a decision tree. It ends with an output (for instance its
whole view), or makes the call c and goes on by the answer, or draws y from a distribution of its
own choice and goes on by y. So each call may depend on all earlier answers and on all its coins.
There is no bound on its running time. -/
inductive Play (C : Type) (A : C → Type) (α : Type) : Type 1
  | done (a : α) : Play C A α
  | call (c : C) (k : A c → Play C A α) : Play C A α
  | draw (β : Type) (d : PMF β) (k : β → Play C A α) : Play C A α

namespace Play

variable {C : Type} {A : C → Type} {α : Type}

/-- The law of the adversary's output if each call c is answered by a fresh draw from O c. -/
def run (O : ∀ c, PMF (A c)) : Play C A α → PMF α
  | done a => PMF.pure a
  | call c k => (O c).bind fun a => (k a).run O
  | draw _ d k => d.bind fun y => (k y).run O

@[simp] theorem run_done (O : ∀ c, PMF (A c)) (a : α) : (done a : Play C A α).run O = PMF.pure a :=
  rfl

@[simp] theorem run_call (O : ∀ c, PMF (A c)) (c : C) (k : A c → Play C A α) :
    (call c k).run O = (O c).bind fun a => (k a).run O := rfl

@[simp] theorem run_draw (O : ∀ c, PMF (A c)) (β : Type) (d : PMF β) (k : β → Play C A α) :
    (draw β d k).run O = d.bind fun y => (k y).run O := rfl

/-- The sum of the costs z c of the calls on the most expensive path, whatever the answers and the
coins are. -/
def cost (z : C → ℝ≥0∞) : Play C A α → ℝ≥0∞
  | done _ => 0
  | call c k => z c + ⨆ a, (k a).cost z
  | draw _ _ k => ⨆ y, (k y).cost z

@[simp] theorem cost_done (z : C → ℝ≥0∞) (a : α) : (done a : Play C A α).cost z = 0 := rfl

@[simp] theorem cost_call (z : C → ℝ≥0∞) (c : C) (k : A c → Play C A α) :
    (call c k).cost z = z c + ⨆ a, (k a).cost z := rfl

@[simp] theorem cost_draw (z : C → ℝ≥0∞) (β : Type) (d : PMF β) (k : β → Play C A α) :
    (draw β d k).cost z = ⨆ y, (k y).cost z := rfl

/-- Every call that the adversary makes is allowed, whatever the answers and the coins are. -/
def Calls (ok : C → Prop) : Play C A α → Prop
  | done _ => True
  | call c k => ok c ∧ ∀ a, (k a).Calls ok
  | draw _ _ k => ∀ y, (k y).Calls ok

/-- Step 1 of the proof. Under `ht`: if the answers to each allowed call c have laws within z c in
two games, then the outputs of the adversary are within the sum of the z c on its most expensive
path. -/
theorem tv_run_le {O O' : ∀ c, PMF (A c)} {ok : C → Prop} {z : C → ℝ≥0∞}
    (h : ∀ c, ok c → tv (O c) (O' c) ≤ z c) (t : Play C A α) (ht : t.Calls ok) :
    tv (t.run O) (t.run O') ≤ t.cost z := by
  induction t with
  | done a => rw [run_done, run_done, tv_self]; exact zero_le _
  | call c k ih =>
    have h1 : ∀ a, tv ((k a).run O) ((k a).run O') ≤ ⨆ a, (k a).cost z := fun a =>
      (ih a (ht.2 a)).trans (le_iSup (fun a => (k a).cost z) a)
    rw [run_call, run_call, cost_call]
    exact (tv_bind_le_of_forall (O c) (O' c) _ _ h1).trans (add_le_add (h c ht.1) le_rfl)
  | draw β d k ih =>
    rw [run_draw, run_draw, cost_draw]
    exact tv_bind_right_le_of_forall d _ _ fun y _ =>
      (ih y (ht y)).trans (le_iSup (fun y => (k y).cost z) y)

/-! ### Calls that are answered by algorithms that read a table -/

variable {P : Type} {X : P → Type}

/-- Adversary and sessions as one algorithm: each call c is answered by a run of the table-reading
algorithm s c. -/
def plug (s : ∀ c, Reader P X (A c)) : Play C A α → Reader P X α
  | done a => .done a
  | call c k => (s c).bind fun a => (k a).plug s
  | draw β d k => .draw β d fun y => (k y).plug s

/-- On a fixed table the one algorithm has the law of the adversary's output. -/
theorem run_plug (s : ∀ c, Reader P X (A c)) (t : Play C A α) (f : ∀ p, X p) :
    (t.plug s).run f = t.run fun c => (s c).run f := by
  induction t with
  | done a => rfl
  | call c k ih => simp only [plug, Reader.run_bind, run_call, ih]
  | draw β d k ih => simp only [plug, Reader.run_draw, run_draw, ih]

end Play

/-- The lifetime theorem in abstract form. A hidden ω, of law ν, determines a table tab ω and the
law real ω c of the answer to each call c. Let s c be an algorithm that reads the table and whose
output is within z c of the true answer, for every ω. Let O' be a random table with the same law as
tab ω on every good set of places, and let adversary and algorithms together read a good set of
places only. Then the adversary's output in the real game is within the sum of the z c of its output
in the game in which the algorithms s c answer from the table O'. -/
theorem lifetime_abstract {C : Type} {A : C → Type} {α P Sg Ω : Type} [DecidableEq P] (ν : PMF Ω)
    (tab : Ω → P → Sg) (O' : PMF (P → Sg)) (real : Ω → ∀ c, PMF (A c))
    (s : ∀ c, Reader P (fun _ => Sg) (A c)) (ok : C → Prop) (z : C → ℝ≥0∞) (good : Finset P → Prop)
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

/-! ## Part 2. Tables with independent rows, and loads -/

section Rows

variable {ι Q : Type} [DecidableEq ι] [DecidableEq Q]

/-- The number of places of the set S that are in row e. -/
def rowCard (S : Finset (ι × Q)) (e : ι) : ℕ := (S.filter fun p => p.1 = e).card

omit [DecidableEq Q] in
theorem rowCard_empty (e : ι) : rowCard (∅ : Finset (ι × Q)) e = 0 := by simp [rowCard]

/-- Reading the places loc q, q ∈ T, adds to row e at most the number of q ∈ T whose place is in row
e. -/
theorem rowCard_union_image_le
    {Qp : Type} (S : Finset (ι × Q)) (T : Finset Qp) (loc : Qp → ι × Q) (e : ι) :
    rowCard (S ∪ T.image loc) e ≤ rowCard S e + (T.filter fun q => (loc q).1 = e).card := by
  unfold rowCard
  rw [Finset.filter_union]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  rw [Finset.filter_image]
  exact Finset.card_image_le

/-- Independent rows. Row e of a table is u e (r e), with independent uniform r e from a nonempty
finite R. If the law of each row on any b places (`h`: T.card ≤ b) is the same for u and for u',
then so is the law of the whole table on any set of places that has at most b places in each row. -/
theorem rows_law {Sg R : Type} [Fintype ι] [Fintype R] [Nonempty R] (u u' : ι → R → Q → Sg) (b : ℕ)
    (h : ∀ e (T : Finset Q), T.card ≤ b →
      (unif R).map (fun r => fun p : T => u e r p) = (unif R).map (fun r => fun p : T => u' e r p))
    (S : Finset (ι × Q)) (hS : ∀ e, rowCard S e ≤ b) :
    ((unif (ι → R)).map fun r => fun p : ι × Q => u p.1 (r p.1) p.2).map (res S)
      = ((unif (ι → R)).map fun r => fun p : ι × Q => u' p.1 (r p.1) p.2).map (res S) := by
  rw [map_res_eq_iff]
  intro v
  have key : ∀ w : ι → R → Q → Sg,
      cyl ((unif (ι → R)).map fun r => fun p : ι × Q => w p.1 (r p.1) p.2) S v =
        ((∏ e, cnt fun ρ : R => ∀ q, (e, q) ∈ S → w e ρ q = v (e, q) : ℕ) : ℝ≥0∞) /
          Fintype.card (ι → R) := by
    intro w
    rw [cyl_eq_pr, pr_map, ← cnt_forall_pi, ← pr_unif_eq]
    congr 1
    ext r
    constructor
    · intro hh e q hq
      exact hh (e, q) hq
    · intro hh p hp
      exact hh p.1 p.2 hp
  rw [key u, key u']
  congr 2
  refine Finset.prod_congr rfl fun e _ => ?_
  obtain ⟨T, hT⟩ : ∃ T : Finset Q, T = (S.filter fun p => p.1 = e).image Prod.snd := ⟨_, rfl⟩
  have hmem : ∀ q, q ∈ T ↔ (e, q) ∈ S := by
    intro q
    rw [hT]
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨hpS, hpe⟩ := Finset.mem_filter.1 hp
      subst hpe
      exact hpS
    · intro hq
      exact Finset.mem_image.2 ⟨(e, q), Finset.mem_filter.2 ⟨hq, rfl⟩, rfl⟩
  have hTb : T.card ≤ b := by
    rw [hT]
    exact Finset.card_image_le.trans (hS e)
  have hc : ∀ w : ι → R → Q → Sg, (cnt fun ρ : R => ∀ q, (e, q) ∈ S → w e ρ q = v (e, q))
      = cnt fun ρ : R => (fun p : T => w e ρ p) = fun p : T => v (e, (p : Q)) := by
    intro w
    refine cnt_congr fun ρ => ⟨fun hh => funext fun p => hh p ((hmem p).1 p.2), fun hh q hq => ?_⟩
    exact congrFun hh ⟨q, (hmem q).2 hq⟩
  have h4 := (map_unif_eq_map_unif_iff _ _).1 (h e T hTb) fun p : T => v (e, (p : Q))
  rw [hc u, hc u']
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos h4

variable {X : ι × Q → Type} {β : Type}

/-- The algorithm reads at most w e new places in row e, whatever answers it receives and whatever
was read before. -/
def Adds (c : Reader (ι × Q) X β) (w : ι → ℕ) : Prop :=
  ∀ S, c.Within (fun T => ∀ e, rowCard T e ≤ rowCard S e + w e) S

variable {C : Type} {A : C → Type} {α : Type}

/-- A call c puts the load w c e on row e. "t.Fits w b ld": if the rows carry the loads ld
already, then at the end no row carries more than b, whatever the answers and the coins are. Every
call counts. -/
def Play.Fits (w : C → ι → ℕ) (b : ℕ) : Play C A α → (ι → ℕ) → Prop
  | .done _, ld => ∀ e, ld e ≤ b
  | .call c k, ld => ∀ a, (k a).Fits w b fun e => ld e + w c e
  | .draw _ _ k, ld => ∀ y, (k y).Fits w b ld

/-- Under `hS`: an adversary within the budget (`Fits`), together with sessions that keep to their
loads, reads at most b places in each row. -/
theorem Play.within_plug {s : ∀ c, Reader (ι × Q) X (A c)} {w : C → ι → ℕ} {b : ℕ}
    (hs : ∀ c, Adds (s c) (w c)) (t : Play C A α) (ld : ι → ℕ) (S : Finset (ι × Q))
    (hS : ∀ e, rowCard S e ≤ ld e) (ht : t.Fits w b ld) :
    (t.plug s).Within (fun T => ∀ e, rowCard T e ≤ b) S := by
  induction t generalizing ld S with
  | done a => exact fun e => (hS e).trans (ht e)
  | call c k ih =>
    exact Reader.within_bind _ _ S
      (Reader.Within.mono
        (fun T hT a => ih a _ T (fun e => (hT e).trans (Nat.add_le_add_right (hS e) _)) (ht a))
        (hs c S))
  | draw β d k ih => exact fun y => ih y ld S hS (ht y)

end Rows

/-! ## Part 3. One session, and its simulator as an algorithm that reads a table -/

section Session

variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type}

/-- What the game returns of one session: the verifier randomness and the output (a disclosed view,
or `none`). -/
abbrev Sess (Q : InteractiveOracleProof Y E) : Type := Rho Q.shape × Option (DView Q)

/-- The type of the simulators of Iop.Honest.HVZK: given the instance, the verifier randomness and
what the external strings hold where the verifier reads them, a law of outputs. -/
abbrev SimOf (Q : InteractiveOracleProof Y E) : Type :=
  Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))

/-- A session: uniform verifier randomness, fresh prover coins, the output at ρ. -/
def sess (H : Honest Q Wt) (w : Wt) (y : Y) : PMF (Sess Q) :=
  (unif (Rho Q.shape)).bind fun ρ => (H.output w y ρ).map fun o => (ρ, o)

/-- A simulated session on the external strings str: uniform verifier randomness, then the
simulator, which is given the instance, the verifier randomness and the answers at the verifier's
positions. -/
def simSess (Q : InteractiveOracleProof Y E) (Sim : SimOf Q) (y : Y) (str : E.Str) : PMF (Sess Q) :=
  (unif (Rho Q.shape)).bind fun ρ => (Sim y ρ (Q.extAns y ρ str)).map fun o => (ρ, o)

/-- A session and its simulated counterpart are within the error of the simulator. -/
theorem tv_sess_le (H : Honest Q Wt) (Sim : SimOf Q) (w : Wt) (y : Y) {z : ℝ≥0∞}
    (h : prRho {ρ | H.output w y ρ ≠ Sim y ρ (Q.extAns y ρ (H.ext w))} ≤ z) :
    tv (sess H w y) (simSess Q Sim y (H.ext w)) ≤ z := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (le_trans (pr_mono _ ?_) h)
  intro ρ hρ hEq
  exact hρ (congrArg (fun d : PMF (Option (DView Q)) => d.map fun o => (ρ, o)) hEq)

variable {P Qp Sg β : Type}

open Classical in
/-- Read the places loc q for the q of a list, one after the other, note the answers, and go on with
the notes. -/
def readK (loc : Qp → P) :
    List Qp → (Qp → Option Sg) →
    ((Qp → Option Sg) → Reader P (fun _ => Sg) β) → Reader P (fun _ => Sg) β
  | [], acc, g => g acc
  | q :: l, acc, g => .read (loc q) fun x => readK loc l (Function.update acc q (some x)) g

open Classical in
theorem run_readK (loc : Qp → P) (f : P → Sg) : ∀ (l : List Qp) (acc : Qp → Option Sg)
    (g : (Qp → Option Sg) → Reader P (fun _ => Sg) β),
    (readK loc l acc g).run f = (g fun q => if q ∈ l then some (f (loc q)) else acc q).run f
  | [], acc, g => by simp [readK]
  | q :: l, acc, g => by
      rw [readK, Reader.run_read, run_readK loc f l]
      congr 2
      funext q'
      by_cases h : q' ∈ l
      · simp [h]
      · by_cases h' : q' = q
        · subst h'
          simp [h]
        · simp [h, h']

theorem within_readK [DecidableEq P] {good : Finset P → Prop} (loc : Qp → P) :
    ∀ (l : List Qp) (acc : Qp → Option Sg)
        (g : (Qp → Option Sg) → Reader P (fun _ => Sg) β) (S : Finset P),
      (∀ acc', (g acc').Within good (S ∪ (l.map loc).toFinset)) → (readK loc l acc g).Within good S
  | [], acc, g, S, h => by simpa [readK] using h acc
  | q :: l, acc, g, S, h => by
      intro x
      refine within_readK loc l _ g _ fun acc' => ?_
      have h1 := h acc'
      rwa [List.map_cons, List.toFinset_cons, Finset.union_insert, ← Finset.insert_union] at h1

/-- The simulated session as an algorithm that reads a table: position q of the external strings is
the place loc q. -/
def sessR (Q : InteractiveOracleProof Y E) (Sim : SimOf Q) (y : Y) (loc : E.Pos → P) :
    Reader P (fun _ => E.Sym) (Sess Q) :=
  .draw (Rho Q.shape) (unif (Rho Q.shape)) fun ρ =>
    readK loc (Q.extReads y ρ).toList (fun _ => none) fun ans =>
      .draw (Option (DView Q)) (Sim y ρ ans) fun o => .done (ρ, o)

open Classical in
theorem run_sessR (Q : InteractiveOracleProof Y E) (Sim : SimOf Q) (y : Y) (loc : E.Pos → P) (f : P → E.Sym)
    (str : E.Str) (h : ∀ q, E.rd str q = f (loc q)) :
    (sessR Q Sim y loc).run f = simSess Q Sim y str := by
  unfold sessR simSess
  rw [Reader.run_draw]
  congr 1
  funext ρ
  rw [run_readK, Reader.run_draw]
  have h1 : (fun q => if q ∈ (Q.extReads y ρ).toList then some (f (loc q)) else none) =
      Q.extAns y ρ str := by
    funext q
    unfold InteractiveOracleProof.extAns
    by_cases hq : q ∈ Q.extReads y ρ <;> simp [hq, h]
  rw [h1]
  rfl

/-- The simulated session reads the places of the verifier's positions and no others. -/
theorem within_sessR [DecidableEq P] (Q : InteractiveOracleProof Y E) (Sim : SimOf Q) (y : Y) (loc : E.Pos → P)
    {good : Finset P → Prop} (S : Finset P) (h : ∀ ρ, good (S ∪ (Q.extReads y ρ).image loc)) :
    (sessR Q Sim y loc).Within good S := by
  intro ρ
  refine within_readK loc _ _ _ S fun acc' o => ?_
  have h1 : ((Q.extReads y ρ).toList.map loc).toFinset = (Q.extReads y ρ).image loc := by
    ext p
    simp
  show good _
  rw [h1]
  exact h ρ

end Session

/-! ## Part 4. Calls and loads -/

section Game

variable {I X : Type}

/-- The calls of the lifetime game. ι is the set of names of the encodings. -/
inductive Call (ι X : Type) : Type
  /-- a session of Test on encoding e -/
  | test (e : ι) : Call ι X
  /-- a session of Link on the encodings e (parent) and e' (child) -/
  | link (e e' : ι) : Call ι X
  /-- a session of the online protocol on encoding e with the instance x -/
  | onl (e : ι) (x : X) : Call ι X

variable {ι : Type}

/-- The query complexity of the session that a call starts to encoding a. -/
def load [DecidableEq ι] (qT qpar qch qon : ℕ) : Call ι X → ι → ℕ
  | .test e, a => if a = e then qT else 0
  | .link e e', a => (if a = e then qpar else 0) + if a = e' then qch else 0
  | .onl e _, a => if a = e then qon else 0

variable [DecidableEq ι]

private theorem card_filter_const_le
    {Qp : Type} (T : Finset Qp) (e a : ι) {q : ℕ} (h : T.card ≤ q) :
    (T.filter fun _ => e = a).card ≤ if a = e then q else 0 := by
  by_cases hae : a = e
  · rw [if_pos hae]
    exact (Finset.card_filter_le _ _).trans h
  · rw [if_neg hae, Finset.filter_false_of_mem fun _ _ hh => hae hh.symm]
    simp

end Game

/-! ## Part 5. Helper lemmas on loads and costs -/

namespace Play

variable {C : Type} {A : C → Type} {α ι : Type}

variable (w : C → ι → ℕ) (b : ℕ)

/-- Loads only grow: an adversary that is within the budget (`Fits`) from the loads ld on starts
from loads within the budget (at most b). (The answering laws O are here only as witnesses that
every call has an answer.) -/
theorem le_of_fits (O : ∀ c, PMF (A c)) (t : Play C A α) (ld : ι → ℕ) (h : t.Fits w b ld) :
    ∀ e, ld e ≤ b := by
  induction t generalizing ld with
  | done a => exact h
  | call c k ih =>
    obtain ⟨a, -⟩ := (O c).support_nonempty
    exact fun e => le_trans (Nat.le_add_right _ _) (ih a _ (h a) e)
  | draw β d k ih =>
    obtain ⟨y, -⟩ := d.support_nonempty
    exact ih y ld (h y)

/-! ### Costs of sums and multiples -/

theorem cost_add_le (z z' : C → ℝ≥0∞) (t : Play C A α) :
    t.cost (fun c => z c + z' c) ≤ t.cost z + t.cost z' := by
  induction t with
  | done a => simp
  | call c k ih =>
    simp only [cost_call]
    have h1 : (⨆ a, (k a).cost fun c => z c + z' c) ≤ (⨆ a, (k a).cost z) + ⨆ a, (k a).cost z' :=
      iSup_le fun a =>
        (ih a).trans
          (add_le_add (le_iSup (fun a => (k a).cost z) a) (le_iSup (fun a => (k a).cost z') a))
    calc z c + z' c + (⨆ a, (k a).cost fun c => z c + z' c)
        ≤ z c + z' c + ((⨆ a, (k a).cost z) + ⨆ a, (k a).cost z') := add_le_add le_rfl h1
      _ = z c + (⨆ a, (k a).cost z) + (z' c + ⨆ a, (k a).cost z') := by ring
  | draw β d k ih =>
    simp only [cost_draw]
    exact iSup_le fun y =>
      (ih y).trans
        (add_le_add (le_iSup (fun y => (k y).cost z) y) (le_iSup (fun y => (k y).cost z') y))

theorem cost_mul_le (z : C → ℝ≥0∞) (x : ℝ≥0∞) (t : Play C A α) :
    t.cost (fun c => z c * x) ≤ t.cost z * x := by
  induction t with
  | done a => simp
  | call c k ih =>
    simp only [cost_call, add_mul]
    exact add_le_add le_rfl
      (iSup_le fun a => (ih a).trans (mul_le_mul' (le_iSup (fun a => (k a).cost z) a) le_rfl))
  | draw β d k ih =>
    simp only [cost_draw]
    exact iSup_le fun y => (ih y).trans (mul_le_mul' (le_iSup (fun y => (k y).cost z) y) le_rfl)

end Play

end Compile.Lifetime
