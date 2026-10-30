-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/OneState.lean: lemmas that say when the verifier's state under
the invariant `Thr` (Honest/Thread/Thr.lean) is determined by the run, and a term for the last
states of the first and the shared chain as a function of the run. The second chain's `Thread` has
a parameter for that function (`ends` in Honest/Thread/Last.lean). All statements are general in
the `Thread`; no sub-protocol and no description is named.

Honest/Thread/ThrUnique.lean proves that the state is unique at one state of the prover's run and
one set of available tables. This file removes both restrictions, under hypotheses that are
definitions of this file.

  1  `OneState`   the statement: one run, one state
  2  `OneStand`, `Thread.opensAvailable`, `DepthsDeclared`, `DepthsAt`   hypotheses on the
     parameters. `depthsAt_of_declared`: the third gives the fourth
  3  `flatMap_congr_mem`, `readsOf_congr`, `Thread.colsTo_congr_at`, `Thread.colsTo_congr`   two
     sets of available tables under the invariant give the same columns
  4  `thr_state_unique_at`, `thr_state_unique'`, `oneState_at`, `oneState_of`   the state is unique
     across two sets of tables; `OneState` from the hypotheses
  5  `EndsAre`, `endsBy`, `endsAre_endsBy`   what the function has to return; a term for it, by
     choice; the term returns it

Why two sets of tables matter. The hypothesis at the second chain's start (`DoorBehindS`,
Honest/Thread/FileD.lean) quantifies over the tables beside the state. A function of the coins, the
input and the challenges can return the state only if the state does not depend on the tables.

Why the depth is a hypothesis. The invariant compares an available table with the `Thread`'s own
by `Table.same`, which compares columns at positions below 2 to the table's `logLength`. `readsOf`
(Honest/Frame.lean) reads columns at positions below 2 to the depth that the round declares. No
clause of `Thr` and no test of `Thread.fits` says that the two depths are equal.

Why there are two hypotheses on the depth. `DepthsDeclared` asks the depth of the parameter `table`
at every list of challenges. Where that parameter is `tableBy`
(Johnson/Desc/ProofFile/Honest/Small/PlayedTo.lean: the table that the library's own run of the
prover's parts sends), it is one default value at every list that is too short for that run to reach
the tree. So `DepthsDeclared` fails there as soon as a round before the border opens a tree that is
not reached at the empty list, with another depth than the default's. The proofs use the depth only
of the table as the invariant reads it (`Thread.tableAt`), at the state of the run at hand.
`DepthsAt` asks just that. The lemmas whose names end in `_at` take it; the older names follow from
them.

Where this comes from. The proof of `thr_state_unique_at` is that of `thr_state_unique`
(Honest/Thread/ThrUnique.lean) with one step replaced by `Thread.colsTo_congr_at`.

Limits.
  * `OneState`, `OneStand`, `DepthsDeclared`, `DepthsAt` and `EndsAre` are definitions, meant as
    hypotheses. It is not proved that any `Thread` meets them.
  * `endsBy` is defined by choice. Nothing computes it.
  * `endsAre_endsBy` holds vacuously where the invariant holds at no run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ThrUnique
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.Sent
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-! ## 1 The statement -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **One run, one state.** At border `n`, the verifier's state under the invariant is determined by
the run's coins, the input and the challenges heard: two states under `ThrS T Said n` at the same
coins, at two states of the prover's run with the same input and the same challenges heard, and at
any two sets of available tables, are equal. A definition, meant as a hypothesis. -/
def OneState (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop) (n : Nat) :
    Prop :=
  ∀ k s m E s' m' E', ThrS T Said n k s m E → ThrS T Said n k s' m' E' →
    m.st.input = m'.st.input → m.st.heard = m'.st.heard → s = s'

/-! ## 2 Three hypotheses on the parameters -/

/-- What is said of the prover's run at border `n` determines the state of that run from the coins,
the input and the challenges heard. A definition, meant as a hypothesis. -/
def OneStand (Said : Nat → Coins Bk → Mid W X → Prop) (n : Nat) : Prop :=
  ∀ k m m', Said n k m → Said n k m' → m.st.input = m'.st.input → m.st.heard = m'.st.heard →
    m = m'

/-- An executable test: every source that a round declared before border `n` opens is available at
that border. -/
def Thread.opensAvailable (T : Thread Bk S Cl V W X Pb) (n : Nat) : Bool :=
  (declsTo T.bs n).all fun d => d.opens.all fun o => decide (o.2 ∈ T.hand n)

/-- Each table that a round declared before border `n` opens has the depth that the round declares.
A definition, meant as a hypothesis on the parameter `table`. -/
def DepthsDeclared (T : Thread Bk S Cl V W X Pb) (n : Nat) : Prop :=
  ∀ d ∈ declsTo T.bs n, ∀ o ∈ d.opens, ∀ k w h, (T.table o.2 k w h).2.logLength = o.1.a

/-- Each table that a round declared before border `n` opens has, as the invariant reads it at this
state of the run, the depth that the round declares. A definition, meant as a hypothesis. -/
def DepthsAt (T : Thread Bk S Cl V W X Pb) (n : Nat) (k : Coins Bk) (m : Mid W X) : Prop :=
  ∀ d ∈ declsTo T.bs n, ∀ o ∈ d.opens, (T.tableAt o.2 k m).2.logLength = o.1.a

/-- `DepthsDeclared` gives `DepthsAt` at every state of the run. -/
theorem depthsAt_of_declared {T : Thread Bk S Cl V W X Pb} {n : Nat} (hd : DepthsDeclared T n)
    (k : Coins Bk) (m : Mid W X) : DepthsAt T n k m :=
  fun d hdm o hom => hd d hdm o hom k m.st.input (m.st.heard.take (T.fixed o.2))

end

/-! ## 3 Two sets of available tables give the same columns -/

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- `readsOf` returns the same list at two functions `tr`, `tr'` from sources to tables that agree,
at every source that a round opens, on the sender's place and on the columns below the declared
depth. -/
theorem readsOf_congr (chain ft : Nat) (st : Nat → Nat → Option (List UInt64))
    {tr tr' : Fmt.TreeSource → Option (Place × Table)} :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
      (∀ d ∈ ds, ∀ o ∈ d.opens, (tr o.2).map (·.1) = (tr' o.2).map (·.1) ∧
        ∀ x, x < 2 ^ o.1.a → (tr o.2).map (·.2.col x) = (tr' o.2).map (·.2.col x)) →
      readsOf chain ft st tr ds Rs = readsOf chain ft st tr' ds Rs
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], _ => by simp [readsOf]
  | d :: ds, R :: Rs, h => by
    simp only [readsOf]
    rw [readsOf_congr chain ft st ds Rs fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]
    congr 1
    congr 1
    refine flatMap_congr_mem fun o ho => List.map_congr_left fun x hx => ?_
    obtain ⟨a, b⟩ := h d List.mem_cons_self o ho
    have hlt : x < 2 ^ o.1.a := by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [a, b x hlt]

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **The columns read before border `n` do not depend on the set of available tables**, among those
that meet the invariant's clause on tables at one state of the run, where every tree opened before
`n` is available there (`ho`) and has the declared depth (`hd`). -/
theorem Thread.colsTo_congr_at {n : Nat} {k : Coins Bk} {m : Mid W X} {E E' : Env}
    (h : T.Hand n k m E) (h' : T.Hand n k m E') (ho : T.opensAvailable n = true)
    (hd : DepthsAt T n k m) : T.colsTo n m E = T.colsTo n m E' := by
  have hst : E.stored = E'.stored :=
    funext fun i => funext fun x => (h.1 i x).trans (h'.1 i x).symm
  have ht : ∀ d ∈ declsTo T.bs n, ∀ o ∈ d.opens,
      (E.tree o.2).map (·.1) = (E'.tree o.2).map (·.1) ∧
        ∀ x, x < 2 ^ o.1.a → (E.tree o.2).map (·.2.col x) = (E'.tree o.2).map (·.2.col x) := by
    intro d hdm o hom
    have hσ : o.2 ∈ T.hand n :=
      of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 ho d hdm) o hom)
    obtain ⟨pt, e, p, -⟩ := T.handAt_elim (h.2 o.2 hσ)
    obtain ⟨pt', e', p', -⟩ := T.handAt_elim (h'.2 o.2 hσ)
    obtain ⟨qt, f, c⟩ := T.col_of_handAt (h.2 o.2 hσ)
    obtain ⟨qt', f', c'⟩ := T.col_of_handAt (h'.2 o.2 hσ)
    obtain rfl : pt = qt := Option.some.inj (e.symm.trans f)
    obtain rfl : pt' = qt' := Option.some.inj (e'.symm.trans f')
    refine ⟨?_, fun x hx => ?_⟩
    · rw [e, e']
      show some pt.1 = some pt'.1
      rw [p, p']
    · have hx' : x < 2 ^ (T.tableAt o.2 k m).2.logLength := by
        rw [hd d hdm o hom]
        exact hx
      rw [e, e']
      show some (pt.2.col x) = some (pt'.2.col x)
      rw [c x hx', c' x hx']
  unfold Thread.colsTo
  rw [hst, readsOf_congr T.chain T.ft E'.stored (declsTo T.bs n) (m.st.heard.drop T.front) ht]

/-- The same from `DepthsDeclared`. -/
theorem Thread.colsTo_congr {n : Nat} {k : Coins Bk} {m : Mid W X} {E E' : Env}
    (h : T.Hand n k m E) (h' : T.Hand n k m E') (ho : T.opensAvailable n = true)
    (hd : DepthsDeclared T n) : T.colsTo n m E = T.colsTo n m E' :=
  T.colsTo_congr_at h h' ho (depthsAt_of_declared hd k m)

/-! ## 4 One state -/

/-- **One state of the run, one state of the verifier, at any two sets of available tables.**
`hfun`: the chain begins at one state. `ho`, `hd`: as in `Thread.colsTo_congr_at`. -/
theorem thr_state_unique_at
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁) {n : Nat}
    (ho : T.opensAvailable n = true) {k : Coins Bk} {s s' : S} {m : Mid W X}
    (hd : DepthsAt T n k m) {E E' : Env} (h : Thr T n k s m E) (h' : Thr T n k s' m E') :
    s = s' := by
  unfold Thr at h h'
  obtain ⟨hH, -, -, -, hM, -, -⟩ := h
  obtain ⟨hH', -, -, -, hM', -, -⟩ := h'
  unfold Thread.Made at hM hM'
  obtain ⟨-, -, -, -, s₀, cols, hb, hc, hf⟩ := hM
  obtain ⟨-, -, -, -, s₁, cols', hb', hc', hf'⟩ := hM'
  have e0 : s₀ = s₁ := hfun _ _ _ _ _ hb hb'
  have ec : cols = cols' := by
    rw [T.colsTo_congr_at hH hH' ho hd, hc'] at hc
    exact (Except.ok.inj hc).symm
  subst e0
  subst ec
  rw [hf] at hf'
  exact (Prod.mk.inj (Except.ok.inj hf')).1

/-- The same from `DepthsDeclared`. -/
theorem thr_state_unique'
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁) {n : Nat}
    (ho : T.opensAvailable n = true) (hd : DepthsDeclared T n) {k : Coins Bk} {s s' : S}
    {m : Mid W X} {E E' : Env} (h : Thr T n k s m E) (h' : Thr T n k s' m E') : s = s' :=
  thr_state_unique_at T hfun ho (depthsAt_of_declared hd k m) h h'

/-- **`OneState`**, where the depths are asked only wherever the invariant holds together with what
is said of the run. -/
theorem oneState_at {Said : Nat → Coins Bk → Mid W X → Prop} {n : Nat} (hS : OneStand Said n)
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁)
    (ho : T.opensAvailable n = true)
    (hd : ∀ k s m E, ThrS T Said n k s m E → DepthsAt T n k m) : OneState T Said n := by
  intro k s m E s' m' E' h h' hi hh
  obtain rfl : m = m' := hS k m m' h.2 h'.2 hi hh
  exact thr_state_unique_at T hfun ho (hd k s m E h) h.1 h'.1

/-- **`OneState` from the three hypotheses** and `hfun`. -/
theorem oneState_of {Said : Nat → Coins Bk → Mid W X → Prop} {n : Nat} (hS : OneStand Said n)
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁)
    (ho : T.opensAvailable n = true) (hd : DepthsDeclared T n) : OneState T Said n :=
  oneState_at T hS hfun ho fun k _ m _ _ => depthsAt_of_declared hd k m

end

/-! ## 5 The two earlier chains' last states as a function of the run -/

section
variable {Bk : ProverCoinCounts} {S₁ Cl₁ V₁ W₁ X₁ Pb₁ S₂ Cl₂ V₂ W₂ X₂ Pb₂ W₃ : Type}
  (T₁ : Thread Bk S₁ Cl₁ V₁ W₁ X₁ Pb₁) (Said₁ : Nat → Coins Bk → Mid W₁ X₁ → Prop) (n₁ : Nat)
  (T₂ : Thread Bk S₂ Cl₂ V₂ W₂ X₂ Pb₂) (Said₂ : Nat → Coins Bk → Mid W₂ X₂ → Prop) (n₂ : Nat)
  (in₁ : W₃ → W₁) (in₂ : W₃ → W₂)

/-- **What the function has to return.** `in₁`, `in₂`: the two earlier chains' inputs, computed from
the second chain's. Wherever the two invariants hold at their borders `n₁` and `n₂`, at these
inputs, `ends` returns the two states, from the coins, the second chain's input and the two chains'
challenges, the first chain's before the shared chain's. A definition, meant as a hypothesis. -/
def EndsAre (ends : Coins Bk → W₃ → List Fmt.Drawn → S₁ × S₂) : Prop :=
  ∀ k w s₁ m₁ E₁ s₂ m₂ E₂, ThrS T₁ Said₁ n₁ k s₁ m₁ E₁ → ThrS T₂ Said₂ n₂ k s₂ m₂ E₂ →
    m₁.st.input = in₁ w → m₂.st.input = in₂ w →
    ends k w (m₁.st.heard ++ m₂.st.heard) = (s₁, s₂)

open Classical in
/-- **A term for the function, by choice.** Where there are two states under the two invariants, at
these coins and inputs and at challenges that make up the given list, it returns such a pair, chosen
by `Classical.choice`; elsewhere a default value. It is not executable: nothing computes it. -/
noncomputable def endsBy [Inhabited S₁] [Inhabited S₂] :
    Coins Bk → W₃ → List Fmt.Drawn → S₁ × S₂ := fun k w h =>
  if hE : ∃ p : S₁ × S₂, ∃ m₁ E₁ m₂ E₂, ThrS T₁ Said₁ n₁ k p.1 m₁ E₁ ∧
      ThrS T₂ Said₂ n₂ k p.2 m₂ E₂ ∧ m₁.st.input = in₁ w ∧ m₂.st.input = in₂ w ∧
      m₁.st.heard ++ m₂.st.heard = h then hE.choose else default

/-- **The term returns what it has to**, where each of the two earlier chains has one state for
each run. The list of challenges splits in one way, because the invariant fixes how many challenges
each chain has heard (`Thread.heard_length`, Honest/Thread/PaysLaw.lean). -/
theorem endsAre_endsBy [Inhabited S₁] [Inhabited S₂] (h₁ : OneState T₁ Said₁ n₁)
    (h₂ : OneState T₂ Said₂ n₂) :
    EndsAre T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ (endsBy T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂) := by
  intro k w s₁ m₁ E₁ s₂ m₂ E₂ u₁ u₂ i₁ i₂
  have hE : ∃ p : S₁ × S₂, ∃ m₁' E₁' m₂' E₂', ThrS T₁ Said₁ n₁ k p.1 m₁' E₁' ∧
      ThrS T₂ Said₂ n₂ k p.2 m₂' E₂' ∧ m₁'.st.input = in₁ w ∧ m₂'.st.input = in₂ w ∧
      m₁'.st.heard ++ m₂'.st.heard = m₁.st.heard ++ m₂.st.heard :=
    ⟨(s₁, s₂), m₁, E₁, m₂, E₂, u₁, u₂, i₁, i₂, rfl⟩
  unfold endsBy
  rw [dif_pos hE]
  obtain ⟨m₁', E₁', m₂', E₂', v₁, v₂, j₁, j₂, hh⟩ := hE.choose_spec
  have hl : m₁'.st.heard.length = m₁.st.heard.length := by
    rw [T₁.heard_length v₁.1.2.1, T₁.heard_length u₁.1.2.1]
  obtain ⟨a, b⟩ := List.append_inj hh hl
  exact Prod.ext (h₁ k _ _ _ _ _ _ v₁ u₁ (j₁.trans i₁.symm) a)
    (h₂ k _ _ _ _ _ _ v₂ u₂ (j₂.trans i₂.symm) b)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.flatMap_congr_mem
#print axioms ProofFile.Honest.readsOf_congr
#print axioms ProofFile.Honest.depthsAt_of_declared
#print axioms ProofFile.Honest.Thread.colsTo_congr_at
#print axioms ProofFile.Honest.Thread.colsTo_congr
#print axioms ProofFile.Honest.thr_state_unique_at
#print axioms ProofFile.Honest.thr_state_unique'
#print axioms ProofFile.Honest.oneState_at
#print axioms ProofFile.Honest.oneState_of
#print axioms ProofFile.Honest.endsAre_endsBy
