-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedAdds.lean: the steps by which the shipped Lean verifier adds the claims of a
sub-proof, and the list of forms that they add up to.

A sub-proof adds a claim in one of two ways: by Fork.lin (a form), or by t2Lin
(OnBytes/Model/Trees.lean: a form and runs of entries, under one weight). Between two claims it
takes other steps: it fills slots, and behind the last claim it sets the virtual rows' weights.

Main names.
  runEnts, Run2.ents, claimForm a runs: a run written out as entries, and a claim of the second
    kind as one form. claimForm_value: its value is the form's plus the runs'.
  Keeps F G: G has the weights L of F, its coefficients LS, its constant, its count of claims, its
    theta and its number of slots. keeps_total: the gathered total is the same. hide_keeps,
    modifyRow_keeps: filling a slot keeps; so does a change of a virtual row that leaves L and L0.
  Adds F l G: G comes from F by steps of the three kinds, and l lists the forms that were added.
  adds_total: then the gathered total has grown by the weighted sum of the values of l.
  adds_sum: from a state with the total 0 and no claim, the total is that weighted sum.
  Walk F H l, HWalk H l: the walk's share as one statement. HWalk IS A HYPOTHESIS on a run: it is
    proved here for no routine. walk_sum: it gives the premise of settle_batch.
  settle_batch, settle_batch_iff: let the total at the state H be the weighted sum of the values of
    l in the world of the committed entries, and let Fork.settle return at H. Then the left side of
    the equation that goes to the chain is the gap of the one form of the claims l, read at H.

What this file does not claim. That the run of a sub-proof is such a walk (Adds) is not stated:
each step's law is here, the walk through a whole routine is not. That the routine which sets the
virtual rows' weights keeps (Keeps) is proved for each of its steps, not for its loops.


-/
import OnBytes.Model.TreesLaws
import OnBytes.Tie.Pv.Led.LedKeep
import OnBytes.Tie.Pv.Led.LedWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

/-! ## A claim with runs as one form -/

/-- The entries number i, .., i + count - 1 of a run, each with its coefficient. -/
def runEnts (r : Model.Run2) : (count i : Nat) → List Model.Ent
  | 0, _ => []
  | count + 1, i =>
    { tree := r.tree, row := r.row, idx := r.first + i,
      coef := mulE r.coef (r.w.getD (r.w0 + i) zeroE) } :: runEnts r count (i + 1)

/-- A run, written out as entries. -/
def Run2.ents (r : Model.Run2) : List Model.Ent := runEnts r r.n 0

/-- A claim of a form and runs, as one form. -/
def claimForm (a : Model.Aff) (runs : Array Model.Run2) : Model.Aff :=
  { a with ents := a.ents ++ (runs.toList.flatMap Run2.ents).toArray }

variable {K : Type} [Field K] (ρ : Model.Reading K) (W : Model.World K)

theorem runEnts_value (r : Model.Run2) : ∀ count i : Nat,
    ((runEnts r count i).map (Model.Ent.value ρ W)).sum =
      ρ.val r.coef * Model.runSum
        (fun i => ρ.val (r.w.getD (r.w0 + i) zeroE) * W.entry r.tree r.row (r.first + i)) count i
  | 0, _ => by simp [runEnts, Model.runSum]
  | count + 1, i => by
    simp only [runEnts, List.map_cons, List.sum_cons, Model.runSum, runEnts_value r count (i + 1),
      Model.Ent.value, ρ.mul]
    ring

theorem flatMap_value : ∀ runs : List Model.Run2,
    ((runs.flatMap Run2.ents).map (Model.Ent.value ρ W)).sum =
      (runs.map (Model.Run2.value ρ W)).sum
  | [] => rfl
  | r :: runs => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      flatMap_value runs, Run2.ents, runEnts_value, Model.Run2.value]

/-- The one form of a claim with runs is worth the form plus the runs. -/
theorem claimForm_value (a : Model.Aff) (runs : Array Model.Run2) :
    (claimForm a runs).value ρ W =
      a.value ρ W + (runs.toList.map (Model.Run2.value ρ W)).sum := by
  simp only [claimForm, Model.Aff.value, Array.toList_append, List.map_append, List.sum_append,
    flatMap_value]
  ring

/-! ## Steps that add nothing -/

/-- G has what the gathered equation of F holds, its count of claims, its theta and its number of
slots. -/
structure Keeps (F G : Model.Fork) : Prop where
  /-- the weights L and their first columns -/
  keys : G.trees.map treeKey = F.trees.map treeKey
  /-- the coefficients of the slots -/
  LS : G.LS = F.LS
  /-- the constant -/
  c0 : G.c0 = F.c0
  /-- the count of claims -/
  nClaim : G.nClaim = F.nClaim
  /-- the batching element -/
  theta : G.theta = F.theta
  /-- the number of slots -/
  ns : G.ns = F.ns

theorem keeps_total {F G : Model.Fork} (k : Keeps F G) : G.total ρ W = F.total ρ W := by
  simp only [Model.Fork.total, treesValue_keys ρ W _ _ k.keys, k.LS, k.c0]

theorem hide_keeps {F G : Model.Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) :
    Keeps F G := by
  obtain ⟨rfl, _⟩ := hide_spec h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem modifyRow_keeps (F : Model.Fork) (t r : Nat) (f : Model.HRow → Model.HRow)
    (hf : ∀ R, (f R).L = R.L ∧ (f R).L0 = R.L0) :
    Keeps F { F with trees := F.trees.modify t fun X => { X with rows := X.rows.modify r f } } := by
  have hk : ∀ R, rowKey (f R) = rowKey R := fun R => by
    simp only [rowKey, (hf R).1, (hf R).2]
  have ht : ∀ X : Model.HTree, treeKey { X with rows := X.rows.modify r f } = treeKey X :=
    fun X => Model.map_modify_same rowKey f hk X.rows r
  exact ⟨Model.map_modify_same treeKey _ ht F.trees t, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The walk -/

/-- G comes from F by adding the forms of l, in order, with steps between that add nothing. -/
inductive Adds : Model.Fork → List Model.Aff → Model.Fork → Prop
  /-- no step -/
  | nil (F : Model.Fork) : Adds F [] F
  /-- a step that adds nothing -/
  | keep {F G G' : Model.Fork} {l : List Model.Aff} : Adds F l G → Keeps G G' → Adds F l G'
  /-- a claim by Fork.lin -/
  | lin {F G G' : Model.Fork} {l : List Model.Aff} {f : Model.Aff} :
    Adds F l G → G.lin f = some G' → Adds F (l ++ [f]) G'
  /-- a claim of a form and runs: the three steps of t2Lin -/
  | runs {F G F1 F2 G' : Model.Fork} {l : List Model.Aff} {k : E} {a : Model.Aff}
    {rs : Array Model.Run2} : Adds F l G → G.kap = some (k, F1) → F1.push k a = some F2 →
    F2.pushRuns k rs = some G' → Adds F (l ++ [claimForm a rs]) G'

theorem sumFrom_snoc {α : Type} (g : Nat → α → K) (x : α) : ∀ (l : List α) (s : Nat),
    Model.sumFrom g s (l ++ [x]) = Model.sumFrom g s l + g (s + l.length) x
  | [], s => by simp [Model.sumFrom]
  | y :: l, s => by
    simp only [List.cons_append, Model.sumFrom, sumFrom_snoc g x l (s + 1), List.length_cons]
    rw [show s + 1 + l.length = s + (l.length + 1) by omega]
    ring

/-- The gathered total grows by the weighted sum of the values of the forms that were added. -/
theorem adds_total {F G : Model.Fork} {l : List Model.Aff} (A : Adds F l G)
    (hs : F.LS.size = F.ns) :
    G.total ρ W = F.total ρ W + Model.claimsValue ρ W (ρ.val F.theta) F.nClaim l ∧
      G.nClaim = F.nClaim + l.length ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns := by
  induction A with
  | nil => simp [Model.claimsValue, Model.sumFrom, hs]
  | keep _ k ih =>
    obtain ⟨t, n, th, ns, sz⟩ := ih
    exact ⟨by rw [keeps_total ρ W k, t], by rw [k.nClaim, n], by rw [k.theta, th],
      by rw [k.ns, ns], by rw [k.LS, k.ns, sz]⟩
  | lin _ h ih =>
    obtain ⟨t, n, th, ns, sz⟩ := ih
    obtain ⟨t2, n2, th2, ns2, sz2, _⟩ := Model.Fork.lin_total ρ W _ _ _ sz h
    refine ⟨?_, ?_, by rw [th2, th], by rw [ns2, ns], sz2⟩
    · rw [t2, t, th, n]
      simp only [Model.claimsValue, sumFrom_snoc]
      ring
    · rw [n2, n, List.length_append, List.length_singleton]
      omega
  | runs _ h1 h2 h3 ih =>
    obtain ⟨t, n, th, ns, sz⟩ := ih
    obtain ⟨t2, n2, th2, ns2, sz2, _⟩ := Model.Fork.claim_total ρ W _ _ _ _ _ _ _ sz h1 h2 h3
    refine ⟨?_, ?_, by rw [th2, th], by rw [ns2, ns], sz2⟩
    · rw [t2, t, th, n]
      simp only [Model.claimsValue, sumFrom_snoc, claimForm_value]
      ring
    · rw [n2, n, List.length_append, List.length_singleton]
      omega

/-- From a state with the total 0 and no claim, the total is the weighted sum of the values. -/
theorem adds_sum {F H : Model.Fork} {l : List Model.Aff} (A : Adds F l H)
    (hs : F.LS.size = F.ns) (h0 : F.nClaim = 0) (ht : F.total ρ W = 0) :
    H.total ρ W = Model.claimsValue ρ W (ρ.val H.theta) 0 l := by
  obtain ⟨t, _, th, _, _⟩ := adds_total ρ W A hs
  rw [t, ht, zero_add, th, h0]

/-- The walk's share, as one statement: the state H at which the one equation is written comes, by
steps of the three kinds, from a state F that has gathered nothing, and l lists the forms that were
added. Whoever says of a form (the row of a sumcheck, a tie of an end value) that the verifier
claims it says that it is a member of l. -/
structure Walk (F H : Model.Fork) (l : List Model.Aff) : Prop where
  /-- the steps -/
  adds : Adds F l H
  /-- one coefficient for each slot -/
  sized : F.LS.size = F.ns
  /-- no claim yet -/
  fresh : F.nClaim = 0
  /-- nothing gathered yet -/
  zero : ∀ W : Model.World K, F.total ρ W = 0

/-- The hypothesis on a run: there is such a walk to H. -/
def HWalk (H : Model.Fork) (l : List Model.Aff) : Prop := ∃ F, Walk ρ F H l

theorem walk_sum {H : Model.Fork} {l : List Model.Aff} (h : HWalk ρ H l) :
    H.total ρ W = Model.claimsValue ρ W (ρ.val H.theta) 0 l := by
  obtain ⟨F, w⟩ := h
  exact adds_sum ρ W w.adds w.sized w.fresh (w.zero W)

/-! ## The one equation, from the total -/

variable {J : Type} [Fintype J] (Y : Lay J)

/-- The one equation. Let the total at H be the weighted sum of the values of l in the world of the
committed entries, and let Fork.settle return the coefficients mc on the mask row and the constant
c. Then the left side of the equation that goes to the chain is the gap of the one form of the
claims l, read at H. -/
theorem settle_batch (H : Model.Fork) (l : List Model.Aff) (used : Nat) (mc : Array E) (c : E)
    (m : J → K)
    (hsum : H.total ρ (portWorld ρ Y H m) =
      Model.claimsValue ρ (portWorld ρ Y H m) (ρ.val H.theta) 0 l)
    (hset : H.settle used = some (mc, c)) :
    Model.treesValue ρ (portWorld ρ Y H m) H.trees + Model.maskValue ρ (Y.maskAt m) mc + ρ.val c =
      (batchAt (ρ.val H.theta) ((List.range' 0 l.length).zip (claimsOf ρ Y H l))).gap m := by
  have e := Model.Fork.settle_whole ρ H used mc c (Y.maskAt m)
    (fun t r idx => Y.entryAt m t (rowWeight ρ H.trees t r) idx) hset
  rw [batch_claimsValue, ← hsum]
  exact e

/-- The equation that goes to the chain holds if and only if the one form of the claims holds of
the committed entries at theta. -/
theorem settle_batch_iff (H : Model.Fork) (l : List Model.Aff) (used : Nat) (mc : Array E) (c : E)
    (m : J → K)
    (hsum : H.total ρ (portWorld ρ Y H m) =
      Model.claimsValue ρ (portWorld ρ Y H m) (ρ.val H.theta) 0 l)
    (hset : H.settle used = some (mc, c)) :
    Model.treesValue ρ (portWorld ρ Y H m) H.trees + Model.maskValue ρ (Y.maskAt m) mc +
        ρ.val c = 0 ↔
      (batchAt (ρ.val H.theta) ((List.range' 0 l.length).zip (claimsOf ρ Y H l))).Holds m := by
  rw [settle_batch ρ Y H l used mc c m hsum hset]
  exact Iff.rfl

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.claimForm_value
#print axioms OnBytes.Road.Rows.adds_total
#print axioms OnBytes.Road.Rows.adds_sum
#print axioms OnBytes.Road.Rows.settle_batch_iff
