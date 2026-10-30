-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadWalk.lean: the states in which the claims of the output head's sub-proof are added.

The theorems on the claims of the output head's sub-proof (Johnson/Road/HeadLedger.lean,
HeadJoin.lean, HeadSteps.lean [not in this library], HeadPolicyForms.lean) each begin: "if the
routine succeeds from a state F with one coefficient for each slot", and they read the tables of the
reads with the number of columns that F gives to the array of the reads. The verifier runs these
routines one after the other (walk in OnBytes/Model/Head.lean). This file shows that each routine is
run from a state of that kind, and that the number of columns is one number for all.

Main definitions: Kept (a later state has one coefficient for each slot and the same numbers of
columns); Keeps (a routine that succeeds leaves such a state), Leaves (it leaves state and context),
Adds (it leaves the context and adds a list of claims); OkL (a routine of a link succeeds); Noted.
Main theorems: the rules keeps_..., leaves_..., adds_... (how the three pass through the monad and
its loops); ok_change, hide_same, keeps_hideRun; leaves_LINE, leaves_keyForm; adds_claimSquares,
adds_claimStream, adds_claimPolicy, adds_claimLogits; ok_claimJoin; objects_list; keeps_objects,
keeps_claimLedger, keeps_claimJoin, keeps_pscRow, keeps_claimPlanes; okL_pure, okL_bind, okL_lift;
walk_parts (the routines of the walk, each with its states and contexts, in the verifier's order);
walk_states (six routines start from a state that is kept, and what each does to the state).

What is not claimed. The routine that adds the claims of the smallness test (objectsF in
OnBytes/Model/Tail.lean) is not treated here: that it keeps the state is a hypothesis of
walk_states, which is used for the one of the six routines that runs after it
(Johnson/Road/HeadTailKeeps.lean shows it). Nothing is said about the value of a claim, about the
state in which the walk begins, or about what a verifier's acceptance shows. Every theorem begins
"if the routine succeeds": none says that it does. The program does not import this file.
-/
import Johnson.Road.HeadJoin
import Johnson.Road.HeadLedger

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd.Walk

open OnBytes.Model (Reading World Aff Fork SubM)

/-! ## What is kept -/

/-- The state G has one coefficient for each slot, and every array has as many columns in G as in
F. -/
def Kept (F G : Fork) : Prop := G.LS.size = G.ns ∧ ∀ t, colsOf G t = colsOf F t

/-- A state with one coefficient for each slot is kept from itself. -/
theorem Kept.refl {F : Fork} (hs : F.LS.size = F.ns) : Kept F F := ⟨hs, fun _ => rfl⟩

/-- If G is kept from F and H is kept from G, then H is kept from F. -/
theorem Kept.trans {F G H : Fork} (a : Kept F G) (b : Kept G H) : Kept F H :=
  ⟨b.1, fun t => (b.2 t).trans (a.2 t)⟩

/-- From a state with one coefficient for each slot, the routine m, if it succeeds, leaves a state
that is kept. -/
def Keeps {α : Type} (m : SubM α) : Prop :=
  ∀ F C a G D, F.LS.size = F.ns → Ok m F C a G D → Kept F G

/-- A routine that leaves the state. -/
theorem keeps_of_leaves {α : Type} {m : SubM α} (h : ∀ F C a G D, Ok m F C a G D → G = F) :
    Keeps m := by
  intro F C a G D hs hk
  rw [h F C a G D hk]
  exact Kept.refl hs

/-- A routine that only returns a value keeps the state's shape. -/
theorem keeps_pure {α : Type} (a : α) : Keeps (pure a : SubM α) :=
  keeps_of_leaves fun F C b G D h => ((ok_pure a b F G C D).mp h).2.1

/-- One routine after another keeps the state's shape, if each of the two does. -/
theorem keeps_bind {α β : Type} {m : SubM α} {f : α → SubM β} (hm : Keeps m)
    (hf : ∀ a, Keeps (f a)) : Keeps (m >>= f) := by
  intro F C b G D hs h
  rw [ok_bind] at h
  obtain ⟨a, F1, C1, h1, h2⟩ := h
  have k1 := hm F C a F1 C1 hs h1
  exact k1.trans (hf a F1 C1 b G D k1.1 h2)

/-- A block that is run inside a routine does not see the state, so it keeps its shape. -/
theorem keeps_lift {α : Type} (x : Blk α) : Keeps (liftM x : SubM α) :=
  keeps_of_leaves fun F C a G D h => ((ok_lift x F G C D a).mp h).2

/-- A block that is lifted into a routine by StateT.lift keeps the state's shape. -/
theorem keeps_slift {α : Type} (x : Blk α) : Keeps (StateT.lift x : SubM α) := keeps_lift x

/-- Adding a claim keeps the state's shape. -/
theorem keeps_lin (f : Aff) : Keeps (SubM.lin f) := by
  intro F C a G D hs h
  rw [ok_lin] at h
  exact lin_cols hs h.1

/-- Marking an owed claim as added changes the list of owed claims alone, so it keeps the state's
shape. -/
theorem keeps_paid (i : ℕ) : Keeps (SubM.paid i) := by
  intro F C a G D hs h
  rw [ok_paid] at h
  rw [h.1]
  exact ⟨hs, fun _ => rfl⟩

/-- A step on the state that may refuse, as a routine. -/
theorem ok_change (f : Fork → Option Fork) (F G : Fork) (C D : Ctx) (u : Unit) :
    Ok (SubM.change f) F C u G D ↔ f F = some G ∧ D = C := by
  unfold Ok
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

/-- Putting a hidden value under a slot changes no coefficient, no number of slots and no array. -/
theorem hide_same {F G : Fork} {j : ℕ} {s k : E} (h : F.hide j s k = some G) :
    G.LS = F.LS ∧ G.ns = F.ns ∧ G.trees = F.trees := by
  unfold Fork.hide at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- The same for a run of hidden values. -/
theorem hideSteps_same (k : E) : ∀ (l : List E) (p q : ℕ × Fork),
    l.foldlM (Fork.hideStep k) p = some q →
      q.2.LS = p.2.LS ∧ q.2.ns = p.2.ns ∧ q.2.trees = p.2.trees
  | [], p, q, h => by
    have e : p = q := by simpa using h
    rw [e]
    exact ⟨rfl, rfl, rfl⟩
  | y :: l, p, q, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep k p y with
    | none => simp [hq] at h
    | some p1 =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep k) p1 = some q := by simpa using h
      obtain ⟨a1, a2, a3⟩ := hideSteps_same k l p1 q h2
      obtain ⟨j, G⟩ := p
      have h3 : (G.hide j y k).map (fun H => (j + 1, H)) = some p1 := hq
      cases hh : G.hide j y k with
      | none => simp [hh] at h3
      | some H =>
        rw [hh] at h3
        have e : (j + 1, H) = p1 := by simpa using h3
        obtain ⟨b1, b2, b3⟩ := hide_same hh
        rw [← e] at a1 a2 a3
        exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

/-- The routine that puts a run of hidden values under slots keeps the state's shape. -/
theorem keeps_hideRun (first : ℕ) (v : Array E) (k : E) :
    Keeps (SubM.change fun F => F.hideRun first v k) := by
  intro F C a G D hs h
  rw [ok_change] at h
  have h1 : F.hideRun first v k = some G := h.1
  unfold Fork.hideRun at h1
  rw [← Array.foldlM_toList] at h1
  cases hq : v.toList.foldlM (Fork.hideStep k) (first, F) with
  | none => simp [hq] at h1
  | some x =>
    rw [hq] at h1
    have e : x.2 = G := by simpa using h1
    obtain ⟨a1, a2, a3⟩ := hideSteps_same k v.toList (first, F) x hq
    rw [e] at a1 a2 a3
    refine ⟨by rw [a1, a2]; exact hs, fun t => ?_⟩
    unfold colsOf
    rw [a3]

/-! ## Loops -/

/-- A fold over a list keeps the state's shape, if every step does. -/
theorem keeps_foldlM {α β : Type} (l : List α) (b : β) {f : β → α → SubM β}
    (hf : ∀ c x, Keeps (f c x)) : Keeps (l.foldlM f b) := by
  induction l generalizing b with
  | nil =>
    rw [List.foldlM_nil]
    exact keeps_pure b
  | cons x l ih =>
    rw [List.foldlM_cons]
    exact keeps_bind (hf b x) fun c => ih c

/-- Adding the claims of an array, one after the other, keeps the state's shape. -/
theorem keeps_forM (l : Array Aff) : Keeps (l.forM SubM.lin) := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact keeps_foldlM l.toList _ fun _ x => keeps_lin x

/-! ## Routines that only read -/

/-- The routine m, if it succeeds, leaves the state and the context. -/
def Leaves {α : Type} (m : SubM α) : Prop := ∀ F C a G D, Ok m F C a G D → G = F ∧ D = C

/-- A routine that leaves state and context keeps the state's shape. -/
theorem Leaves.keeps {α : Type} {m : SubM α} (h : Leaves m) : Keeps m :=
  keeps_of_leaves fun F C a G D hk => (h F C a G D hk).1

/-- A routine that only returns a value leaves state and context. -/
theorem leaves_pure {α : Type} (a : α) : Leaves (pure a : SubM α) :=
  fun F C b G D h => ((ok_pure a b F G C D).mp h).2

/-- One routine after another leaves state and context, if each of the two does. -/
theorem leaves_bind {α β : Type} {m : SubM α} {f : α → SubM β} (hm : Leaves m)
    (hf : ∀ a, Leaves (f a)) : Leaves (m >>= f) := by
  intro F C b G D h
  rw [ok_bind] at h
  obtain ⟨a, F1, C1, h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := hm F C a F1 C1 h1
  obtain ⟨e3, e4⟩ := hf a F1 C1 b G D h2
  exact ⟨e3.trans e1, e4.trans e2⟩

/-- A choice between two routines that leave state and context leaves them. -/
theorem leaves_ite {α : Type} {c : Prop} [Decidable c] {a b : SubM α} (ha : Leaves a)
    (hb : Leaves b) : Leaves (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A public condition under a name leaves state and context. -/
theorem leaves_mustAs (n : String) (b : Bool) : Leaves (liftM (Model.mustAs n b) : SubM Unit) := by
  intro F C a G D h
  rw [ok_lift, mustAs_ok] at h
  exact ⟨h.2, h.1.2⟩

/-- Unwrapping an optional value under a name leaves state and context. -/
theorem leaves_getAs {α : Type} (n : String) (x : Option α) :
    Leaves (liftM (Model.Head.getAs n x) : SubM α) := by
  intro F C a G D h
  rw [ok_lift, getAs_ok] at h
  exact ⟨h.2, h.1.2⟩

/-- Unwrapping the result of a function that may refuse leaves state and context. -/
theorem leaves_held {α : Type} (x : Except String α) :
    Leaves (liftM (Model.Head.held x) : SubM α) := by
  intro F C a G D h
  rw [ok_lift, held_ok] at h
  exact ⟨h.2, h.1.2⟩

/-- A routine that refuses does not succeed, so what Leaves asks holds of it. -/
theorem leaves_refuse {α : Type} (n : String) :
    Leaves (liftM (Model.refuse n : Blk α) : SubM α) := by
  intro F C a G D h
  rw [ok_lift] at h
  have h1 : (Except.error { name := n } : Except Failure (α × Ctx)) = .ok (a, D) := h.1
  cases h1

/-- A loop over a list leaves state and context, if every step does. -/
theorem leaves_forIn_list {α β : Type} (l : List α) (b : β) {f : α → β → SubM (ForInStep β)}
    (hf : ∀ x c, Leaves (f x c)) : Leaves (forIn l b f) := by
  induction l generalizing b with
  | nil =>
    rw [List.forIn_nil]
    exact leaves_pure b
  | cons x l ih =>
    rw [List.forIn_cons]
    refine leaves_bind (hf x b) fun r => ?_
    cases r with
    | done c => exact leaves_pure c
    | yield c => exact ih c

/-- A loop over the numbers below n leaves state and context, if every step does. -/
theorem leaves_forIn_range {β : Type} (n : ℕ) (b : β) {f : ℕ → β → SubM (ForInStep β)}
    (hf : ∀ x c, Leaves (f x c)) : Leaves (forIn [:n] b f) := by
  have e : forIn [:n] b f = forIn (List.range' 0 n) b f := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range', range_list]
  rw [e]
  exact leaves_forIn_list _ b hf

/-- A world in which every hidden value and every entry is 0: for the theorems on readers that speak
of a world, where only what they say of state and context is wanted. -/
def world0 : World Cb.Gl.E := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- The routine that finds where a table begins leaves state and context. -/
theorem leaves_tabAt (R : Model.Head.Run) (n : String) : Leaves (Model.Head.tabAt R n) :=
  fun _ _ _ _ _ h => ⟨(ok_tabAt h).1, (ok_tabAt h).2.1⟩

/-- The routine that returns an entry of a table as a form leaves state and context. -/
theorem leaves_U3at (R : Model.Head.Run) (t i : ℕ) : Leaves (Model.Head.U3at R t i) :=
  fun _ _ _ _ _ h => ⟨(ok_U3at h).1, (ok_U3at h).2.1⟩

/-- The routine that returns the weights of a segment's entries leaves state and context. -/
theorem leaves_ewOf (R : Model.Head.Run) (sn : String) : Leaves (Model.Head.ewOf R sn) :=
  fun _ _ _ _ _ h => ⟨(ok_ewOf h).1, (ok_ewOf h).2.1⟩

/-- The routine that returns the weights of a segment's blocks leaves state and context. -/
theorem leaves_ewh (R : Model.Head.Run) (sn : String) : Leaves (Model.Head.ewh R sn) :=
  fun _ _ _ _ _ h => ⟨(ok_ewh h).1, (ok_ewh h).2.1⟩

/-- The routine that reads limbs of a segment's cells under the segment's weights leaves state and
context. -/
theorem leaves_Sl (R : Model.Head.Run) (sn : String) (a b c : ℕ) :
    Leaves (Model.Head.Sl R sn a b c) := fun _ _ _ _ _ h =>
  ⟨(Sl_value Reading.gl world0 gl_numerals h).1, (Sl_value Reading.gl world0 gl_numerals h).2.1⟩

/-- The routine that reads the limbs of a block of the stream leaves state and context. -/
theorem leaves_xbA (R : Model.Head.Run) (t kh : ℕ) : Leaves (Model.Head.xbA R t kh) :=
  fun _ _ _ _ _ h =>
  ⟨(xbA_value Reading.gl world0 gl_numerals h).1, (xbA_value Reading.gl world0 gl_numerals h).2.1⟩

/-- The routine that reads the two limbs of a channel's activation leaves state and context. -/
theorem leaves_sh2 (R : Model.Head.Run) (t j : ℕ) : Leaves (Model.Head.sh2 R t j) :=
  fun _ _ _ _ _ h =>
  ⟨(sh2_value Reading.gl world0 gl_numerals h).1, (sh2_value Reading.gl world0 gl_numerals h).2.1⟩

/-- The routine that reads one of the six numbers of the cost ledger leaves state and context. -/
theorem leaves_gapAt (R : Model.Head.Run) (P : String) (i : ℕ) (w : E) :
    Leaves (Model.Head.gapAt R P i w) := fun _ _ _ _ _ h =>
  ⟨(gapAt_value Reading.gl world0 gl_numerals h).1,
    (gapAt_value Reading.gl world0 gl_numerals h).2.1⟩

/-- The routine that reads a row of the ledger with five limbs leaves state and context. -/
theorem leaves_row5At (R : Model.Head.Run) (P : String) : Leaves (Model.Head.row5At R P) :=
  fun _ _ _ _ _ h => ⟨(ok_row5At h).1, (ok_row5At h).2.1⟩

/-- The routine that returns the position coordinates of a segment's call leaves state and context.
-/
theorem leaves_ztSeg (R : Model.Head.Run) (sn : String) : Leaves (Model.Head.ztSeg R sn) := by
  unfold Model.Head.ztSeg
  exact leaves_bind (leaves_getAs _ _) fun _ => leaves_pure _

/-- The routine that reads the middle digit of a margin leaves state and context. -/
theorem leaves_middleDigit (R : Model.Head.Run) (sn : String) (w : E) :
    Leaves (Model.Head.middleDigit R sn w) := by
  unfold Model.Head.middleDigit
  exact leaves_bind (leaves_Sl _ _ _ _ _) fun _ => leaves_pure _

/-- The routine that reads the low digit of a margin leaves state and context. -/
theorem leaves_lowDigit (R : Model.Head.Run) (sn : String) (w : E) :
    Leaves (Model.Head.lowDigit R sn w) := by
  unfold Model.Head.lowDigit
  exact leaves_bind (leaves_Sl _ _ _ _ _) fun _ => leaves_pure _

/-- The form of a segment. -/
theorem leaves_LINE (R : Model.Head.Run) (sn : String) : Leaves (Model.Head.LINE R sn) := by
  unfold Model.Head.LINE
  try dsimp only
  refine leaves_bind (leaves_ewOf _ _) fun ew => ?_
  refine leaves_ite ?_ (leaves_ite ?_ (leaves_ite ?_ (leaves_ite ?_ (leaves_ite ?_
    (leaves_ite ?_ (leaves_refuse _))))))
  · exact leaves_bind (leaves_Sl _ _ _ _ _) fun _ => leaves_bind (leaves_Sl _ _ _ _ _) fun _ =>
      leaves_pure _
  · exact leaves_bind (leaves_Sl _ _ _ _ _) fun _ => leaves_pure _
  · refine leaves_bind (leaves_ztSeg _ _) fun zt => ?_
    refine leaves_ite (leaves_middleDigit _ _ _) (leaves_ite (leaves_lowDigit _ _ _) ?_)
    exact leaves_bind (leaves_gapAt _ _ _ _) fun _ => leaves_bind (leaves_gapAt _ _ _ _) fun _ =>
      leaves_bind (leaves_middleDigit _ _ _) fun _ => leaves_bind (leaves_lowDigit _ _ _) fun _ =>
        leaves_pure _
  · exact leaves_bind (leaves_ztSeg _ _) fun _ => leaves_bind (leaves_Sl _ _ _ _ _) fun _ =>
      leaves_bind (leaves_Sl _ _ _ _ _) fun _ => leaves_pure _
  · refine leaves_bind (leaves_tabAt _ _) fun t => ?_
    refine leaves_bind (leaves_forIn_range _ _ fun j c => ?_) fun _ => leaves_pure _
    exact leaves_bind (leaves_U3at _ _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
      leaves_pure _
  · refine leaves_bind (leaves_tabAt _ _) fun t => ?_
    refine leaves_bind (leaves_forIn_range _ _ fun j c => ?_) fun _ => ?_
    · exact leaves_bind (leaves_sh2 _ _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
        leaves_pure _
    · exact leaves_bind (leaves_Sl _ _ _ _ _) fun _ => leaves_pure _

/-- The form of a call's key vector. -/
theorem leaves_keyForm (R : Model.Head.Run) (q : ℕ) (laid : Array ℕ) :
    Leaves (Model.Head.keyForm R q laid) := by
  unfold Model.Head.keyForm
  try dsimp only
  refine leaves_bind (leaves_forIn_list _ _ fun g c => ?_) fun ⟨_, _⟩ => ?_
  · exact leaves_bind (leaves_LINE _ _) fun _ => leaves_bind (leaves_getAs _ _) fun _ =>
      leaves_bind (leaves_pure _) fun _ => leaves_pure _
  · refine leaves_bind (leaves_forIn_range _ _ fun j c => ?_) fun ⟨_, _⟩ => leaves_pure _
    refine leaves_ite ?_ ?_
    · refine leaves_bind (leaves_pure _) fun _ => leaves_ite ?_ ?_
      · exact leaves_bind (leaves_mustAs _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
          leaves_pure _
      · exact leaves_bind (leaves_pure _) fun _ => leaves_pure _
    · refine leaves_bind (leaves_pure _) fun _ => leaves_ite ?_ ?_
      · exact leaves_bind (leaves_mustAs _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
          leaves_pure _
      · exact leaves_bind (leaves_pure _) fun _ => leaves_pure _

/-! ## Routines that read and add claims -/

/-- The routine m, if it succeeds, leaves the context, and what it does to the state is to add a
list of claims. -/
def Adds {α : Type} (m : SubM α) : Prop :=
  ∀ F C a G D, Ok m F C a G D → D = C ∧ ∃ l, F.lins l = some G

/-- A routine that only adds claims keeps the state's shape. -/
theorem Adds.keeps {α : Type} {m : SubM α} (h : Adds m) : Keeps m := by
  intro F C a G D hs hk
  obtain ⟨_, l, hl⟩ := h F C a G D hk
  exact lins_cols l hs hl

/-- A routine that leaves state and context adds the empty list of claims. -/
theorem Leaves.adds {α : Type} {m : SubM α} (h : Leaves m) : Adds m := by
  intro F C a G D hk
  obtain ⟨e1, e2⟩ := h F C a G D hk
  rw [e1]
  exact ⟨e2, [], rfl⟩

/-- The routine that adds one claim adds the list of that claim. -/
theorem adds_lin (f : Aff) : Adds (SubM.lin f) := by
  intro F C a G D h
  rw [ok_lin] at h
  exact ⟨h.2, [f], lins_one h.1⟩

/-- One routine after another adds the two lists of claims, joined. -/
theorem adds_bind {α β : Type} {m : SubM α} {f : α → SubM β} (hm : Adds m)
    (hf : ∀ a, Adds (f a)) : Adds (m >>= f) := by
  intro F C b G D h
  rw [ok_bind] at h
  obtain ⟨a, F1, C1, h1, h2⟩ := h
  obtain ⟨e1, l1, a1⟩ := hm F C a F1 C1 h1
  obtain ⟨e2, l2, a2⟩ := hf a F1 C1 b G D h2
  exact ⟨e2.trans e1, l1 ++ l2, lins_append_some a1 a2⟩

/-- The routine behind the sum of squares leaves the context and only adds claims. -/
theorem adds_claimSquares (R : Model.Head.Run) : Adds (Model.Head.claimSquares R) := by
  unfold Model.Head.claimSquares Model.layerObject
  try dsimp only
  refine adds_bind (adds_lin _) fun _ => adds_bind (adds_lin _) fun _ =>
    adds_bind (leaves_mustAs _ _).adds fun _ => adds_bind (leaves_held _).adds fun e =>
      adds_bind (leaves_tabAt _ _).adds fun t => ?_
  refine adds_bind (Leaves.adds (leaves_forIn_range _ _ fun kh c => ?_)) fun _ => adds_lin _
  refine leaves_bind (leaves_forIn_range _ _ fun l c2 => ?_) fun _ =>
    leaves_bind (leaves_pure _) fun _ => leaves_pure _
  exact leaves_bind (leaves_U3at _ _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
    leaves_pure _

/-- With five limbs, the routine behind the stream times the reciprocal leaves the context and only
adds claims. -/
theorem adds_claimStream {R : Model.Head.Run} (hXL : R.h.XL = 5) :
    Adds (Model.Head.claimStream R) := by
  have h5 : (R.h.XL == 5) = true := by rw [hXL]; rfl
  unfold Model.Head.claimStream
  try dsimp only
  refine adds_bind (leaves_ewh _ _).adds fun wh => adds_bind (leaves_tabAt _ _).adds fun t => ?_
  refine adds_bind (Leaves.adds (leaves_forIn_range _ _ fun kh c => ?_)) fun SX => ?_
  · exact leaves_bind (leaves_xbA _ _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
      leaves_pure _
  · refine adds_bind (adds_lin _) fun _ => ?_
    rw [if_pos h5]
    refine adds_bind (Leaves.adds ?_) fun _ => adds_bind (adds_lin _) fun _ => adds_lin _
    have e : (fun x : Model.Row5 Aff => x.R) <$> Model.Head.row5At R "rt_N" =
        Model.Head.row5At R "rt_N" >>= fun a => pure a.R :=
      (bind_pure_comp _ _).symm
    rw [e]
    exact leaves_bind (leaves_row5At _ _) fun _ => leaves_pure _

/-- The routine of the acceptance policy leaves the context and only adds claims. -/
theorem adds_claimPolicy (R : Model.Head.Run) : Adds (Model.Head.claimPolicy R) := by
  unfold Model.Head.claimPolicy
  try dsimp only
  refine adds_bind (leaves_gapAt _ _ _ _).adds fun _ =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ => adds_bind (adds_lin _) fun _ =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ => adds_bind (adds_lin _) fun _ =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ => adds_bind (adds_lin _) fun _ =>
    adds_bind (leaves_tabAt _ _).adds fun te =>
    adds_bind (leaves_gapAt _ _ _ _).adds fun _ => ?_
  refine adds_bind (Leaves.adds (leaves_forIn_range _ _ fun l c => ?_)) fun _ => adds_lin _
  refine leaves_bind (leaves_forIn_range _ _ fun xh c2 => ?_) fun _ =>
    leaves_bind (leaves_pure _) fun _ => leaves_pure _
  exact leaves_bind (leaves_U3at _ _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
    leaves_pure _

/-- The routine behind the logits leaves the context and only adds claims. -/
theorem adds_claimLogits (R : Model.Head.Run) : Adds (Model.Head.claimLogits R) := by
  unfold Model.Head.claimLogits
  try dsimp only
  refine adds_bind (leaves_tabAt _ _).adds fun t => ?_
  refine adds_bind (Leaves.adds (leaves_forIn_range _ _ fun k c => ?_)) fun _ =>
    adds_bind (adds_lin _) fun _ => adds_lin _
  exact leaves_bind (leaves_sh2 _ _ _) fun _ => leaves_bind (leaves_pure _) fun _ =>
    leaves_pure _

/-- The routine marks the lookup's claim on the key vectors as added and adds one claim. -/
theorem ok_claimJoin {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (h : Ok (Model.Head.claimJoin R) F C u G D) :
    D = C ∧ ∃ f, (F.paid R.x.g1.owedJoin).lin f = some G := by
  unfold Model.Head.claimJoin at h
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨⟨KF, laid⟩, F1, C1, h1, h⟩ := h
  obtain ⟨e1, e2⟩ := leaves_forIn_range _ _
    (fun q c => leaves_bind (leaves_keyForm _ _ _) fun ⟨_, _⟩ =>
      leaves_bind (leaves_pure _) fun _ => leaves_pure _) _ _ _ _ _ h1
  try dsimp only at h
  rw [e1, e2, ok_bind] at h
  obtain ⟨_, F2, C2, h2, h⟩ := h
  obtain ⟨e3, e4⟩ := leaves_mustAs _ _ _ _ _ _ _ h2
  rw [e3, e4, ok_bind] at h
  obtain ⟨f, F3, C3, h3, h⟩ := h
  obtain ⟨e5, e6, _⟩ := ok_join h3
  rw [e5, e6, ok_lin] at h
  exact ⟨h.2, f, h.1⟩

/-! ## The other routines of the walk -/

/-- A public condition keeps the state's shape. -/
theorem keeps_must (b : Bool) : Keeps (SubM.must b) := keeps_slift _

/-- Recording the constant of the one equation leaves the state. -/
theorem ok_noteConstant {s : String} {F G : Fork} {C D : Ctx} {u : Unit}
    (h : Ok (Model.Head.noteConstant s) F C u G D) : G = F := by
  unfold Model.Head.noteConstant at h
  rw [ok_bind] at h
  obtain ⟨F0, F1, C1, h1, h2⟩ := h
  rw [ok_get] at h1
  have h3 : Ok (liftM (Blk.note ("head: " ++ ("constant behind " ++ s)) F0.c0) : SubM Unit)
      F1 C1 u G D := h2
  rw [ok_lift] at h3
  exact h3.2.trans h1.2.1

/-- The routine that adds the lookup's claims on mask entries keeps the state's shape. -/
theorem keeps_objects (g : Model.Forest.Heard) : Keeps (Model.Forest.objects g) := by
  unfold Model.Forest.objects
  exact keeps_bind (keeps_forM _) fun _ => keeps_paid _

/-- Adding the claims of a list, one after the other, as a fold. -/
theorem ok_foldlM_lin : ∀ (l : List Aff) (u0 : PUnit) (F : Fork) (C : Ctx) (u : PUnit) (G : Fork)
    (D : Ctx), Ok (l.foldlM (fun _ => SubM.lin) u0) F C u G D → D = C ∧ F.lins l = some G
  | [], u0, F, C, u, G, D, h => by
    rw [List.foldlM_nil, ok_pure] at h
    rw [h.2.1]
    exact ⟨h.2.2, rfl⟩
  | f :: l, u0, F, C, u, G, D, h => by
    rw [List.foldlM_cons, ok_bind] at h
    obtain ⟨u1, F1, C1, h1, h2⟩ := h
    rw [ok_lin] at h1
    obtain ⟨e, hl⟩ := ok_foldlM_lin l u1 F1 C1 u G D h2
    exact ⟨e.trans h1.2, lins_cons_some h1.1 hl⟩

/-- Adding the claims of an array, one after the other: the context is left, and the state is the
one that the list of these claims leads to. -/
theorem ok_forM_lin {l : Array Aff} {F G : Fork} {C D : Ctx} {u : PUnit}
    (h : Ok (l.forM SubM.lin) F C u G D) : D = C ∧ F.lins l.toList = some G := by
  unfold Array.forM at h
  rw [← Array.foldlM_toList] at h
  exact ok_foldlM_lin l.toList _ F C u G D h

/-- Which claims the lookup's routine objects adds: the forms that the lookup has kept as its rows,
in their order. Then it marks them as added. -/
theorem objects_list {g : Model.Forest.Heard} {F G : Fork} {C D : Ctx} {u : Unit}
    (h : Ok (Model.Forest.objects g) F C u G D) :
    D = C ∧ ∃ G', F.lins g.rows.toList = some G' ∧ G = G'.paid g.owedObjects := by
  unfold Model.Forest.objects at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h2⟩ := h
  obtain ⟨e1, hl⟩ := ok_forM_lin h1
  rw [ok_paid] at h2
  exact ⟨h2.2.trans e1, F1, hl, h2.1⟩

/-- With five limbs, the routine that adds the claims on the row ledger keeps the state's shape. -/
theorem keeps_claimLedger {R : Model.Head.Run} (hXL : R.h.XL = 5) :
    Keeps (Model.Head.claimLedger R) := by
  intro F C a G D hs h
  obtain ⟨_, _, _, _, _, hl⟩ := ok_claimLedger hXL hs h
  exact lins_cols _ hs hl

/-- The routine that adds the claim on the calls' key vectors keeps the state's shape. -/
theorem keeps_claimJoin (R : Model.Head.Run) : Keeps (Model.Head.claimJoin R) := by
  intro F C a G D hs h
  obtain ⟨_, f, hf⟩ := ok_claimJoin h
  have k1 : Kept F (F.paid R.x.g1.owedJoin) := ⟨hs, fun _ => rfl⟩
  exact k1.trans (lin_cols k1.1 hf)

/-- The claim that a sumcheck leaves: making it puts hidden values under slots. -/
theorem keeps_pscRow (p : Model.Psc) (S0 : E) (kept : Aff) : Keeps (Model.pscRow p S0 kept) := by
  unfold Model.pscRow
  exact keeps_bind (keeps_must _) fun _ => keeps_bind (keeps_hideRun _ _ _) fun _ => keeps_pure _

/-- The routine that forms the planes' value at a point keeps the state's shape, if its reads do. -/
theorem keeps_planesAt (g : Model.Forest.Heard) (lm e : ℕ) {bit : ℕ → ℕ → SubM Aff}
    (hb : ∀ a b, Keeps (bit a b)) : Keeps (Model.Forest.planesAt g lm e bit) := by
  unfold Model.Forest.planesAt
  try dsimp only
  exact keeps_foldlM _ _ fun f col => keeps_bind (hb _ _) fun _ => keeps_pure _

/-- The lookup's routine that adds the three claims on the planes keeps the state's shape, if its
reads do. -/
theorem keeps_planeLins (g : Model.Forest.Heard) (lm : ℕ) {bit : ℕ → ℕ → SubM Aff}
    {pin : ℕ → SubM Aff} (hb : ∀ a b, Keeps (bit a b)) (hp : ∀ a, Keeps (pin a)) :
    Keeps (Model.Forest.planeLins g lm bit pin) := by
  unfold Model.Forest.planeLins Model.Forest.planeClaims Model.Forest.planesAdded
  try dsimp only
  refine keeps_bind ?_ fun _ => keeps_bind (keeps_forM _) fun _ => keeps_paid _
  refine keeps_bind (keeps_must _) fun _ => keeps_bind (keeps_planesAt _ _ _ hb) fun _ =>
    keeps_bind (keeps_planesAt _ _ _ hb) fun _ => ?_
  refine keeps_bind (keeps_foldlM _ _ fun f col => ?_) fun _ => ?_
  · exact keeps_bind (hp _) fun _ => keeps_pure _
  · exact keeps_bind (keeps_pscRow _ _ _) fun ⟨_, _⟩ => keeps_pure _

/-- The routine that adds the three claims on the planes in the head's sub-proof keeps the state's
shape. -/
theorem keeps_claimPlanes (R : Model.Head.Run) : Keeps (Model.Head.claimPlanes R) := by
  unfold Model.Head.claimPlanes
  try dsimp only
  refine keeps_bind (leaves_tabAt _ _).keeps fun _ => keeps_bind (leaves_tabAt _ _).keeps fun _ =>
    keeps_bind (leaves_tabAt _ _).keeps fun _ => ?_
  exact keeps_planeLins _ _
    (fun _ _ => keeps_bind (keeps_lift _) fun _ => (leaves_U3at _ _ _).keeps)
    (fun _ => keeps_bind (keeps_lift _) fun _ => (leaves_U3at _ _ _).keeps)

/-! ## Routines of a link -/

/-- The routine m of a link, run from the link's state Lc, the state F of the sub-proof and the
context C, succeeds with the value a and leaves Lc', G and D. -/
def OkL {α : Type} (m : Model.LinkM α) (Lc : Model.LinkCtx) (F : Fork) (C : Ctx) (a : α)
    (Lc' : Model.LinkCtx) (G : Fork) (D : Ctx) : Prop :=
  Ok (m Lc) F C (a, Lc') G D

/-- A routine of a link that only returns a value succeeds, with that value, and leaves all three
states. -/
theorem okL_pure {α : Type} (a b : α) (Lc Lc' : Model.LinkCtx) (F G : Fork) (C D : Ctx) :
    OkL (pure a : Model.LinkM α) Lc F C b Lc' G D ↔ b = a ∧ Lc' = Lc ∧ G = F ∧ D = C := by
  have e : (pure a : Model.LinkM α) Lc = (pure (a, Lc) : SubM (α × Model.LinkCtx)) := rfl
  unfold OkL
  rw [e, ok_pure]
  constructor
  · rintro ⟨h1, h2, h3⟩
    cases h1
    exact ⟨rfl, rfl, h2, h3⟩
  · rintro ⟨rfl, rfl, h2, h3⟩
    exact ⟨rfl, h2, h3⟩

/-- One routine of a link after another succeeds exactly if the first succeeds and the second
succeeds from what the first leaves. -/
theorem okL_bind {α β : Type} (m : Model.LinkM α) (f : α → Model.LinkM β)
    (Lc Lc' : Model.LinkCtx) (F G : Fork) (C D : Ctx) (b : β) :
    OkL (m >>= f) Lc F C b Lc' G D ↔
      ∃ a L1 F1 C1, OkL m Lc F C a L1 F1 C1 ∧ OkL (f a) L1 F1 C1 b Lc' G D := by
  have e : (m >>= f) Lc = (m Lc >>= fun p => f p.1 p.2) := rfl
  unfold OkL
  rw [e, ok_bind]
  constructor
  · rintro ⟨⟨a, L1⟩, F1, C1, h1, h2⟩
    exact ⟨a, L1, F1, C1, h1, h2⟩
  · rintro ⟨a, L1, F1, C1, h1, h2⟩
    exact ⟨(a, L1), F1, C1, h1, h2⟩

/-- A routine of the sub-proof inside a link leaves the link's state. -/
theorem okL_lift {α : Type} (x : SubM α) (Lc Lc' : Model.LinkCtx) (F G : Fork) (C D : Ctx)
    (a : α) : OkL (liftM x : Model.LinkM α) Lc F C a Lc' G D ↔ Ok x F C a G D ∧ Lc' = Lc := by
  have e : (liftM x : Model.LinkM α) Lc = (x >>= fun y => pure (y, Lc)) := rfl
  unfold OkL
  rw [e, ok_bind]
  constructor
  · rintro ⟨y, F1, C1, h1, h2⟩
    rw [ok_pure] at h2
    obtain ⟨e1, e2, e3⟩ := h2
    cases e1
    rw [e2, e3]
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, G, D, h1, (ok_pure _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩⟩

/-! ## The walk -/

/-- Between two routines of the walk the constant of the one equation is recorded: the state stays,
the context may change. -/
def Noted (F : Fork) (C D : Ctx) : Prop := ∃ s, Ok (Model.Head.noteConstant s) F C () F D

/-- The routines of the walk, in the verifier's order, each with the state and the context from
which it starts and those that it leaves. The link's state is left. -/
theorem walk_parts {R : Model.Head.Run} {tl tl' : Model.HTailF2} {wo : Model.WsForkOut}
    {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx}
    (h : OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D) :
    Lc' = Lc ∧ ∃ (F1 F2 F3 F4 F5 F6 F7 F8 F9 : Fork) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : Ctx)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : Ctx),
      Ok (Model.Forest.objects R.x.g1) F C () F1 d0 ∧
      Noted F1 d0 c1 ∧
      Ok (Model.Head.claimSquares R) F1 c1 () F2 d1 ∧
      Noted F2 d1 c2 ∧
      Ok (Model.Head.claimLedger R) F2 c2 () F3 d2 ∧
      Noted F3 d2 c3 ∧
      Ok (Model.Head.claimStream R) F3 c3 () F4 d3 ∧
      Noted F4 d3 c4 ∧
      Ok (Model.Head.claimJoin R) F4 c4 () F5 d4 ∧
      Noted F5 d4 c5 ∧
      Ok (Model.Head.claimPolicy R) F5 c5 () F6 d5 ∧
      Noted F6 d5 c6 ∧
      Ok (Model.Head.claimPlanes R) F6 c6 () F7 d6 ∧
      Noted F7 d6 c7 ∧
      Ok (tl.objectsF R.t.funs) F7 c7 tl' F8 d7 ∧
      Noted F8 d7 c8 ∧
      Ok (Model.Head.claimLogits R) F8 c8 () F9 d8 ∧
      Noted F9 d8 c9 ∧
      Ok (Model.wsForkLin wo.toWsMerged) F9 c9 () G d9 ∧
      Noted G d9 D := by
  unfold Model.Head.walk at h
  rw [okL_bind] at h
  obtain ⟨_, L0a, F1, d0, a0, h⟩ := h
  rw [okL_lift] at a0
  rw [a0.2, okL_bind] at h
  obtain ⟨_, L0b, N0, c1, b0, h⟩ := h
  rw [okL_lift] at b0
  have n0 := ok_noteConstant b0.1
  rw [n0] at b0
  rw [b0.2, n0] at h
  rw [okL_bind] at h
  obtain ⟨_, L1a, F2, d1, a1, h⟩ := h
  rw [okL_lift] at a1
  rw [a1.2, okL_bind] at h
  obtain ⟨_, L1b, N1, c2, b1, h⟩ := h
  rw [okL_lift] at b1
  have n1 := ok_noteConstant b1.1
  rw [n1] at b1
  rw [b1.2, n1] at h
  rw [okL_bind] at h
  obtain ⟨_, L2a, F3, d2, a2, h⟩ := h
  rw [okL_lift] at a2
  rw [a2.2, okL_bind] at h
  obtain ⟨_, L2b, N2, c3, b2, h⟩ := h
  rw [okL_lift] at b2
  have n2 := ok_noteConstant b2.1
  rw [n2] at b2
  rw [b2.2, n2] at h
  rw [okL_bind] at h
  obtain ⟨_, L3a, F4, d3, a3, h⟩ := h
  rw [okL_lift] at a3
  rw [a3.2, okL_bind] at h
  obtain ⟨_, L3b, N3, c4, b3, h⟩ := h
  rw [okL_lift] at b3
  have n3 := ok_noteConstant b3.1
  rw [n3] at b3
  rw [b3.2, n3] at h
  rw [okL_bind] at h
  obtain ⟨_, L4a, F5, d4, a4, h⟩ := h
  rw [okL_lift] at a4
  rw [a4.2, okL_bind] at h
  obtain ⟨_, L4b, N4, c5, b4, h⟩ := h
  rw [okL_lift] at b4
  have n4 := ok_noteConstant b4.1
  rw [n4] at b4
  rw [b4.2, n4] at h
  rw [okL_bind] at h
  obtain ⟨_, L5a, F6, d5, a5, h⟩ := h
  rw [okL_lift] at a5
  rw [a5.2, okL_bind] at h
  obtain ⟨_, L5b, N5, c6, b5, h⟩ := h
  rw [okL_lift] at b5
  have n5 := ok_noteConstant b5.1
  rw [n5] at b5
  rw [b5.2, n5] at h
  rw [okL_bind] at h
  obtain ⟨_, L6a, F7, d6, a6, h⟩ := h
  rw [okL_lift] at a6
  rw [a6.2, okL_bind] at h
  obtain ⟨_, L6b, N6, c7, b6, h⟩ := h
  rw [okL_lift] at b6
  have n6 := ok_noteConstant b6.1
  rw [n6] at b6
  rw [b6.2, n6] at h
  rw [okL_bind] at h
  obtain ⟨t1, L7a, F8, d7, a7, h⟩ := h
  rw [okL_lift] at a7
  rw [a7.2, okL_bind] at h
  obtain ⟨_, L7b, N7, c8, b7, h⟩ := h
  rw [okL_lift] at b7
  have n7 := ok_noteConstant b7.1
  rw [n7] at b7
  rw [b7.2, n7] at h
  rw [okL_bind] at h
  obtain ⟨_, L8a, F9, d8, a8, h⟩ := h
  rw [okL_lift] at a8
  rw [a8.2, okL_bind] at h
  obtain ⟨_, L8b, N8, c9, b8, h⟩ := h
  rw [okL_lift] at b8
  have n8 := ok_noteConstant b8.1
  rw [n8] at b8
  rw [b8.2, n8] at h
  rw [okL_bind] at h
  obtain ⟨_, L9a, F10, d9, a9, h⟩ := h
  rw [okL_lift] at a9
  rw [a9.2, okL_bind] at h
  obtain ⟨_, L9b, N9, c10, b9, h⟩ := h
  rw [okL_lift] at b9
  have n9 := ok_noteConstant b9.1
  rw [n9] at b9
  rw [b9.2, n9] at h
  rw [okL_pure] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  rw [e1, e3, e4]
  exact ⟨e2, F1, F2, F3, F4, F5, F6, F7, F8, F9, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9,
    a0.1, ⟨_, b0.1⟩,
    a1.1, ⟨_, b1.1⟩,
    a2.1, ⟨_, b2.1⟩,
    a3.1, ⟨_, b3.1⟩,
    a4.1, ⟨_, b4.1⟩,
    a5.1, ⟨_, b5.1⟩,
    a6.1, ⟨_, b6.1⟩,
    a7.1, ⟨_, b7.1⟩,
    a8.1, ⟨_, b8.1⟩,
    a9.1, ⟨_, b9.1⟩⟩

/-- Each routine of the walk on which the files beside this one have theorems starts from a state
with one coefficient for each slot in which every array has as many columns as at the beginning of
the walk; and what each does to the state. hT: the routine of the smallness test keeps the state. It
is used for the last of the six routines alone. -/
theorem walk_states {R : Model.Head.Run} {tl tl' : Model.HTailF2} {wo : Model.WsForkOut}
    {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} (hXL : R.h.XL = 5)
    (hs : F.LS.size = F.ns) (hT : Keeps (tl.objectsF R.t.funs))
    (h : OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D) :
    ∃ (F1 F2 F3 F4 F5 F6 F8 F9 : Fork) (c1 c2 c3 c4 c5 c8 : Ctx),
      (Kept F F1 ∧ Ok (Model.Head.claimSquares R) F1 c1 () F2 c1 ∧ ∃ l, F1.lins l = some F2) ∧
      (Kept F F2 ∧ Ok (Model.Head.claimLedger R) F2 c2 () F3 c2 ∧ ∃ l, F2.lins l = some F3) ∧
      (Kept F F3 ∧ Ok (Model.Head.claimStream R) F3 c3 () F4 c3 ∧ ∃ l, F3.lins l = some F4) ∧
      (Kept F F4 ∧ Ok (Model.Head.claimJoin R) F4 c4 () F5 c4 ∧
        ∃ f, (F4.paid R.x.g1.owedJoin).lin f = some F5) ∧
      (Kept F F5 ∧ Ok (Model.Head.claimPolicy R) F5 c5 () F6 c5 ∧ ∃ l, F5.lins l = some F6) ∧
      (Kept F F8 ∧ Ok (Model.Head.claimLogits R) F8 c8 () F9 c8 ∧ ∃ l, F8.lins l = some F9) := by
  obtain ⟨_, F1, F2, F3, F4, F5, F6, F7, F8, F9, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9,
    a0, _, a1, _, a2, _, a3, _, a4, _, a5, _, a6, _, a7, _, a8, _, _, _⟩ := walk_parts h
  have k1 : Kept F F1 := keeps_objects _ F C _ F1 d0 hs a0
  have k2 : Kept F F2 := k1.trans ((adds_claimSquares R).keeps F1 c1 _ F2 d1 k1.1 a1)
  have k3 : Kept F F3 := k2.trans (keeps_claimLedger hXL F2 c2 _ F3 d2 k2.1 a2)
  have k4 : Kept F F4 := k3.trans ((adds_claimStream hXL).keeps F3 c3 _ F4 d3 k3.1 a3)
  have k5 : Kept F F5 := k4.trans (keeps_claimJoin R F4 c4 _ F5 d4 k4.1 a4)
  have k6 : Kept F F6 := k5.trans ((adds_claimPolicy R).keeps F5 c5 _ F6 d5 k5.1 a5)
  have k7 : Kept F F7 := k6.trans (keeps_claimPlanes R F6 c6 _ F7 d6 k6.1 a6)
  have k8 : Kept F F8 := k7.trans (hT F7 c7 _ F8 d7 k7.1 a7)
  obtain ⟨e1, l1⟩ := adds_claimSquares R F1 c1 _ F2 d1 a1
  obtain ⟨e2, _, _, _, _, l2⟩ := ok_claimLedger hXL k2.1 a2
  obtain ⟨e3, l3⟩ := adds_claimStream hXL F3 c3 _ F4 d3 a3
  obtain ⟨e4, l4⟩ := ok_claimJoin a4
  obtain ⟨e5, l5⟩ := adds_claimPolicy R F5 c5 _ F6 d5 a5
  obtain ⟨e8, l8⟩ := adds_claimLogits R F8 c8 _ F9 d8 a8
  rw [e1] at a1
  rw [e2] at a2
  rw [e3] at a3
  rw [e4] at a4
  rw [e5] at a5
  rw [e8] at a8
  exact ⟨F1, F2, F3, F4, F5, F6, F8, F9, c1, c2, c3, c4, c5, c8, ⟨k1, a1, l1⟩, ⟨k2, a2, _, l2⟩,
    ⟨k3, a3, l3⟩, ⟨k4, a4, l4⟩, ⟨k5, a5, l5⟩, ⟨k8, a8, l8⟩⟩

#print axioms keeps_hideRun
#print axioms leaves_LINE
#print axioms leaves_keyForm
#print axioms adds_claimSquares
#print axioms adds_claimStream
#print axioms adds_claimPolicy
#print axioms adds_claimLogits
#print axioms ok_claimJoin
#print axioms keeps_claimPlanes
#print axioms keeps_objects
#print axioms objects_list
#print axioms okL_bind
#print axioms okL_lift
#print axioms walk_parts
#print axioms walk_states

end OnBytes.Road.Hd.Walk
