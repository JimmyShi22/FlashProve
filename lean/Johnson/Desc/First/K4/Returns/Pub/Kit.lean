-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Kit.lean: SMALL GENERAL LAWS on two values that may be missing
(OptRel, OnBytes/Flat/LinksFreeLayer.lean), on folds and maps whose value may be missing, on sizes
of arrays, and on readers of the forms' environment (OnBytes/Model/LayerForms.lean).

Limits. Nothing here says that any function returns: each law compares two calls, or gives a size.
Nothing is evaluated. ropeFactor_size says again, to the letter, a statement of the library
(OnBytes.Road.ropeFactor_size, Johnson/Road/FormsKeysQK.lean). No property is claimed.

  OptRel.some, .isSome_eq, .mono, .of_right, .of_left, optRel_of_isSome, optRel_ite, optRel_guard,
  ite_isSome
  foldlM_opt_rel_mem, foldlM_opt_rel   a fold whose step reads the state, at two steps.
  foldlM_all2_rel, afoldlM_all2_rel    the same over two lists, or arrays, member by member.
  amapM_size_rel    a map over the numbers below n, at two functions: both are missing, or both
                    have n members.
  all2_push         one member more at the end of two arrays.
  getElem?_size, eqTab_size_eq, eqLow_size_eq, cutLast_rel, length_flatMap_two, size_flatMap_two,
  ropeFactor_size
  callOf_skel, ewOf_skel, ewh_skel, SxsA_skel, shSum_skel   readers at two environments.
-/
import Johnson.Desc.First.K4.Returns.Pub.Skel
import Johnson.Road.K4.Total.SkelReaders
import OnBytes.Desc.First.K4.StackPublic
import OnBytes.Flat.PendingSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind size_eqTab)
open OnBytes.Desc.First.K4.Total (EnvSkel bind_same amapM_same sumForms_same tabAt_skel xbA_skel
  longA_skel tensorAt_skel shIn_skel)

/-! ## Two values that may be missing -/

theorem OptRel.some {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) :
    OptRel R (Option.some a) (Option.some b) := h

theorem OptRel.isSome_eq {α : Type} {R : α → α → Prop} {x y : Option α} (h : OptRel R x y) :
    x.isSome = y.isSome := by
  cases x <;> cases y
  · rfl
  · exact h.elim
  · exact h.elim
  · rfl

theorem OptRel.mono {α : Type} {R S : α → α → Prop} (hs : ∀ a b, R a b → S a b) {x y : Option α}
    (h : OptRel R x y) : OptRel S x y := by
  cases x <;> cases y
  · trivial
  · exact h.elim
  · exact h.elim
  · exact hs _ _ h

/-- Where the second is there, so is the first. -/
theorem OptRel.of_right {α : Type} {R : α → α → Prop} {x y : Option α} {b : α} (h : OptRel R x y)
    (hy : y = Option.some b) : ∃ a, x = Option.some a ∧ R a b := by
  subst hy
  cases x
  · exact h.elim
  · exact ⟨_, rfl, h⟩

/-- Where the first is there, so is the second. -/
theorem OptRel.of_left {α : Type} {R : α → α → Prop} {x y : Option α} {a : α} (h : OptRel R x y)
    (hx : x = Option.some a) : ∃ b, y = Option.some b ∧ R a b := by
  subst hx
  cases y
  · exact h.elim
  · exact ⟨_, rfl, h⟩

theorem optRel_of_isSome {α : Type} {x y : Option α} (h : x.isSome = y.isSome) :
    OptRel (fun _ _ => True) x y := by
  cases x <;> cases y
  · trivial
  · cases h
  · cases h
  · trivial

theorem optRel_ite {α : Type} {R : α → α → Prop} {c : Prop} [Decidable c] {x y x' y' : Option α}
    (h1 : OptRel R x x') (h2 : OptRel R y y') :
    OptRel R (if c then x else y) (if c then x' else y') := by
  by_cases h : c
  · simpa only [if_pos h] using h1
  · simpa only [if_neg h] using h2

/-- An early test, behind which nothing is returned where it fails, in front of the rest: at two
tests that agree. -/
theorem optRel_guard {β : Type} {R : β → β → Prop} {c c' : Prop} [Decidable c] [Decidable c']
    (h : c ↔ c') {f f' : PUnit → Option β} (hf : OptRel R (f ⟨⟩) (f' ⟨⟩)) :
    OptRel R ((if c then none else pure PUnit.unit) >>= f)
      ((if c' then none else pure PUnit.unit) >>= f') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]
    trivial
  · rw [if_neg hc, if_neg (mt h.mpr hc)]
    exact hf

theorem ite_isSome {α β : Type} {c : Prop} [Decidable c] {a b : Option α} {a' b' : Option β}
    (h1 : a.isSome = a'.isSome) (h2 : b.isSome = b'.isSome) :
    (if c then a else b).isSome = (if c then a' else b').isSome := by
  by_cases h : c
  · simpa only [if_pos h] using h1
  · simpa only [if_neg h] using h2

/-! ## Folds and maps whose value may be missing -/

/-- A fold whose step reads the state, at two steps. -/
theorem foldlM_opt_rel_mem {α σ : Type} {R : σ → σ → Prop} {f f' : σ → α → Option σ} :
    ∀ (l : List α), (∀ a a' x, x ∈ l → R a a' → OptRel R (f a x) (f' a' x)) →
      ∀ a a', R a a' → OptRel R (l.foldlM f a) (l.foldlM f' a')
  | [], _, _, _, r => by
    rw [List.foldlM_nil, List.foldlM_nil]
    exact r
  | x :: l, h, a, a', r => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact optRel_bind (h a a' x (List.mem_cons_self ..) r) fun b b' rb =>
      foldlM_opt_rel_mem l (fun c c' z hz => h c c' z (List.mem_cons_of_mem _ hz)) b b' rb

theorem foldlM_opt_rel {α σ : Type} {R : σ → σ → Prop} {f f' : σ → α → Option σ}
    (h : ∀ a a' x, R a a' → OptRel R (f a x) (f' a' x)) (l : List α) (a a' : σ) (r : R a a') :
    OptRel R (l.foldlM f a) (l.foldlM f' a') :=
  foldlM_opt_rel_mem l (fun a a' x _ => h a a' x) a a' r

/-- The same over two lists, member by member. -/
theorem foldlM_all2_rel {α β σ : Type} {S : α → β → Prop} {R : σ → σ → Prop}
    {f : σ → α → Option σ} {f' : σ → β → Option σ}
    (h : ∀ a a' x y, R a a' → S x y → OptRel R (f a x) (f' a' y)) {l : List α} {l' : List β}
    (hl : All2 S l l') : ∀ a a', R a a' → OptRel R (l.foldlM f a) (l'.foldlM f' a') := by
  induction hl with
  | nil =>
    intro a a' r
    rw [List.foldlM_nil, List.foldlM_nil]
    exact r
  | cons h0 _ ih =>
    intro a a' r
    rw [List.foldlM_cons, List.foldlM_cons]
    exact optRel_bind (h _ _ _ _ r h0) fun b b' rb => ih b b' rb

/-- The same over two arrays. -/
theorem afoldlM_all2_rel {α β σ : Type} {S : α → β → Prop} {R : σ → σ → Prop}
    {f : σ → α → Option σ} {f' : σ → β → Option σ}
    (h : ∀ a a' x y, R a a' → S x y → OptRel R (f a x) (f' a' y)) {l : Array α} {l' : Array β}
    (hl : All2 S l.toList l'.toList) (a a' : σ) (r : R a a') :
    OptRel R (l.foldlM f a) (l'.foldlM f' a') := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact foldlM_all2_rel h hl a a' r

/-- A map over the numbers below n, at two functions that are there at the same numbers. -/
theorem amapM_size_rel {β : Type} (n : Nat) {f f' : Nat → Option β}
    (h : ∀ i, i < n → (f i).isSome = (f' i).isSome) :
    OptRel (fun a a' => a.size = n ∧ a'.size = n) ((Array.range n).mapM f)
      ((Array.range n).mapM f') := by
  have e : ((Array.range n).mapM f).isSome = ((Array.range n).mapM f').isSome :=
    amapM_same (Array.range n) fun i hi => h i (by
      rw [Array.toList_range] at hi
      exact List.mem_range.mp hi)
  cases h1 : (Array.range n).mapM f with
  | none =>
    cases h2 : (Array.range n).mapM f' with
    | none => trivial
    | some b =>
      rw [h1, h2] at e
      cases e
  | some a =>
    cases h2 : (Array.range n).mapM f' with
    | none =>
      rw [h1, h2] at e
      cases e
    | some b => exact ⟨mapM_size h1, mapM_size h2⟩

/-- One member more at the end of two arrays. -/
theorem all2_push {α β : Type} {R : α → β → Prop} {l : Array α} {l' : Array β} {a : α} {b : β}
    (h : All2 R l.toList l'.toList) (hab : R a b) :
    All2 R (l.push a).toList (l'.push b).toList := by
  rw [Array.toList_push, Array.toList_push]
  exact h.append (.cons hab .nil)

/-! ## Sizes -/

theorem getElem?_size {α β : Type} {a : Array α} {b : Array β} (h : a.size = b.size) (i : Nat) :
    (a[i]?).isSome = (b[i]?).isSome := by
  by_cases hi : i < a.size
  · have hj : i < b.size := by omega
    have e1 : a[i]? = Option.some a[i] := getElem?_pos a i hi
    have e2 : b[i]? = Option.some b[i] := getElem?_pos b i hj
    simp only [e1, e2, Option.isSome_some]
  · have hj : ¬ i < b.size := by omega
    have e1 : a[i]? = none := getElem?_neg a i hi
    have e2 : b[i]? = none := getElem?_neg b i hj
    simp only [e1, e2, Option.isSome_none]

theorem eqTab_size_eq {z z' : Array E} (h : z.size = z'.size) :
    (eqTab z).size = (eqTab z').size := by
  rw [size_eqTab, size_eqTab, h]

theorem eqLow_size_eq {rs rs' : Array E} (h : rs.size = rs'.size) (lo hi : Nat) :
    (eqLow rs lo hi).size = (eqLow rs' lo hi).size := by
  unfold eqLow
  refine eqTab_size_eq ?_
  rw [Array.size_reverse, Array.size_reverse, Array.size_extract, Array.size_extract, h]

/-- A point cut in two, at two points of one size. -/
theorem cutLast_rel {z z' : Array E} (h : z.size = z'.size) (k : Nat) :
    OptRel (fun p p' => p.1.size = p'.1.size ∧ p.2.size = p'.2.size) (cutLast z k).toOption
      (cutLast z' k).toOption := by
  unfold cutLast
  by_cases hk : k > z.size
  · have hk' : k > z'.size := h ▸ hk
    rw [if_pos hk, if_pos hk']
    trivial
  · have hk' : ¬ k > z'.size := h ▸ hk
    rw [if_neg hk, if_neg hk']
    refine OptRel.some ⟨?_, ?_⟩
    · rw [Array.size_extract, Array.size_extract, h]
    · rw [Array.size_extract, Array.size_extract, h]

theorem length_flatMap_two {α β : Type} (f : α → List β) (h : ∀ a, (f a).length = 2) :
    ∀ l : List α, (l.flatMap f).length = 2 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, h, length_flatMap_two f h l, List.length_cons]
    omega

theorem size_flatMap_two {β : Type} (n : Nat) (f : Nat → Array β) (h : ∀ i, (f i).size = 2) :
    ((Array.range n).flatMap f).size = 2 * n := by
  rw [← Array.length_toList, Array.toList_flatMap,
    length_flatMap_two _ (fun i => by rw [Array.length_toList]; exact h i), Array.length_toList,
    Array.size_range]

/-- The factor on the coordinates within a head has two members for each pair of coordinates. The
same statement stands in Johnson/Road/FormsKeysQK.lean (OnBytes.Road.ropeFactor_size). -/
theorem ropeFactor_size (c : ClaimEnv) (et lfc : Array E) (lam : Nat) :
    (c.ropeFactor et lfc lam).size = 2 * (c.v.y.h.dh / 2) := by
  unfold ClaimEnv.ropeFactor
  exact size_flatMap_two _ _ fun _ => rfl

/-! ## Readers of the forms' environment, at two environments -/

variable {v v₀ : Env}

/-- The call that holds a segment. -/
theorem callOf_skel (hy : v.y = v₀.y) (sn : String) : v.callOf sn = v₀.callOf sn := by
  unfold Env.callOf
  rw [hy]

theorem ewOf_skel (hy : v.y = v₀.y) (sn : String) : (v.ewOf sn).isSome = (v₀.ewOf sn).isSome := by
  unfold Env.ewOf
  rw [Option.isSome_map, Option.isSome_map, callOf_skel hy]

theorem ewh_skel (hy : v.y = v₀.y) (sn : String) : (v.ewh sn).isSome = (v₀.ewh sn).isSome := by
  unfold Env.ewh
  rw [Option.isSome_map, Option.isSome_map, callOf_skel hy]

/-- A residual stream's sum over blocks, whatever the weights. -/
theorem SxsA_skel (S : EnvSkel v v₀) (wh wh₀ : Array E) (Z : String) (sg : Nat) :
    (v.SxsA wh Z sg).isSome = (v₀.SxsA wh₀ Z sg).isSome := by
  unfold Env.SxsA
  rw [S.y]
  simp only [tabAt_skel S]
  refine bind_same _ fun tb => bind_same _ fun txs => sumForms_same _ fun xh _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  exact ite_isSome (xbA_skel S tb xh) (longA_skel S tb txs _ xh)

/-- A tensor's sum over entries at a token point, whatever the weights. -/
theorem shSum_skel (S : EnvSkel v v₀) (ew ew₀ : Array E) (n : Nat) (X P : String) (i : Nat) :
    (v.shSum ew n X P i).isSome = (v₀.shSum ew₀ n X P i).isSome := by
  unfold Env.shSum
  rw [tensorAt_skel S]
  refine sumForms_same n fun x _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  exact shIn_skel S _ i x

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.OptRel.some
#print axioms OnBytes.Desc.First.K4.RtPub.OptRel.isSome_eq
#print axioms OnBytes.Desc.First.K4.RtPub.OptRel.mono
#print axioms OnBytes.Desc.First.K4.RtPub.OptRel.of_right
#print axioms OnBytes.Desc.First.K4.RtPub.OptRel.of_left
#print axioms OnBytes.Desc.First.K4.RtPub.optRel_of_isSome
#print axioms OnBytes.Desc.First.K4.RtPub.optRel_ite
#print axioms OnBytes.Desc.First.K4.RtPub.optRel_guard
#print axioms OnBytes.Desc.First.K4.RtPub.ite_isSome
#print axioms OnBytes.Desc.First.K4.RtPub.foldlM_opt_rel_mem
#print axioms OnBytes.Desc.First.K4.RtPub.foldlM_opt_rel
#print axioms OnBytes.Desc.First.K4.RtPub.foldlM_all2_rel
#print axioms OnBytes.Desc.First.K4.RtPub.afoldlM_all2_rel
#print axioms OnBytes.Desc.First.K4.RtPub.amapM_size_rel
#print axioms OnBytes.Desc.First.K4.RtPub.all2_push
#print axioms OnBytes.Desc.First.K4.RtPub.getElem?_size
#print axioms OnBytes.Desc.First.K4.RtPub.eqTab_size_eq
#print axioms OnBytes.Desc.First.K4.RtPub.eqLow_size_eq
#print axioms OnBytes.Desc.First.K4.RtPub.cutLast_rel
#print axioms OnBytes.Desc.First.K4.RtPub.length_flatMap_two
#print axioms OnBytes.Desc.First.K4.RtPub.size_flatMap_two
#print axioms OnBytes.Desc.First.K4.RtPub.ropeFactor_size
#print axioms OnBytes.Desc.First.K4.RtPub.callOf_skel
#print axioms OnBytes.Desc.First.K4.RtPub.ewOf_skel
#print axioms OnBytes.Desc.First.K4.RtPub.ewh_skel
#print axioms OnBytes.Desc.First.K4.RtPub.SxsA_skel
#print axioms OnBytes.Desc.First.K4.RtPub.shSum_skel
