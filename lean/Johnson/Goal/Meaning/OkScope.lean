-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/OkScope.lean: the lookup's own test on its record, FoNums.ok
(OnBytes/Tie/Pv/Lookup/Port/FoNums.lean:131), says yes at the three sorts of record of the public
part; and the host's count of padding keys at a layers' link returns.

The library has the law: what Forest.shape returns, with a pub that pubAsk takes, passes FoNums.ok
(shape_ok, OnBytes/Tie/Pv/Lookup/Port/FoShape.lean:132; shapeOf_ok, Peel/FoPayCaller.lean:45), and
that the three layouts' records are such (Fo.layout_shape, Ends/FoPublicShape.lean:27;
Fo.Pub2.shapeOf_shapeHid, Ends/FoLookPubA.lean:64; Fo.Pub2.shapeOf_headLayout,
Ends/FoLookPubH.lean:51). Here they are drawn together at publicOf's X.
  ok_layers, ok_head: FoNums.ok X.y.fo and FoNums.ok X.HLy.fs WHEREVER publicOf RETURNS.
  ok_att: FoNums.ok Ag.fs at the plan of every group, wherever publicOf returns with p4.
  ok_att_in_scope: FoNums.ok (fsA X g) for g < 12, in the goals' scope.
  laidOf_some: Env.laidOf (OnBytes/Model/LayerForms.lean:601) returns, and keeps the array's size,
    if every column's tree lies within the array.
  tree_in_scope: in the goals' scope every column of a call lies in a tree of that call.
  laid_in_scope: in the goals' scope: weighedOf returns on all calls, and the fold of laidOf over
    what it returns, from Forest.noPub X.y.fo, returns: the text of the host's count at a layers'
    link, at the environment Alg.envG X.layers 0 [].
-/
import Johnson.Goal.Meaning.WeighedScope
import Johnson.Goal.Meaning.LookScope
import Johnson.Goal.Meaning.AttForInScope
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicShape
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubH
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Layer (Env Lay)
open OnBytes.Model.Verify (publicOf Public layerShape)

section Any
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- The layers' layout, wherever publicOf returns. -/
theorem layout_of_public (h : publicOf pol KL lay = .ok X) :
    Layer.layout (layerShape X.P) X.P.polCalls = .ok X.y := by
  obtain ⟨P, y, hpl, eP, ey, -⟩ := Hd.public_parts h
  have hy := Hd.layerLayout_of_polLayout hpl
  rw [← eP, ← ey] at hy
  exact hy

theorem ok_layers (h : publicOf pol KL lay = .ok X) : FoNums.ok X.y.fo = true :=
  Fo.Pay.shapeOf_ok (Fo.layout_shape (layout_of_public h))

theorem ok_head (h : publicOf pol KL lay = .ok X) : FoNums.ok X.HLy.fs = true := by
  obtain ⟨P, y, -, -, -, -, -, hl, -⟩ := Hd.public_parts h
  exact Fo.Pay.shapeOf_ok (Fo.Pub2.shapeOf_headLayout hl).1

theorem ok_att (h : publicOf pol KL lay = .ok X) (hp4 : (layerShape X.P).p4 = true) {g : ℕ}
    (hg : g < X.y.NGr) : ∃ Ag, X.A[g]? = some Ag ∧ FoNums.ok Ag.fs = true := by
  obtain ⟨Ag, lines, cf, hA, -, -, hh, -⟩ := hid_of_public h hp4 hg
  exact ⟨Ag, hA, Fo.Pay.shapeOf_ok (Fo.Pub2.shapeOf_shapeHid hh).1⟩

end Any

/-! ## laidOf returns -/

/-- A fold of steps that may refuse returns, if every step keeps a property under which no step
refuses. -/
theorem fold_some {β : Type} (f : β → ℕ → Option β) (P : β → Prop) (N : ℕ)
    (hs : ∀ b x, x < N → P b → ∃ b', f b x = some b' ∧ P b') :
    ∀ n, n ≤ N → ∀ b, P b → ∃ b', (List.range n).foldlM f b = some b' ∧ P b'
  | 0, _, b, hb => ⟨b, rfl, hb⟩
  | n + 1, hn, b, hb => by
    obtain ⟨b1, h1, p1⟩ := fold_some f P N hs n (by omega) b hb
    obtain ⟨b2, h2, p2⟩ := hs b1 n (by omega) p1
    refine ⟨b2, ?_, p2⟩
    rw [List.range_succ, List.foldlM_append, h1]
    show List.foldlM f b1 [n] = some b2
    rw [List.foldlM_cons, h2]
    rfl

theorem laidOf_some (v : Env) (q : ℕ) (weighed : Array Bool) (laid : Array ℕ)
    (H : ∀ x, x < weighed.size →
      v.y.fo.first.getD q 0 + x / 2 ^ (v.y.fo.dT - v.y.h.lt) < laid.size) :
    ∃ laid', v.laidOf q weighed laid = some laid' ∧ laid'.size = laid.size := by
  unfold Layer.Env.laidOf
  refine fold_some _ (fun b => b.size = laid.size) weighed.size (fun b x hx hb => ?_) _
    (Nat.le_refl _) laid rfl
  by_cases hw : weighed.getD x true = true
  · exact ⟨b, if_pos hw, hb⟩
  · have h2 := H x hx
    rw [← hb] at h2
    refine ⟨b.modify (v.y.fo.first.getD q 0 + x / 2 ^ (v.y.fo.dT - v.y.h.lt)) (· + v.y.T), ?_, ?_⟩
    · rw [if_neg hw]
      exact if_pos h2
    · show (b.modify _ _).size = laid.size
      rw [Array.size_modify]
      exact hb

/-- The like over any list. -/
theorem foldl_some {α β : Type} (f : β → α → Option β) (P : β → Prop) : ∀ l : List α,
    (∀ a ∈ l, ∀ b, P b → ∃ b', f b a = some b' ∧ P b') →
    ∀ b, P b → ∃ b', l.foldlM f b = some b' ∧ P b'
  | [], _, b, hb => ⟨b, rfl, hb⟩
  | a :: l, H, b, hb => by
    obtain ⟨b1, h1, p1⟩ := H a List.mem_cons_self b hb
    obtain ⟨b2, h2, p2⟩ := foldl_some f P l (fun x hx => H x (List.mem_cons_of_mem _ hx)) b1 p1
    refine ⟨b2, ?_, p2⟩
    rw [List.foldlM_cons, h1]
    exact h2

/-- A list's mapM returns if the function returns at each member. -/
theorem mapM_some {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b) →
    ∃ r, l.mapM f = some r ∧ r.length = l.length ∧
      ∀ i, i < l.length → ∃ a b, l[i]? = some a ∧ r[i]? = some b ∧ f a = some b
  | [], _ => ⟨[], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | a :: l, H => by
    obtain ⟨b, hb⟩ := H a List.mem_cons_self
    obtain ⟨r, hr, hl, hi⟩ := mapM_some f l fun x hx => H x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: r, ?_, by simp [hl], fun i hi' => ?_⟩
    · rw [List.mapM_cons, hb, hr]
      rfl
    · cases i with
      | zero => exact ⟨a, b, rfl, rfl, hb⟩
      | succ i =>
        obtain ⟨a', b', e1, e2, e3⟩ := hi i (by simpa using hi')
        exact ⟨a', b', by simpa using e1, by simpa using e2, e3⟩

/-! ## In scope -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

theorem ok_att_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    FoNums.ok (Att.fsA X g) = true := by
  obtain ⟨cf, hh, -⟩ := Att.hid_in_scope hZ hR h hg
  exact Fo.Pay.shapeOf_ok (Fo.Pub2.shapeOf_shapeHid hh).1

/-- In scope every column of call q lies in a tree of the call. -/
theorem tree_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {q : ℕ} {cd : CallD} (hq : X.y.calls[q]? = some cd)
    {x : ℕ} (hx : x < X.y.Lam * cd.J) :
    X.y.fo.first.getD q 0 + x / 2 ^ (X.y.fo.dT - X.y.h.lt) < X.y.fo.NT := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  have hy := B.lay
  obtain ⟨f1, f2, f3⟩ := fo_of_layout hy
  have hqs : q < X.y.calls.size := by
    rcases Nat.lt_or_ge q X.y.calls.size with a | a
    · exact a
    · rw [Array.getElem?_eq_none a] at hq
      cases hq
  have hNC : q < X.y.fo.NC := by rw [f2, f3]; exact hqs
  obtain ⟨-, -, c, -⟩ := Cb.Fo.ok_parts (ok_layers h)
  obtain ⟨-, -, hn, hb⟩ := c q hNC
  -- the call's record
  have hcl : X.y.fo.calls[q]? = some (X.y.callRecord q cd) := by
    rw [f1, cl_of_layout hy]
    simp [hq]
  have hn' : X.y.h.ll + cd.lJ + X.y.h.lt = FoNums.io X.y.fo q + X.y.fo.dT := by
    rw [← hn]
    unfold FoNums.nOf
    rw [hcl]
    rfl
  -- the numbers of columns
  have hJ : cd.J = 2 ^ cd.lJ := by
    obtain ⟨cl, taken, -, -, hc⟩ := (admitted_of_layout hy B.switches.p3).calls
    have hm : cd ∈ X.y.calls := Array.mem_of_getElem? hq
    rw [hc] at hm
    obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (Array.mem_def.mp hm)
    rfl
  have hLam : X.y.Lam = 2 ^ X.y.h.ll := (laid_of_layout hy B.switches.p3).2.Lam
  have hlt : X.y.h.lt ≤ X.y.fo.dT := by
    have a := look_hot hZ hR h
    have e : X.y.h.lt = Inst.Model.All.DF.lT := by
      rw [shape_of_public h, shape_in_scope hZ hR h]
      rfl
    rw [e]
    exact a
  have hx' : x < 2 ^ (FoNums.io X.y.fo q) * 2 ^ (X.y.fo.dT - X.y.h.lt) := by
    rw [← pow_add, show FoNums.io X.y.fo q + (X.y.fo.dT - X.y.h.lt) = X.y.h.ll + cd.lJ by omega,
      pow_add, ← hLam, ← hJ]
    exact hx
  exact (hb _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx'))).1

/-- THE HOST's COUNT AT A LAYERS' LINK RETURNS, in the goals' scope. -/
theorem laid_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    ∃ laid, ((X.y.calls.mapM (Alg.envG X.layers 0 []).weighedOf).bind fun weighed =>
      weighed.toList.zipIdx.foldlM
        (fun laid x => (Alg.envG X.layers 0 []).laidOf x.2 x.1 laid)
        (Forest.noPub X.y.fo)) = some laid := by
  obtain ⟨r, hr, hl, hi⟩ := mapM_some (Alg.envG X.layers 0 []).weighedOf X.y.calls.toList
    fun cd hcd => weighed_in_scope hZ hR h cd (Array.mem_def.mpr hcd)
  have e : X.y.calls.mapM (Alg.envG X.layers 0 []).weighedOf = some r.toArray := by
    rw [Array.mapM_eq_mapM_toList, hr]
    rfl
  rw [e]
  show ∃ laid, r.zipIdx.foldlM
    (fun laid x => (Alg.envG X.layers 0 []).laidOf x.2 x.1 laid) (Forest.noPub X.y.fo) = some laid
  obtain ⟨laid, hlaid, -⟩ := foldl_some
    (fun laid (x : Array Bool × ℕ) => (Alg.envG X.layers 0 []).laidOf x.2 x.1 laid)
    (fun b => b.size = X.y.fo.NT) r.zipIdx
    (fun x hx b hb => by
      have hx' : r[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.mp hx
      have hq : x.2 < X.y.calls.toList.length := by
        rw [← hl]
        rcases Nat.lt_or_ge x.2 r.length with a | a
        · exact a
        · rw [List.getElem?_eq_none a] at hx'
          cases hx'
      obtain ⟨cd, w, e1, e2, e3⟩ := hi x.2 hq
      have ew : w = x.1 := Option.some.inj (e2.symm.trans hx')
      subst ew
      have hcq : X.y.calls[x.2]? = some cd := by
        rw [← Array.getElem?_toList]
        exact e1
      have hsz : x.1.size = X.y.Lam * cd.J := by
        rw [weighedOf_eq] at e3
        rw [(marks_spec _ _ _ e3).1, Array.size_replicate]
        rfl
      obtain ⟨b', h1, h2⟩ := laidOf_some (Alg.envG X.layers 0 []) x.2 x.1 b fun y hy => by
        rw [hb]
        exact tree_in_scope hZ hR h hcq (by rw [← hsz]; exact hy)
      exact ⟨b', h1, h2.trans hb⟩)
    (Forest.noPub X.y.fo) (Array.size_replicate ..)
  exact ⟨laid, hlaid⟩

#print axioms ok_layers
#print axioms ok_head
#print axioms ok_att
#print axioms ok_att_in_scope
#print axioms laidOf_some
#print axioms tree_in_scope
#print axioms laid_in_scope

end Meaning.P34
