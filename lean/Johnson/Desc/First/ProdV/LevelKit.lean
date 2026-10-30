--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ProdV/LevelKit.lean: small lemmas for the grand product's law
(Johnson/Desc/First/ProdV/LevelSound.lean): on lists and arrays; on what the part's texts return
(level, MaskedSum.whole, MaskedSum.row); on the ledger behind a hearing and its row (`ledger_of`);
on forms and worlds (`OnFilled`, `value_congr`, `value_later`, `cutWorld`); on points read off
arrays (`pt`, `pt_layBack`); on a level's order (`coords_facts`).

Limits. Of `verify-on-bytes` only pure functions and lemmas on them are used, no routine in a
context: OnBytes/Tie/Pv/Psc/PscFork.lean: Sized, Filled, Same, hideRun_ok, getD_set_self,
getD_set_other; OnBytes/Tie/Pv/Psc/PscLater.lean: Later, Later.trans, hideRun_later, shown_iff;
OnBytes/Model/HideLaws.lean: Reading, World, Aff.value and its laws, Fork.worldOf,
foldl_push_toList. One direction: from a return.
Not claimed: anything on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.ProdV.Level
import Johnson.Desc.Part.MaskedSumSound
import OnBytes.Tie.Pv.Psc.PscLater
import OnBytes.Desc.First.P2.ProdCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.ProdV
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.Part
open OnBytes.Desc.First.P1 OnBytes.Desc.First.P2

/-! ### Lists and arrays -/

theorem drop_succ_of_cons {α : Type} : ∀ (n : ℕ) (l : List α) (a : α) (t : List α),
    l.drop n = a :: t → l.drop (n + 1) = t
  | 0, [], _, _, h => by simp at h
  | 0, _ :: _, _, _, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    simp [h.2]
  | _ + 1, [], _, _, h => by simp at h
  | n + 1, _ :: l, a, t, h => by
    simpa using drop_succ_of_cons n l a t (by simpa using h)

theorem take_app {α : Type} : ∀ (l t : List α) (n : ℕ), l.length = n → (l ++ t).take n = l
  | [], _, n, h => by
    subst h
    rfl
  | a :: l, t, n, h => by
    subst h
    show a :: (l ++ t).take l.length = a :: l
    rw [take_app l t _ rfl]

theorem getLastD_snoc {α : Type} : ∀ (l : List α) (g d : α), (l ++ [g]).getLastD d = g
  | [], _, _ => rfl
  | a :: l, g, _ => by
    rw [List.cons_append, List.getLastD_cons]
    exact getLastD_snoc l g a

theorem mapM_two {α β : Type} (f : α → Option β) (x y : α) (l : List β)
    (h : [x, y].mapM f = some l) : ∃ a b, f x = some a ∧ f y = some b ∧ l = [a, b] := by
  cases hx : f x with
  | none => simp [List.mapM_cons, hx] at h
  | some a =>
    cases hy : f y with
    | none => simp [List.mapM_cons, hx, hy] at h
    | some b =>
      simp [List.mapM_cons, hx, hy] at h
      exact ⟨a, b, rfl, rfl, h.symm⟩

theorem getD_toList {α : Type} (a : Array α) (k : ℕ) (d : α) : a.getD k d = a.toList.getD k d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem getD_replicate (n i : ℕ) : (Array.replicate n zeroE).getD i zeroE = zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem getD_beyond {α : Type} (a : Array α) (k : ℕ) (d : α) (h : a.size ≤ k) : a.getD k d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

theorem size_set {α : Type} (a : Array α) (j : ℕ) (v : α) : (a.set! j v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

/-! ### What the texts return -/

/-- The call of the masked sumcheck that a level makes. -/
def levelCall (m : Nat) (z : Array E) (order : List Nat) : MaskedSum.Call :=
  ⟨0, levelVars m z order, some levelEnds⟩

/-- The level's end term: the product of the two shown end values. -/
def endProd : List E → List E → E := fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)

theorem level_spec {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    ∃ (hd : MaskedSum.Heard) (line : Fmt.RoundView) (s : List E),
      MaskedSum.whole C (levelCall m z order) endProd F (rs.take (m + 3)) = some (hd, o.row, G) ∧
      rs.drop (m + 3) = line :: rest ∧ MaskedSum.roundOf 0 1 line = some (s, [o.xi]) ∧
      o.r = layBack m order (hd.r.take m) ∧ o.sL = hd.sEnd ∧ o.sR = hd.sEnd + 1 := by
  unfold level at h
  split at h
  · cases h
  · split at h
    · rename_i hd row G' line rest' hw hdrop
      split at h
      · rename_i s xi hr
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          subst h1 h2 h3
          exact ⟨hd, line, s, hw, hdrop, hr, rfl, rfl, rfl⟩
      · cases h
    · cases h

theorem whole_spec {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff} {e : MaskedSum.Ends} (hk : k.ends = some e)
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G')) :
    ∃ (G : Fork) (sh : List E), MaskedSum.hear C k F rs = some (h, G) ∧
      MaskedSum.shownEnds h e.n G = some sh ∧
      MaskedSum.row h (endTerm h.r sh) {} G = some (f, G') := by
  unfold MaskedSum.whole at hw
  rw [hk] at hw
  cases hh : MaskedSum.hear C k F rs with
  | none => simp [hh] at hw
  | some x =>
    obtain ⟨h1, G⟩ := x
    cases hs : MaskedSum.shownEnds h1 e.n G with
    | none => simp [hh, hs] at hw
    | some sh =>
      cases hr : MaskedSum.row h1 (endTerm h1.r sh) {} G with
      | none => simp [hh, hs, hr] at hw
      | some y =>
        obtain ⟨f1, G1⟩ := y
        simp [hh, hs, hr] at hw
        obtain ⟨a1, a2, a3⟩ := hw
        subst a1 a2 a3
        exact ⟨G, sh, rfl, hs, hr⟩

theorem shownEnds_two {h : MaskedSum.Heard} {G : Fork} {sh : List E}
    (hs : MaskedSum.shownEnds h 2 G = some sh) :
    ∃ a b, G.shown h.sEnd = some a ∧ G.shown (h.sEnd + 1) = some b ∧ sh = [a, b] :=
  mapM_two (fun j => G.shown (h.sEnd + j)) 0 1 sh hs

theorem row_spec {h : MaskedSum.Heard} {S0 : E} {kept : Aff} {F G : Fork} {f : Aff}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) :
    F.hideRun h.first (Array.replicate (MaskedSum.hidingAt (h.vars.zip h.r)).1.length zeroE)
      (subE zeroE oneE) = some G := by
  unfold MaskedSum.row at hr
  cases hG : F.hideRun h.first
      (Array.replicate (MaskedSum.hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) with
  | none => simp [hG] at hr
  | some G' =>
    simp only [hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hr
    rw [hr.2]

/-! ### The ledger behind a hearing and its row -/

/-- What the ledger holds behind hear and row, from a ledger whose arrays have their size. -/
theorem ledger_of {C : Aff} {k : MaskedSum.Call} {F G1 G : Fork} {rs : List Fmt.RoundView}
    {hd : MaskedSum.Heard} {S0 : E} {f : Aff} {R : MaskedSum.Read} (hF : Sized F)
    (hh : MaskedSum.hear C k F rs = some (hd, G1)) (hrow : MaskedSum.row hd S0 {} G1 = some (f, G))
    (hR : MaskedSum.readAll k rs = some R) :
    hd.first = F.next ∧ hd.sEnd = F.next + MaskedSum.ownSlots k.all ∧ hd.start = C ∧
      hd.r = R.rounds.map (·.2) ∧ F.publicPart C = some hd.target ∧
      Later F G ∧ Sized G ∧ G.next = hd.sEnd + R.values.length ∧
      (∀ i, i < (MaskedSum.hidingAt (hd.vars.zip hd.r)).1.length →
        Filled G (hd.first + i) ∧ G.vp.getD (hd.first + i) zeroE = zeroE ∧
          G.mf.getD (hd.first + i) zeroE = subE zeroE oneE) ∧
      (∀ i, i < R.values.length →
        Filled G (hd.sEnd + i) ∧ G.vp.getD (hd.sEnd + i) zeroE = G1.vp.getD (hd.sEnd + i) zeroE ∧
          G.mf.getD (hd.sEnd + i) zeroE = hd.r.getLastD zeroE) := by
  obtain ⟨_, T, R', hT, hR', hrec, hfill⟩ := MaskedSum.hear_spec hh
  have hRR : R' = R := Option.some.inj (hR'.symm.trans hR)
  subst hRR
  have hrow' := row_spec hrow
  have e1 : hd.first = F.next := by rw [hrec]
  have e2 : hd.sEnd = F.next + MaskedSum.ownSlots k.all := by rw [hrec]
  have e3 : hd.start = C := by rw [hrec]
  have e4 : hd.r = R'.rounds.map (·.2) := by rw [hrec]
  have e5 : hd.target = T := by rw [hrec]
  have hF1 : Sized
      ({ F with next := F.next + MaskedSum.ownSlots k.all + R'.values.length } : Fork) := hF
  have lF : Later F
      ({ F with next := F.next + MaskedSum.ownSlots k.all + R'.values.length } : Fork) :=
    ⟨Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _), rfl, id,
      fun _ h => ⟨h, rfl, rfl⟩⟩
  obtain ⟨a1, a2, a3, _⟩ := hideRun_ok _ G1 _ _ _ hF1 hfill
  have l1 := hideRun_later hF1 hfill
  obtain ⟨b1, b2, b3, _⟩ := hideRun_ok G1 G _ _ _ a2 hrow'
  have l2 := hideRun_later a2 hrow'
  refine ⟨e1, e2, e3, e4, by rw [e5]; exact hT, (lF.trans l1).trans l2, b2, ?_, ?_, ?_⟩
  · rw [b1.next, a1.next, e2]
  · intro i hi
    obtain ⟨_, _, c3, c4, c5⟩ := b3 i (by simpa using hi)
    exact ⟨c3, by rw [c4, getD_replicate], c5⟩
  · intro i hi
    obtain ⟨_, _, c3, _, c5⟩ := a3 i (by simpa using hi)
    rw [← e2] at c3 c5
    obtain ⟨d1, d2, d3⟩ := l2.keep _ c3
    exact ⟨d1, d2, by rw [d3, c5, e4]⟩

/-! ### Forms and worlds -/

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- Every slot that the form names is filled and lies below the next free slot. -/
def OnFilled (F : Fork) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, Filled F x.1 ∧ x.1 < F.next

/-- A form's value reads a world only at the slots that the form names, and at the entries. -/
theorem value_congr (a : Aff) (W W' : World K) (he : W.entry = W'.entry)
    (hs : ∀ x ∈ a.slots.toList, W.slot x.1 = W'.slot x.1) : a.value ρ W = a.value ρ W' := by
  have h1 : a.ents.toList.map (Ent.value ρ W) = a.ents.toList.map (Ent.value ρ W') :=
    List.map_congr_left fun x _ => by simp only [Ent.value, he]
  have h2 : a.slots.toList.map (slotValue ρ W) = a.slots.toList.map (slotValue ρ W') :=
    List.map_congr_left fun x hx => by simp only [slotValue, hs x hx]
  simp only [Aff.value, h1, h2]

/-- A form on filled slots is worth the same at every later ledger. -/
theorem value_later {F G : Fork} (h : Later F G) (a : Aff) (ha : OnFilled F a) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) :
    a.value ρ (G.worldOf ρ mask entry) = a.value ρ (F.worldOf ρ mask entry) :=
  value_congr ρ a _ _ rfl fun x hx => by
    show ρ.val (G.vp.getD x.1 zeroE) - ρ.val (G.mf.getD x.1 zeroE) * mask x.1 =
      ρ.val (F.vp.getD x.1 zeroE) - ρ.val (F.mf.getD x.1 zeroE) * mask x.1
    rw [(h.keep x.1 (ha x hx).1).2.1, (h.keep x.1 (ha x hx).1).2.2]

theorem slot_later {F G : Fork} (h : Later F G) {j : ℕ} (hj : Filled F j) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) :
    (G.worldOf ρ mask entry).slot j = (F.worldOf ρ mask entry).slot j := by
  show ρ.val (G.vp.getD j zeroE) - ρ.val (G.mf.getD j zeroE) * mask j =
    ρ.val (F.vp.getD j zeroE) - ρ.val (F.mf.getD j zeroE) * mask j
  rw [(h.keep j hj).2.1, (h.keep j hj).2.2]

/-- The world W below the slot c; the mask row's own entries from c on. -/
def cutWorld (W : World K) (mask : ℕ → K) (c : ℕ) : World K :=
  ⟨fun j => if j < c then W.slot j else mask j, W.entry⟩

theorem cutWorld_lt (W : World K) (mask : ℕ → K) {c j : ℕ} (h : j < c) :
    (cutWorld W mask c).slot j = W.slot j := if_pos h

theorem cutWorld_ge (W : World K) (mask : ℕ → K) {c j : ℕ} (h : ¬ j < c) :
    (cutWorld W mask c).slot j = mask j := if_neg h

theorem dotFrom_congr : ∀ (u : List E) (h h' : ℕ → K), (∀ i, i < u.length → h i = h' i) →
    MaskedSum.dotFrom ρ h u = MaskedSum.dotFrom ρ h' u
  | [], _, _, _ => rfl
  | x :: u, h, h', H => by
    show ρ.val x * h 0 + MaskedSum.dotFrom ρ (fun i => h (i + 1)) u =
      ρ.val x * h' 0 + MaskedSum.dotFrom ρ (fun i => h' (i + 1)) u
    rw [H 0 (by simp), dotFrom_congr u _ _ fun i hi => H (i + 1) (by simpa using hi)]

end

theorem addMul_slots (a b : Aff) (k : E) : (Aff.addMul a b k).slots.toList =
    a.slots.toList ++ b.slots.toList.map fun x => (x.1, mulE x.2 k) :=
  foldl_push_toList (fun x : Nat × E => (x.1, mulE x.2 k)) b.slots a.slots

theorem OnFilled.addMul {F : Fork} {a b : Aff} (k : E) (ha : OnFilled F a) (hb : OnFilled F b) :
    OnFilled F (Aff.addMul a b k) := by
  intro x hx
  rw [addMul_slots] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
    exact hb y hy

theorem OnFilled.empty (F : Fork) : OnFilled F {} := by
  intro x hx
  simp at hx

theorem OnFilled.slot {F : Fork} {j : ℕ} (h : Filled F j ∧ j < F.next) :
    OnFilled F (Aff.slot j) := by
  intro x hx
  have e : x = (j, oneE) := by simpa [Aff.slot] using hx
  subst e
  exact h

theorem OnFilled.later {F G : Fork} {a : Aff} (h : Later F G) (ha : OnFilled F a) :
    OnFilled G a := fun x hx =>
  ⟨(h.keep x.1 (ha x hx).1).1, Nat.lt_of_lt_of_le (ha x hx).2 h.next⟩

theorem onFilled_stepDown {G : Fork} {o : LevelOut} (hL : Filled G o.sL ∧ o.sL < G.next)
    (hR : Filled G o.sR ∧ o.sR < G.next) : OnFilled G (stepDown o).2 := by
  show OnFilled G (Aff.addMul (Aff.addMul {} (Aff.slot o.sL) (subE oneE o.xi))
    (Aff.addMul {} (Aff.slot o.sR) o.xi) oneE)
  exact ((OnFilled.empty G).addMul _ (OnFilled.slot hL)).addMul _
    ((OnFilled.empty G).addMul _ (OnFilled.slot hR))

/-! ### Points read off arrays -/

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- An array of elements as a point: coordinate k is the reading of member k; 0 behind the end. -/
def pt (a : Array E) : ℕ → K := fun k => ρ.val (a.getD k zeroE)

theorem pt_beyond (a : Array E) (k : ℕ) (h : a.size ≤ k) : pt ρ a k = 0 := by
  show ρ.val (a.getD k zeroE) = 0
  rw [getD_beyond a k zeroE h, ρ.zero]

theorem pt_set (a : Array E) (j : ℕ) (v : E) (hj : j < a.size) :
    pt ρ (a.set! j v) = Function.update (pt ρ a) j (ρ.val v) := by
  funext k
  rw [Function.update_apply]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl]
    show ρ.val ((a.set! k v).getD k zeroE) = _
    rw [getD_set_self a k v zeroE hj]
  · rw [if_neg hk]
    show ρ.val ((a.set! j v).getD k zeroE) = ρ.val (a.getD k zeroE)
    rw [getD_set_other a j k v zeroE hk]

theorem pt_replicate (m : ℕ) : pt ρ (Array.replicate m zeroE) = fun _ => 0 := by
  funext k
  show ρ.val ((Array.replicate m zeroE).getD k zeroE) = 0
  rw [getD_replicate, ρ.zero]

theorem pt_cons (x : E) (r : Array E) : pt ρ (#[x] ++ r) = pcons (ρ.val x) (pt ρ r) := by
  funext k
  cases k with
  | zero =>
    show ρ.val ((#[x] ++ r).getD 0 zeroE) = ρ.val x
    rw [getD_toList]
    simp
  | succ k =>
    show ρ.val ((#[x] ++ r).getD (k + 1) zeroE) = ρ.val (r.getD k zeroE)
    rw [getD_toList, getD_toList]
    simp

theorem pt_fold (m : ℕ) : ∀ (order : List ℕ) (cs : List E) (a : Array E), a.size = m →
    (∀ b ∈ order, b < m) →
    pt ρ ((order.zip cs).foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) a) =
      place (order.map fun b => m - 1 - b) (cs.map ρ.val) (pt ρ a)
  | [], _, _, _, _ => by simp [place]
  | _ :: _, [], _, _, _ => by simp [place]
  | b :: order, c :: cs, a, ha, hb => by
    have hbm : b < m := hb b (by simp)
    have ih := pt_fold m order cs (a.set! (m - 1 - b) c) (by rw [size_set]; exact ha)
      fun x hx => hb x (by simp [hx])
    rw [pt_set ρ a (m - 1 - b) c (by omega)] at ih
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons, place] at ih ⊢
    exact ih

/-- The point that a level hands back is the challenges laid at the coordinates of the order. -/
theorem pt_layBack (m : ℕ) (order : List ℕ) (cs : List E) (hb : ∀ b ∈ order, b < m) :
    pt ρ (layBack m order cs) =
      place (order.map fun b => m - 1 - b) (cs.map ρ.val) (fun _ => 0) := by
  unfold layBack
  rw [pt_fold ρ m order cs _ (by simp) hb, pt_replicate]

end

theorem fold_size (m : ℕ) : ∀ (l : List (ℕ × E)) (a : Array E),
    (l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) a).size = a.size
  | [], _ => rfl
  | x :: l, a => by
    rw [List.foldl_cons, fold_size m l, size_set]

theorem layBack_size (m : ℕ) (order : List ℕ) (cs : List E) : (layBack m order cs).size = m := by
  unfold layBack
  rw [fold_size]
  simp

/-! ### A level's order -/

theorem orderOk_facts {m : ℕ} {order : List ℕ} (h : orderOk m order = true) :
    order.length = m ∧ (∀ b ∈ order, b < m) ∧ ∀ b, b < m → order.count b = 1 := by
  simp only [orderOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The coordinates in the order of the rounds: each of the m coordinates just once. -/
theorem coords_facts {m : ℕ} {order : List ℕ} (h : orderOk m order = true) :
    (order.map fun b => m - 1 - b).Nodup ∧ (∀ i ∈ order.map fun b => m - 1 - b, i < m) ∧
      (∀ k, k < m → k ∈ order.map fun b => m - 1 - b) ∧
      (order.map fun b => m - 1 - b).length = m := by
  obtain ⟨hl, hlt, hc⟩ := orderOk_facts h
  have hn : order.Nodup := List.nodup_iff_count_le_one.mpr fun a => by
    by_cases ha : a ∈ order
    · rw [hc a (hlt a ha)]
    · rw [List.count_eq_zero_of_not_mem ha]
      omega
  refine ⟨List.Nodup.map_on (fun x hx y hy e => ?_) hn, fun i hi => ?_, fun k hk => ?_, ?_⟩
  · have e' : m - 1 - x = m - 1 - y := e
    have := hlt x hx
    have := hlt y hy
    omega
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
    have := hlt b hb
    show m - 1 - b < m
    omega
  · have hm : m - 1 - k ∈ order := List.count_pos_iff.mp (by rw [hc _ (by omega)]; omega)
    exact List.mem_map.mpr ⟨m - 1 - k, hm, by show m - 1 - (m - 1 - k) = k; omega⟩
  · rw [List.length_map]
    exact hl

/-! ### The level's call, read -/

theorem level_shapeOk (m : ℕ) (z : Array E) (order : List ℕ) :
    MaskedSum.shapeOk ⟨0, levelVars m z order, some levelEnds⟩ = true := by
  simp only [MaskedSum.shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun v hv => ?_, by decide, by decide⟩
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
  exact ⟨by show 2 ≤ 3; omega, by show 3 ≤ 65; omega⟩

theorem all_wt {K : Type} [Field K] (ρ : Reading K) (m : ℕ) (z : Array E) (order : List ℕ) :
    (⟨0, levelVars m z order, some levelEnds⟩ : MaskedSum.Call).all.map (MaskedSum.Var.wt ρ) =
      (order.map fun b => m - 1 - b).map (fun i => ptWt (pt ρ z i) 3) ++ [ptWt 0 3] := by
  show (levelVars m z order ++ [MaskedSum.Var.point zeroE 3]).map (MaskedSum.Var.wt ρ) = _
  have h1 : (MaskedSum.Var.wt ρ ∘ fun b => MaskedSum.Var.point (z.getD (m - 1 - b) zeroE) 3) =
      ((fun i => ptWt (pt ρ z i) 3) ∘ fun b => m - 1 - b) := rfl
  have h2 : [MaskedSum.Var.point zeroE 3].map (MaskedSum.Var.wt ρ) = [ptWt (0 : K) 3] := by
    show [ptWt (ρ.val zeroE) 3] = _
    rw [ρ.zero]
  rw [List.map_append, levelVars, List.map_map, List.map_map, h1, h2]

end VerifiableInference.Desc.First.ProdV
