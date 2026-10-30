-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/TablesSpec.lean: kind K5: what tablesP
(Johnson/Desc/First/Att/TablesP.lean) lays where: each named table lies in the list with its matrix,
its block's length and its weight vector, and its length is stored under its first entry.

Main names:
  `Ext s s'`: a later state of the placing: what was laid stays; the lengths stored under earlier
    first entries stay. `Tab s t mat len phi e`, `AsTabS`: a table's facts at a state. `Sp r Q`:
    wherever r returns, the state behind is a later one and Q holds there. `Stable`. The rules bind,
    pure, lift, mono; `sp_add`, `sp_addRow`, `sp_lng`, `sp_addLong`, `sp_addAs`, `sp_mapM`,
    `sp_tail`.
  `PosG g`: a premise on six public numbers: NAs, kAs / NAs, fillH, fillO T / 2^la, fillQ T / 2^la
    and kbA are not 0. An empty table would share its first entry with the next one, and the length
    stored under that entry would be the next one's.
  `TablesAre g mats lk p t n`, `sp_placeAll`, `tables_are`: tablesP g mats nW lk p = some t → PosG g
    → ∃ n, TablesAre g mats lk p t n.
Nothing of OnBytes is used but the field's type E.
Not claimed: that a table is true of a matrix.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.TablesAgree

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T)

variable {α β : Type}

/-- A later state of the placing: what was laid stays; the lengths stored under earlier first entries stay. -/
structure Ext (s s' : Placed) : Prop where
  funs : ∀ f ∈ s.funs.toList, f ∈ s'.funs.toList
  len : ∀ k < s.next, s'.tabLen.lookup k = s.tabLen.lookup k
  next : s.next ≤ s'.next

theorem Ext.refl (s : Placed) : Ext s s := ⟨fun _ h => h, fun _ _ => rfl, le_refl _⟩

theorem Ext.trans {a b c : Placed} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨fun f hf => h2.funs f (h1.funs f hf),
    fun k hk => (h2.len k (lt_of_lt_of_le hk h1.next)).trans (h1.len k hk), le_trans h1.next h2.next⟩

/-- A table lies in the list with these numbers and weights; its length is stored under its first entry. -/
structure Tab (s : Placed) (t mat len : ℕ) (phi : Array E) (e : ℕ) : Prop where
  laid : ∃ f ∈ s.funs.toList, f.start = t ∧ f.mat = mat ∧ f.len = len ∧ f.phi = phi
  size : s.tabLen.lookup t = some e
  lt : t < s.next

theorem Tab.ext {s s' : Placed} {t mat len e : ℕ} {phi : Array E} (h : Tab s t mat len phi e)
    (x : Ext s s') : Tab s' t mat len phi e :=
  ⟨by obtain ⟨f, hf, r⟩ := h.laid; exact ⟨f, x.funs f hf, r⟩, (x.len t h.lt).trans h.size,
    lt_of_lt_of_le h.lt x.next⟩

/-- Wherever r returns: the state behind is a later one, and Q holds of what is returned there. -/
def Sp (r : T α) (Q : α → Placed → Prop) : Prop :=
  ∀ s a s', r s = some (a, s') → Ext s s' ∧ Q a s'

def Stable (Q : Placed → Prop) : Prop := ∀ s s', Q s → Ext s s' → Q s'

theorem tbind_some {r : T α} {k : α → T β} {s : Placed} {x : β × Placed} (h : (r >>= k) s = some x) :
    ∃ y, r s = some y ∧ k y.1 y.2 = some x := by
  have h' : (r s).bind (fun y => k y.1 y.2) = some x := h
  cases hr : r s with
  | none => rw [hr] at h'; cases h'
  | some y => rw [hr] at h'; exact ⟨y, rfl, h'⟩

theorem Sp.bind {r : T α} {k : α → T β} {Q : α → Placed → Prop} {R : α → β → Placed → Prop}
    (h1 : Sp r Q) (hs : ∀ a, Stable (Q a)) (h2 : ∀ a, Sp (k a) (R a)) :
    Sp (r >>= k) fun b s => ∃ a, Q a s ∧ R a b s := by
  intro s b s' h
  obtain ⟨y, e1, e2⟩ := tbind_some h
  obtain ⟨x1, q⟩ := h1 s y.1 y.2 e1
  obtain ⟨x2, r'⟩ := h2 y.1 y.2 b s' e2
  exact ⟨x1.trans x2, y.1, hs y.1 _ _ q x2, r'⟩

theorem Sp.pure (a : α) : Sp (Pure.pure a : T α) fun b _ => b = a := by
  intro s b s' h
  have h' : some (a, s) = some (b, s') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  exact ⟨Ext.refl _, rfl⟩

theorem Sp.lift (x : Option α) : Sp (monadLift x : T α) fun _ _ => True := by
  intro s b s' h
  cases x with
  | none => cases h
  | some a =>
    have h' : some (a, s) = some (b, s') := h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨Ext.refl _, trivial⟩

theorem Sp.mono {r : T α} {Q Q' : α → Placed → Prop} (h : Sp r Q) (f : ∀ a s, Q a s → Q' a s) : Sp r Q' :=
  fun s a s' e => ⟨(h s a s' e).1, f a s' (h s a s' e).2⟩

theorem stable_true : Stable fun _ => True := fun _ _ _ _ => trivial
theorem stable_const (p : Prop) : Stable fun _ => p := fun _ _ h _ => h
theorem stable_tab (t mat len e : ℕ) (phi : Array E) : Stable fun s => Tab s t mat len phi e :=
  fun _ _ h x => h.ext x
theorem Stable.and {P Q : Placed → Prop} (h1 : Stable P) (h2 : Stable Q) : Stable fun s => P s ∧ Q s :=
  fun s s' h x => ⟨h1 s s' h.1 x, h2 s s' h.2 x⟩

/-! ### the routines -/

theorem sp_add (mats : Array (ℕ × ℕ)) (mat len : ℕ) (phi : Array E) (e : ℕ) (he : 0 < e) :
    Sp (P.add mats mat len phi e) fun a s => Tab s a mat len phi e ∧ P.fits mats mat len e = true := by
  intro s a s' h
  unfold P.add P.mustAs at h
  cases hf : P.fits mats mat len e with
  | false => rw [hf] at h; cases h
  | true =>
    rw [hf] at h
    have h' : some (s.next, Placed.mk (s.next + e) ((s.next, e) :: s.tabLen)
      (s.funs.push (Fun1.mk mat len phi 2 s.next))) = some (a, s') := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    refine ⟨⟨fun f hf => by simp [hf], fun k hk => ?_, Nat.le_add_right _ _⟩,
      ⟨⟨Fun1.mk mat len phi 2 s.next, by simp, rfl, rfl, rfl, rfl⟩, by simp [List.lookup],
        by show s.next < s.next + e; omega⟩, rfl⟩
    show List.lookup k ((s.next, e) :: s.tabLen) = _
    rw [List.lookup_cons]
    have : (k == s.next) = false := by simp; omega
    rw [this]

theorem sp_weights (n : ℕ) (f : Unit → Array E) : Sp (P.T.weights n f) fun a _ => a = f () := by
  unfold P.T.weights
  exact Sp.pure _

theorem sp_addRow (g : Geo) (mats : Array (ℕ × ℕ)) (psi : Unit → Array E) (he : 0 < g.fillH) :
    Sp (P.addRow g mats psi) fun a s => Tab s a g.NAs g.T (psi ()) g.fillH ∧
      P.fits mats g.NAs g.T g.fillH = true := by
  unfold P.addRow
  refine (Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun w => sp_add mats _ _ w _ he).mono ?_
  rintro a s ⟨w, rfl, q⟩
  exact q

theorem sp_getAs (n : String) (x : Option α) : Sp (P.T.getAs n x) fun a _ => x = some a := by
  cases x with
  | none => intro s a s' h; cases h
  | some v => exact (Sp.pure v).mono fun a _ e => by rw [e]

theorem sp_lng (g : Geo) (zc : Array E) (ptk : Unit → Array E) :
    Sp (P.lng g zc ptk) fun a _ => ∃ c, P.cutLast zc g.ls = some c ∧ a = P.blockRows (P.eqTab c.2) (ptk ()) := by
  unfold P.lng
  refine (Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun w =>
    Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind (sp_getAs _ _) (fun _ => stable_const _) fun c => sp_weights _ _).mono ?_
  rintro a s ⟨w, rfl, _, _, c, hc, rfl⟩
  exact ⟨c, hc, rfl⟩

theorem sp_addLong (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc : Array E) (ptk : Unit → Array E)
    (e : ℕ) (he : 0 < e) : Sp (P.addLong g mats mat zc ptk e) fun a s =>
      ∃ c, P.cutLast zc g.ls = some c ∧ Tab s a mat (2 ^ g.la) (P.blockRows (P.eqTab c.2) (ptk ())) e ∧
        P.fits mats mat (2 ^ g.la) e = true := by
  unfold P.addLong
  refine (Sp.bind (sp_lng g zc ptk) (fun _ => stable_const _) fun w => sp_add mats _ _ w _ he).mono ?_
  rintro a s ⟨w, ⟨c, hc, rfl⟩, q⟩
  exact ⟨c, hc, q⟩

theorem add_some {mats : Array (ℕ × ℕ)} {mat len e a : ℕ} {phi : Array E} {s s' : Placed}
    (h : P.add mats mat len phi e s = some (a, s')) : P.fits mats mat len e = true ∧ a = s.next ∧
      s' = Placed.mk (s.next + e) ((s.next, e) :: s.tabLen) (s.funs.push (Fun1.mk mat len phi 2 s.next)) := by
  unfold P.add P.mustAs at h
  cases hf : P.fits mats mat len e with
  | false => rw [hf] at h; cases h
  | true =>
    rw [hf] at h
    have h' : some (s.next, Placed.mk (s.next + e) ((s.next, e) :: s.tabLen)
      (s.funs.push (Fun1.mk mat len phi 2 s.next))) = some (a, s') := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨rfl, rfl, rfl⟩

theorem discard_some {r : T α} {s s' : Placed} {u : PUnit} (h : (discard r) s = some (u, s')) :
    ∃ a, r s = some (a, s') := by
  have h' : (r s).bind (fun x => some (PUnit.unit, x.2)) = some (u, s') := h
  cases hr : r s with
  | none => rw [hr] at h'; cases h'
  | some y =>
    rw [hr] at h'
    have e : y.2 = s' := (Prod.mk.inj (Option.some.inj h')).2
    exact ⟨y.1, by rw [← e]⟩

theorem forM_parts (mats : Array (ℕ × ℕ)) (len : ℕ) (phi : Array E) (w : ℕ) (hw : 0 < w) :
    ∀ (qs : List ℕ) (s s' : Placed) (u : PUnit),
      (qs.forM fun q => discard (P.add mats q len phi w)) s = some (u, s') →
      s'.next = s.next + qs.length * w ∧ Ext s s' ∧
      (∀ n q, qs[n]? = some q → ∃ f ∈ s'.funs.toList, f.start = s.next + n * w ∧ f.mat = q ∧ f.len = len ∧
        f.phi = phi) ∧ ∀ q ∈ qs, P.fits mats q len w = true
  | [], s, s', u, h => by
    have h' : some (PUnit.unit, s) = some (u, s') := h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨by simp, Ext.refl _, fun n q hq => by simp at hq, fun q hq => by cases hq⟩
  | q0 :: qs, s, s', u, h => by
    have h0 : ((discard (P.add mats q0 len phi w) : T PUnit) >>= fun _ =>
      qs.forM fun q => discard (P.add mats q len phi w)) s = some (u, s') := h
    obtain ⟨y, e1, e2⟩ := tbind_some h0
    obtain ⟨a, ea⟩ := discard_some (u := y.1) (s' := y.2) e1
    obtain ⟨x1, _⟩ := sp_add mats q0 len phi w hw s a y.2 ea
    obtain ⟨ff, _, es⟩ := add_some ea
    obtain ⟨n2, x2, l2, f2⟩ := forM_parts mats len phi w hw qs y.2 s' u e2
    have en : y.2.next = s.next + w := by rw [es]
    refine ⟨by rw [n2, en, List.length_cons]; ring, x1.trans x2, ?_, ?_⟩
    · intro n q hq
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        subst hq
        refine ⟨Fun1.mk q0 len phi 2 s.next, x2.funs _ (by rw [es]; simp), by simp, rfl, rfl, rfl⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at hq
        obtain ⟨f, hf, a1, a2⟩ := l2 n q hq
        exact ⟨f, hf, by rw [a1, en]; ring, a2⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact ff
      · exact f2 q hq'

/-- A table on the planes' matrix: the tables of its parts side by side; the length of all under the first entry. -/
structure AsTabS (s : Placed) (g : Geo) (t : ℕ) (phi : Array E) : Prop where
  laid : ∀ q < g.NAs, ∃ f ∈ s.funs.toList, f.start = t + q * (g.kAs / g.NAs) ∧ f.mat = q ∧
    f.len = 2 ^ g.lmS ∧ f.phi = phi
  size : s.tabLen.lookup t = some (g.NAs * (g.kAs / g.NAs))
  lt : t < s.next

theorem stable_as (g : Geo) (t : ℕ) (phi : Array E) : Stable fun s => AsTabS s g t phi :=
  fun _ _ h x => ⟨fun q hq => by obtain ⟨f, hf, r⟩ := h.laid q hq; exact ⟨f, x.funs f hf, r⟩,
    (x.len t h.lt).trans h.size, lt_of_lt_of_le h.lt x.next⟩

theorem sp_addAs (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Unit → Array E) (hn : 0 < g.NAs)
    (hw : 0 < g.kAs / g.NAs) : Sp (P.addAs g mats phi) fun a s => AsTabS s g a (phi ()) ∧
      ∀ q < g.NAs, P.fits mats q (2 ^ g.lmS) (g.kAs / g.NAs) = true := by
  intro s a s'' h
  unfold P.addAs P.T.weights P.T.placed P.T.total at h
  obtain ⟨y0, e0, h⟩ := tbind_some h
  have e0' : some (phi (), s) = some y0 := e0
  obtain rfl := Option.some.inj e0'
  obtain ⟨y1, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y1 := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  obtain ⟨n2, x2, l2, f2⟩ := forM_parts mats _ _ _ hw _ s y2.2 y2.1 e2
  obtain ⟨y3, e3, h⟩ := tbind_some h
  have e3' : some (PUnit.unit, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some y3 := e3
  obtain rfl := Option.some.inj e3'
  have h' : some (s.next, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some (a, s'') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  rw [List.length_range] at n2
  have hpos : 0 < g.NAs * (g.kAs / g.NAs) := Nat.mul_pos hn hw
  refine ⟨⟨x2.funs, fun k hk => ?_, x2.next⟩, ⟨fun q hq => l2 q q (by simp [hq]), ?_, ?_⟩,
    fun q hq => f2 q (List.mem_range.2 hq)⟩
  · show List.lookup k ((s.next, _) :: y2.2.tabLen) = _
    rw [List.lookup_cons]
    have : (k == s.next) = false := by simp; omega
    rw [this]
    exact x2.len k hk
  · show List.lookup s.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) = _
    rw [List.lookup_cons, beq_self_eq_true, n2]
    simp
  · show s.next < y2.2.next
    omega

theorem sp_mapML {ι : Type} (f : ι → T α) (Q : ι → α → Placed → Prop) (hf : ∀ x, Sp (f x) (Q x))
    (hs : ∀ x a, Stable (Q x a)) :
    ∀ xs : List ι, Sp (xs.mapM f) fun ys s => List.Forall₂ (fun x y => Q x y s) xs ys
  | [] => by
    rw [List.mapM_nil]
    exact (Sp.pure _).mono fun a _ e => by rw [e]; exact .nil
  | x :: xs => by
    rw [List.mapM_cons]
    refine (Sp.bind (hf x) (hs x) fun y => Sp.bind (sp_mapML f Q hf hs xs)
      (fun ys s s' h e => h.imp fun a b q => hs a b s s' q e) fun ys => Sp.pure (y :: ys)).mono ?_
    rintro b s ⟨y, q, ys, qs, rfl⟩
    exact .cons q qs

theorem sp_mapM {ι : Type} (f : ι → T α) (Q : ι → α → Placed → Prop) (hf : ∀ x, Sp (f x) (Q x))
    (hs : ∀ x a, Stable (Q x a)) (xs : Array ι) :
    Sp (xs.mapM f) fun ys s => List.Forall₂ (fun x y => Q x y s) xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  refine (Sp.bind (sp_mapML f Q hf hs xs.toList)
    (fun ys s s' h e => h.imp fun a b q => hs a b s s' q e) fun ys => Sp.pure ys.toArray).mono ?_
  rintro b s ⟨ys, qs, rfl⟩
  exact qs

/-! ### the whole placing -/

open VerifiableInference.Desc.First.Att.P (TablesP ScoreT LookIn Pts ScoreP)

def QAs (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Array E) (a : ℕ) (s : Placed) : Prop :=
  AsTabS s g a phi ∧ ∀ q < g.NAs, P.fits mats q (2 ^ g.lmS) (g.kAs / g.NAs) = true
def QRow (g : Geo) (mats : Array (ℕ × ℕ)) (psi : Array E) (a : ℕ) (s : Placed) : Prop :=
  Tab s a g.NAs g.T psi g.fillH ∧ P.fits mats g.NAs g.T g.fillH = true
def QLook (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Array E) (a : ℕ) (s : Placed) : Prop :=
  Tab s a (g.NAs + 2) (2 ^ g.lmb) phi g.kbA ∧ P.fits mats (g.NAs + 2) (2 ^ g.lmb) g.kbA = true
def QLong (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc tokv : Array E) (e a : ℕ) (s : Placed) : Prop :=
  ∃ c, P.cutLast zc g.ls = some c ∧ Tab s a mat (2 ^ g.la) (P.blockRows (P.eqTab c.2) tokv) e ∧
    P.fits mats mat (2 ^ g.la) e = true

theorem stable_QAs (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Array E) (a : ℕ) : Stable (QAs g mats phi a) :=
  (stable_as g a phi).and (stable_const _)
theorem stable_QRow (g : Geo) (mats : Array (ℕ × ℕ)) (psi : Array E) (a : ℕ) : Stable (QRow g mats psi a) :=
  (stable_tab _ _ _ _ _).and (stable_const _)
theorem stable_QLook (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Array E) (a : ℕ) : Stable (QLook g mats phi a) :=
  (stable_tab _ _ _ _ _).and (stable_const _)
theorem stable_QLong (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc tokv : Array E) (e a : ℕ) :
    Stable (QLong g mats mat zc tokv e a) := by
  rintro s s' ⟨c, hc, t, f⟩ x
  exact ⟨c, hc, t.ext x, f⟩
theorem stable_forall₂ {ι : Type} (Q : ι → α → Placed → Prop) (hs : ∀ x a, Stable (Q x a)) (xs : List ι)
    (ys : List α) : Stable fun s => List.Forall₂ (fun x y => Q x y s) xs ys :=
  fun s s' h e => h.imp fun a b q => hs a b s s' q e

/-- The last three steps: the state is read, one test, the record is made of it. -/
theorem sp_tail (b : Placed → Bool) (n : String) (F : Placed → TablesP) :
    Sp (P.T.placed >>= fun t => (monadLift (P.mustAs n (b t)) : T PUnit) >>= fun _ => Pure.pure (F t))
      fun r s => r = F s := by
  intro s r s' h
  obtain ⟨y, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  obtain ⟨x2, _⟩ := Sp.lift _ s y2.1 y2.2 e2
  cases hb : P.mustAs n (b s) with
  | none => rw [hb] at e2; cases e2
  | some u =>
    rw [hb] at e2
    have e2' : some (u, s) = some y2 := e2
    obtain rfl := Option.some.inj e2'
    have h' : some (F s, s) = some (r, s') := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨Ext.refl _, rfl⟩

/-- The numbers that must not be 0 for a table's stored length to stay readable under its first entry. -/
structure PosG (g : Geo) : Prop where
  nas : 0 < g.NAs
  was : 0 < g.kAs / g.NAs
  fillH : 0 < g.fillH
  gSo : 0 < g.fillO * g.T / 2 ^ g.la
  gSq : 0 < g.fillQ * g.T / 2 ^ g.la
  kbA : 0 < g.kbA

/-- The state that a record of tables holds. -/
def stOf (t : TablesP) (n : ℕ) : Placed := Placed.mk n t.tabLen t.funs

/-- **What tablesP lays where.** -/
structure TablesAre (g : Geo) (mats : Array (ℕ × ℕ)) (lk : LookIn) (p : Pts) (t : TablesP) (n : ℕ) : Prop where
  ptM : t.ptM = P.pointM g p.d
  ptD : t.ptD = P.pointD g p.d
  tA : QAs g mats (P.lastN lk.zx g.lmS) t.tA (stOf t n)
  tVM : QAs g mats (P.lastN (P.pointM g p.d) g.lmS) t.tVM (stOf t n)
  tVD : QAs g mats (P.lastN (P.pointD g p.d) g.lmS) t.tVD (stOf t n)
  hW : QRow g mats (P.eqTab p.d.ziW) t.hW (stOf t n)
  hX : QRow g mats (P.eqTab p.d.ziX) t.hX (stOf t n)
  hE : QRow g mats (P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))) t.hE (stOf t n)
  hT : QRow g mats (P.eqTab p.x.ti) t.hT (stOf t n)
  hPi : QRow g mats (P.eqTab (p.x.pi g)) t.hPi (stOf t n)
  hR2 : QRow g mats (P.eqTab (p.x.ri2 g)) t.hR2 (stOf t n)
  tO : QLong g mats (g.NAs + 1) p.d.zcW (P.eqTab p.d.ziW) (g.fillO * g.T / 2 ^ g.la) t.tO (stOf t n)
  qO : QLong g mats (g.NAs + 3) p.d.zcW (P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt)))
    (g.fillQ * g.T / 2 ^ g.la) t.qO (stOf t n)
  qVM : QLong g mats (g.NAs + 3) p.d.zcW (P.tok g p.d.wJv (P.lastCoords p.d.vpm.r g.lB))
    (g.fillQ * g.T / 2 ^ g.la) t.qVM (stOf t n)
  qVD : QLong g mats (g.NAs + 3) p.d.zcW
    (P.tok g (P.eqTab (p.d.vpd.r.extract g.lgk (g.lgk + g.lnT))) (P.lastCoords p.d.vpd.r g.lB))
    (g.fillQ * g.T / 2 ^ g.la) t.qVD (stOf t n)
  qF : QLong g mats (g.NAs + 3) (p.x.rc g) (P.eqTab (p.x.ri g)) (g.fillQ * g.T / 2 ^ g.la) t.qF (stOf t n)
  qKx : QLong g mats (g.NAs + 3) (p.x.rc g) (P.eqTab (p.x.pj g)) (g.fillQ * g.T / 2 ^ g.la) t.qKx (stOf t n)
  tBit0 : QLook g mats lk.phiB0 t.tBit0 (stOf t n)
  tBit1 : QLook g mats lk.phiB1 t.tBit1 (stOf t n)
  tPin : QLook g mats lk.phiP t.tPin (stOf t n)
  score : List.Forall₂ (fun (k : ScoreP) (y : ScoreT) =>
      QRow g mats (P.tok g k.wI k.zi) y.tM (stOf t n) ∧
      QLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi)
        (g.fillQ * g.T / 2 ^ g.la) y.tQ (stOf t n) ∧
      QLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj)
        (g.fillQ * g.T / 2 ^ g.la) y.tK (stOf t n)) p.scores.toList t.score.toList

theorem forall₂_zip {ι β γ : Type} {R : ι → β → Prop} {R' : ι → γ → Prop} :
    ∀ {xs : List ι} {ys : List β} {zs : List γ}, List.Forall₂ R xs ys → List.Forall₂ R' xs zs →
      List.Forall₂ (fun x (y : β × γ) => R x y.1 ∧ R' x y.2) xs (ys.zip zs)
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons a t, .cons b u => .cons ⟨a, b⟩ (forall₂_zip t u)

theorem sp_addAs' (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Unit → Array E) (hp : PosG g) :
    Sp (P.addAs g mats phi) (QAs g mats (phi ())) := sp_addAs g mats phi hp.nas hp.was
theorem sp_addRow' (g : Geo) (mats : Array (ℕ × ℕ)) (psi : Unit → Array E) (hp : PosG g) :
    Sp (P.addRow g mats psi) (QRow g mats (psi ())) := sp_addRow g mats psi hp.fillH
theorem sp_addLong' (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc : Array E) (ptk : Unit → Array E)
    (e : ℕ) (he : 0 < e) : Sp (P.addLong g mats mat zc ptk e) (QLong g mats mat zc (ptk ()) e) :=
  sp_addLong g mats mat zc ptk e he

theorem sp_placeAll (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) (hp : PosG g) :
    Sp (P.placeAll g mats nW lk p) fun t s => TablesAre g mats lk p t s.next := by
  unfold P.placeAll
  refine (Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind (sp_addAs' g mats _ hp) (stable_QAs g mats _) fun tA =>
    Sp.bind (sp_addAs' g mats _ hp) (stable_QAs g mats _) fun tVM =>
    Sp.bind (sp_addAs' g mats _ hp) (stable_QAs g mats _) fun tVD =>
    Sp.bind (sp_mapM _ (fun (k : ScoreP) => QRow g mats (P.tok g k.wI k.zi))
      (fun k => sp_addRow' g mats _ hp) (fun k => stable_QRow g mats _) p.scores)
      (fun ys => stable_forall₂ _ (fun k => stable_QRow g mats _) _ _) fun tM =>
    Sp.bind (sp_addRow' g mats _ hp) (stable_QRow g mats _) fun hW =>
    Sp.bind (sp_addRow' g mats _ hp) (stable_QRow g mats _) fun hX =>
    Sp.bind (sp_addRow' g mats _ hp) (stable_QRow g mats _) fun hE =>
    Sp.bind (sp_addRow' g mats _ hp) (stable_QRow g mats _) fun hT =>
    Sp.bind (sp_addRow' g mats _ hp) (stable_QRow g mats _) fun hPi =>
    Sp.bind (sp_addRow' g mats _ hp) (stable_QRow g mats _) fun hR2 =>
    Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSo) (stable_QLong g mats _ _ _ _) fun tO =>
    Sp.bind (sp_mapM _ (fun (k : ScoreP) (y : ℕ × ℕ) (s : Placed) =>
        QLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi)
          (g.fillQ * g.T / 2 ^ g.la) y.1 s ∧
        QLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj)
          (g.fillQ * g.T / 2 ^ g.la) y.2 s)
      (fun k => (Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun tQ =>
        Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun tK =>
        Sp.pure (tQ, tK)).mono (by rintro y s ⟨tQ, q1, tK, q2, rfl⟩; exact ⟨q1, q2⟩))
      (fun k y => (stable_QLong g mats _ _ _ _ _).and (stable_QLong g mats _ _ _ _ _)) p.scores)
      (fun ys => stable_forall₂ _
        (fun k y => (stable_QLong g mats _ _ _ _ _).and (stable_QLong g mats _ _ _ _ _)) _ _) fun tQK =>
    Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun qO =>
    Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun qVM =>
    Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun qVD =>
    Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun qF =>
    Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun qKx =>
    Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun phiB0 =>
    Sp.bind (Q := QLook g mats phiB0) (sp_add mats _ _ phiB0 _ hp.kbA) (stable_QLook g mats _) fun tBit0 =>
    Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun phiB1 =>
    Sp.bind (Q := QLook g mats phiB1) (sp_add mats _ _ phiB1 _ hp.kbA) (stable_QLook g mats _) fun tBit1 =>
    Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun phiP =>
    Sp.bind (Q := QLook g mats phiP) (sp_add mats _ _ phiP _ hp.kbA) (stable_QLook g mats _) fun tPin =>
    sp_tail _ _ _).mono ?_
  rintro t s ⟨_, _, tA, qA, tVM, qVM, tVD, qVD, tM, qM, hW, qhW, hX, qhX, hE, qhE, hT, qhT, hPi, qhPi,
    hR2, qhR2, _, _, tO, qtO, tQK, qQK, qO, qqO, qVM', qqVM, qVD', qqVD, qF, qqF, qKx, qqKx, _, _, _, rfl,
    tB0, qB0, _, rfl, tB1, qB1, _, rfl, tPn, qPn, rfl⟩
  refine ⟨rfl, rfl, qA, qVM, qVD, qhW, qhX, qhE, qhT, qhPi, qhR2, qtO, qqO, qqVM, qqVD, qqF, qqKx, qB0, qB1, qPn, ?_⟩
  show List.Forall₂ _ p.scores.toList ((tM.zip tQK).map _).toList
  rw [Array.toList_map, Array.toList_zip]
  have z := forall₂_zip qM qQK
  rw [List.forall₂_map_right_iff]
  exact z.imp fun k y q => ⟨q.1, q.2.1, q.2.2⟩

/-- **What tablesP lays where.** -/
theorem tables_are {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) (hp : PosG g) : ∃ n, TablesAre g mats lk p t n := by
  unfold P.tablesP at h
  have h' : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  cases hr : P.placeAll g mats nW lk p {} with
  | none => rw [hr] at h'; cases h'
  | some y =>
    rw [hr] at h'
    have e : y.1 = t := Option.some.inj h'
    subst e
    exact ⟨y.2.next, (sp_placeAll g mats nW lk p hp {} y.1 y.2 hr).2⟩

end K5Law
