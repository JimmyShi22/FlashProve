-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SameTabs.lean: kind K5: two placings of the tables at one geometry,
one list of matrices and equally many units lay every table at one first entry and store one list of
lengths, whatever the points and the weights are.

Main names:
  `TR R r r'`: of two routines of the placing (T, Johnson/Desc/First/Att/TablesP.lean): from one
    first free entry and one list of lengths, where both return: related values, one first free
    entry, one list of lengths. `TR.pure`, `TR.bind`, `TR.mono`, `TR.lift`; `tr_weights`,
    `tr_getAs`, `tr_add`, `tr_parts`, `tr_addAs`, `tr_addRow`, `tr_lng`, `tr_addLong`, `tr_mapML`,
    `tr_mapM`, `tr_placed`.
  `Starts t t'`: the 21 tables' first entries, those of the three tables on the lookup's matrix, and
    the stored lengths are one.
  `tr_placeAll`, `starts_one`: Starts at what placeAll and tablesP return, with the two points ptM
    and ptD as pointM and pointD of the division's record.
Limit: one-sided: both placings are taken to return.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.TablesSpec
import Johnson.Desc.First.Att.Claims.Same

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T TablesP ScoreT LookIn Pts ScoreP)

variable {α α' β β' : Type}

/-- Two placings: from one first free entry and one list of lengths, where both return: related values, one first free entry, one list of lengths. -/
def TR (R : α → α' → Prop) (r : T α) (r' : T α') : Prop :=
  ∀ s s' a t a' t', s.next = s'.next → s.tabLen = s'.tabLen → r s = some (a, t) → r' s' = some (a', t') →
    R a a' ∧ t.next = t'.next ∧ t.tabLen = t'.tabLen

theorem TR.pure {R : α → α' → Prop} {a : α} {a' : α'} (h : R a a') :
    TR R (Pure.pure a : T α) (Pure.pure a' : T α') := by
  intro s s' b t b' t' h1 h2 e e'
  have e1 : some (a, s) = some (b, t) := e
  have e2 : some (a', s') = some (b', t') := e'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e2)
  exact ⟨h, h1, h2⟩

theorem TR.bind {R : α → α' → Prop} {Q : β → β' → Prop} {r : T α} {r' : T α'} {k : α → T β} {k' : α' → T β'}
    (h1 : TR R r r') (h2 : ∀ a a', R a a' → TR Q (k a) (k' a')) : TR Q (r >>= k) (r' >>= k') := by
  intro s s' b t b' t' n1 n2 e e'
  obtain ⟨y, a1, a2⟩ := tbind_some e
  obtain ⟨y', b1, b2⟩ := tbind_some e'
  obtain ⟨q, m1, m2⟩ := h1 s s' y.1 y.2 y'.1 y'.2 n1 n2 a1 b1
  exact h2 _ _ q _ _ _ _ _ _ m1 m2 a2 b2

theorem TR.mono {R Q : α → α' → Prop} {r : T α} {r' : T α'} (h : TR R r r') (f : ∀ a a', R a a' → Q a a') :
    TR Q r r' := fun s s' a t a' t' n1 n2 e e' => by
  obtain ⟨q, m⟩ := h s s' a t a' t' n1 n2 e e'
  exact ⟨f _ _ q, m⟩

theorem TR.lift (x : Option α) (x' : Option α') : TR Any (monadLift x : T α) (monadLift x' : T α') := by
  intro s s' b t b' t' n1 n2 e e'
  cases x with
  | none => cases e
  | some a =>
    cases x' with
    | none => cases e'
    | some a' =>
      have e1 : some (a, s) = some (b, t) := e
      have e2 : some (a', s') = some (b', t') := e'
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj e2)
      exact ⟨trivial, n1, n2⟩

theorem tr_weights (n n' : ℕ) (f f' : Unit → Array E) : TR Any (P.T.weights n f) (P.T.weights n' f') :=
  TR.pure trivial

theorem tr_getAs (n n' : String) (x : Option α) (x' : Option α') : TR Any (P.T.getAs n x) (P.T.getAs n' x') := by
  cases x with
  | none => intro s s' b t b' t' _ _ e; cases e
  | some v =>
    cases x' with
    | none => intro s s' b t b' t' _ _ _ e'; cases e'
    | some v' => exact TR.pure trivial

theorem tr_add (mats : Array (ℕ × ℕ)) (mat mat' len len' : ℕ) (phi phi' : Array E) (e : ℕ) :
    TR Eq (P.add mats mat len phi e) (P.add mats mat' len' phi' e) := by
  intro s s' a t a' t' n1 n2 h h'
  obtain ⟨_, rfl, rfl⟩ := add_some h
  obtain ⟨_, rfl, rfl⟩ := add_some h'
  exact ⟨n1, by show s.next + e = s'.next + e; rw [n1],
    by show (s.next, e) :: s.tabLen = (s'.next, e) :: s'.tabLen; rw [n1, n2]⟩

theorem tr_parts (mats : Array (ℕ × ℕ)) (len : ℕ) (phi phi' : Array E) (w : ℕ) :
    ∀ qs : List ℕ, TR Any (qs.forM fun q => discard (P.add mats q len phi w))
      (qs.forM fun q => discard (P.add mats q len phi' w))
  | [] => TR.pure trivial
  | q0 :: qs => by
    intro s s' a t a' t' n1 n2 h h'
    have h0 : ((discard (P.add mats q0 len phi w) : T PUnit) >>= fun _ =>
      qs.forM fun q => discard (P.add mats q len phi w)) s = some (a, t) := h
    have h0' : ((discard (P.add mats q0 len phi' w) : T PUnit) >>= fun _ =>
      qs.forM fun q => discard (P.add mats q len phi' w)) s' = some (a', t') := h'
    obtain ⟨y, e1, e2⟩ := tbind_some h0
    obtain ⟨y', e1', e2'⟩ := tbind_some h0'
    obtain ⟨b, eb⟩ := discard_some (u := y.1) (s' := y.2) e1
    obtain ⟨b', eb'⟩ := discard_some (u := y'.1) (s' := y'.2) e1'
    obtain ⟨_, m1, m2⟩ := tr_add mats q0 q0 len len phi phi' w s s' b y.2 b' y'.2 n1 n2 eb eb'
    exact tr_parts mats len phi phi' w qs y.2 y'.2 a t a' t' m1 m2 e2 e2'

theorem tr_addAs (g : Geo) (mats : Array (ℕ × ℕ)) (phi phi' : Unit → Array E) :
    TR Eq (P.addAs g mats phi) (P.addAs g mats phi') := by
  intro s s' a t a' t' n1 n2 h h'
  unfold P.addAs P.T.weights P.T.placed P.T.total at h h'
  obtain ⟨y0, e0, h⟩ := tbind_some h
  have e0' : some (phi (), s) = some y0 := e0
  obtain rfl := Option.some.inj e0'
  obtain ⟨y1, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y1 := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  obtain ⟨y3, e3, h⟩ := tbind_some h
  have e3' : some (PUnit.unit, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some y3 := e3
  obtain rfl := Option.some.inj e3'
  have hh : some (s.next, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some (a, t) := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
  obtain ⟨z0, f0, h'⟩ := tbind_some h'
  have f0' : some (phi' (), s') = some z0 := f0
  obtain rfl := Option.some.inj f0'
  obtain ⟨z1, f1, h'⟩ := tbind_some h'
  have f1' : some (s', s') = some z1 := f1
  obtain rfl := Option.some.inj f1'
  obtain ⟨z2, f2, h'⟩ := tbind_some h'
  obtain ⟨z3, f3, h'⟩ := tbind_some h'
  have f3' : some (PUnit.unit, Placed.mk z2.2.next ((s'.next, z2.2.next - s'.next) :: z2.2.tabLen) z2.2.funs) =
      some z3 := f3
  obtain rfl := Option.some.inj f3'
  have hh' : some (s'.next, Placed.mk z2.2.next ((s'.next, z2.2.next - s'.next) :: z2.2.tabLen) z2.2.funs) =
      some (a', t') := h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh')
  obtain ⟨_, m1, m2⟩ := tr_parts mats _ _ _ _ _ s s' y2.1 y2.2 z2.1 z2.2 n1 n2 e2 f2
  exact ⟨n1, m1, by
    show (s.next, y2.2.next - s.next) :: y2.2.tabLen = (s'.next, z2.2.next - s'.next) :: z2.2.tabLen
    rw [n1, m1, m2]⟩

theorem tr_addRow (g : Geo) (mats : Array (ℕ × ℕ)) (psi psi' : Unit → Array E) :
    TR Eq (P.addRow g mats psi) (P.addRow g mats psi') := by
  unfold P.addRow
  exact TR.bind (tr_weights _ _ _ _) fun _ _ _ => tr_add mats _ _ _ _ _ _ _

theorem tr_lng (g : Geo) (zc zc' : Array E) (ptk ptk' : Unit → Array E) :
    TR Any (P.lng g zc ptk) (P.lng g zc' ptk') := by
  unfold P.lng
  exact TR.bind (tr_weights _ _ _ _) fun _ _ _ => TR.bind (TR.lift _ _) fun _ _ _ =>
    TR.bind (tr_getAs _ _ _ _) fun _ _ _ => tr_weights _ _ _ _

theorem tr_addLong (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc zc' : Array E) (ptk ptk' : Unit → Array E)
    (e : ℕ) : TR Eq (P.addLong g mats mat zc ptk e) (P.addLong g mats mat zc' ptk' e) := by
  unfold P.addLong
  exact TR.bind (tr_lng g zc zc' ptk ptk') fun _ _ _ => tr_add mats _ _ _ _ _ _ _

theorem tr_mapML {ι ι' : Type} (f : ι → T α) (f' : ι' → T α) (hf : ∀ x x', TR Eq (f x) (f' x')) :
    ∀ (xs : List ι) (xs' : List ι'), xs.length = xs'.length → TR Eq (xs.mapM f) (xs'.mapM f')
  | [], [], _ => by
    rw [List.mapM_nil, List.mapM_nil]
    exact TR.pure rfl
  | x :: xs, x' :: xs', hl => by
    rw [List.mapM_cons, List.mapM_cons]
    refine TR.bind (hf x x') fun y y' ey => TR.bind (tr_mapML f f' hf xs xs' (by simpa using hl))
      fun ys ys' eys => TR.pure (by rw [ey, eys])
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

theorem tr_mapM {ι ι' : Type} (f : ι → T α) (f' : ι' → T α) (hf : ∀ x x', TR Eq (f x) (f' x'))
    (xs : Array ι) (xs' : Array ι') (hl : xs.size = xs'.size) : TR Eq (xs.mapM f) (xs'.mapM f') := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, map_eq_pure_bind, map_eq_pure_bind]
  exact TR.bind (tr_mapML f f' hf xs.toList xs'.toList (by simpa using hl)) fun ys ys' e =>
    TR.pure (by rw [e])

theorem tr_placed : TR (fun a a' : Placed => a.next = a'.next ∧ a.tabLen = a'.tabLen) P.T.placed P.T.placed := by
  intro s s' a t a' t' n1 n2 e e'
  have e1 : some (s, s) = some (a, t) := e
  have e2 : some (s', s') = some (a', t') := e'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e2)
  exact ⟨⟨n1, n2⟩, n1, n2⟩

/-- The tables' first entries and the stored lengths are one. -/
structure Starts (t t' : TablesP) : Prop where
  tA : t.tA = t'.tA
  tVM : t.tVM = t'.tVM
  tVD : t.tVD = t'.tVD
  score : t.score = t'.score
  hW : t.hW = t'.hW
  hX : t.hX = t'.hX
  hE : t.hE = t'.hE
  hT : t.hT = t'.hT
  hPi : t.hPi = t'.hPi
  hR2 : t.hR2 = t'.hR2
  tO : t.tO = t'.tO
  qO : t.qO = t'.qO
  qVM : t.qVM = t'.qVM
  qVD : t.qVD = t'.qVD
  qF : t.qF = t'.qF
  qKx : t.qKx = t'.qKx
  tBit0 : t.tBit0 = t'.tBit0
  tBit1 : t.tBit1 = t'.tBit1
  tPin : t.tPin = t'.tPin
  tabLen : t.tabLen = t'.tabLen

/-- **Two placings at one geometry, one list of matrices and equally many units lay every table at one first entry**, whatever the points and the weights are. -/
theorem tr_placeAll (g : Geo) (mats : Array (ℕ × ℕ)) (nW nW' : ℕ) (lk lk' : LookIn) (p p' : Pts)
    (hs : p.scores.size = p'.scores.size) :
    TR (fun t t' => Starts t t' ∧ (t.ptM = P.pointM g p.d ∧ t.ptD = P.pointD g p.d) ∧
        t'.ptM = P.pointM g p'.d ∧ t'.ptD = P.pointD g p'.d)
      (P.placeAll g mats nW lk p) (P.placeAll g mats nW' lk' p') := by
  unfold P.placeAll
  exact TR.bind (TR.lift _ _) fun _ _ _ =>
    TR.bind (tr_addAs g mats _ _) fun tA tA' e_tA =>
    TR.bind (tr_addAs g mats _ _) fun tVM tVM' e_tVM =>
    TR.bind (tr_addAs g mats _ _) fun tVD tVD' e_tVD =>
    TR.bind (tr_mapM _ _ (fun _ _ => tr_addRow g mats _ _) p.scores p'.scores hs) fun tM tM' e_tM =>
    TR.bind (tr_addRow g mats _ _) fun hW hW' e_hW =>
    TR.bind (tr_addRow g mats _ _) fun hX hX' e_hX =>
    TR.bind (tr_addRow g mats _ _) fun hE hE' e_hE =>
    TR.bind (tr_addRow g mats _ _) fun hT hT' e_hT =>
    TR.bind (tr_addRow g mats _ _) fun hPi hPi' e_hPi =>
    TR.bind (tr_addRow g mats _ _) fun hR2 hR2' e_hR2 =>
    TR.bind (TR.lift _ _) fun _ _ _ =>
    TR.bind (tr_addLong g mats _ _ _ _ _ _) fun tO tO' e_tO =>
    TR.bind (tr_mapM _ _ (fun _ _ => TR.bind (tr_addLong g mats _ _ _ _ _ _) fun a a' ea =>
      TR.bind (tr_addLong g mats _ _ _ _ _ _) fun b b' eb => TR.pure (by rw [ea, eb])) p.scores p'.scores hs) fun tQK tQK' e_tQK =>
    TR.bind (tr_addLong g mats _ _ _ _ _ _) fun qO qO' e_qO =>
    TR.bind (tr_addLong g mats _ _ _ _ _ _) fun qVM qVM' e_qVM =>
    TR.bind (tr_addLong g mats _ _ _ _ _ _) fun qVD qVD' e_qVD =>
    TR.bind (tr_addLong g mats _ _ _ _ _ _) fun qF qF' e_qF =>
    TR.bind (tr_addLong g mats _ _ _ _ _ _) fun qKx qKx' e_qKx =>
    TR.bind (TR.lift _ _) fun _ _ _ =>
    TR.bind (tr_weights _ _ _ _) fun _ _ _ =>
    TR.bind (tr_add mats _ _ _ _ _ _ _) fun tBit0 tBit0' e_tBit0 =>
    TR.bind (tr_weights _ _ _ _) fun _ _ _ =>
    TR.bind (tr_add mats _ _ _ _ _ _ _) fun tBit1 tBit1' e_tBit1 =>
    TR.bind (tr_weights _ _ _ _) fun _ _ _ =>
    TR.bind (tr_add mats _ _ _ _ _ _ _) fun tPin tPin' e_tPin =>
    TR.bind tr_placed fun t t' et =>
    TR.bind (TR.lift _ _) fun _ _ _ =>
    TR.pure ⟨⟨e_tA, e_tVM, e_tVD, by show Array.map _ (tM.zip tQK) = Array.map _ (tM'.zip tQK'); rw [e_tM, e_tQK],
      e_hW, e_hX, e_hE, e_hT, e_hPi, e_hR2, e_tO, e_qO, e_qVM, e_qVD, e_qF, e_qKx, e_tBit0, e_tBit1, e_tPin, et.2⟩,
      ⟨rfl, rfl⟩, rfl, rfl⟩

/-- The same of tablesP. -/
theorem starts_one {g : Geo} {mats : Array (ℕ × ℕ)} {nW nW' : ℕ} {lk lk' : LookIn} {p p' : Pts} {t t' : TablesP}
    (hs : p.scores.size = p'.scores.size) (h : P.tablesP g mats nW lk p = some t)
    (h' : P.tablesP g mats nW' lk' p' = some t') :
    Starts t t' ∧ (t.ptM = P.pointM g p.d ∧ t.ptD = P.pointD g p.d) ∧
      t'.ptM = P.pointM g p'.d ∧ t'.ptD = P.pointD g p'.d := by
  unfold P.tablesP at h h'
  have a : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  have a' : (P.placeAll g mats nW' lk' p' {}).bind (fun y => some y.1) = some t' := h'
  cases hr : P.placeAll g mats nW lk p {} with
  | none => rw [hr] at a; cases a
  | some y =>
    cases hr' : P.placeAll g mats nW' lk' p' {} with
    | none => rw [hr'] at a'; cases a'
    | some y' =>
      rw [hr] at a
      rw [hr'] at a'
      have e : y.1 = t := Option.some.inj a
      have e' : y'.1 = t' := Option.some.inj a'
      rw [← e, ← e']
      exact (tr_placeAll g mats nW nW' lk lk' p p' hs {} {} y.1 y.2 y'.1 y'.2 rfl rfl hr hr').1

end K5Law
