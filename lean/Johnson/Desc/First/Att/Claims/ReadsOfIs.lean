-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsOfIs.lean: kind K5: the list of tables that tablesP
(Johnson/Desc/First/Att/TablesP.lean) hands to the smallness test IS the list of the declaration's
tables (readsOfK5, Johnson/Desc/First/Att/ReadsOf.lean), in order: an equation, so nothing else
lies in it.

Main names:
  `tablesP_is`: tablesP g mats nW lk p = some t → fit g lk p = true →
    t.funs = ((readsOfK5 g lk p).flatMap tablesOf).toArray.
  `tablesP_lays`: from the return alone, without fit: the same equation with the weights as the
    arrays that the text makes (tablesA); under each field of t stands the declared first entry;
    the declared numbers of entries add up to nW, the length of the segment's vector of reads.
  `tablesP_firsts`: r.first t = (r.decl g lk p).start at every read of the list.
  `starts_running`: the declared first entries are the running sums, from 0 on, of the declared
    numbers of entries (Running). It speaks of the declaration alone.
  `w_beyond`: under fit a declared weight is 0 from the run's length on.
  `w_long`: the order of a long table's weights: number a T + i is feature a of the block at
    position i.
  `cells_short`, `cells_long`, `cells_part`, `cells_column`: what ReadDecl.cells (Reads/Decl.lean)
    gives at the four makes: column i / (m / len) and row i % (m / len) len + j, as tab_read and
    as_read (Johnson/Road/Rows/AttReadLaws.lean) have them. At the make column: as written there,
    for every m; it is tab_read's cell only where m = len.
Tools: Table, layFrom, total; LQ n r Q L: from the first free entry n the routine r of the placing
  lays just the tables L and returns something with Q; its rules; FQ; laidBy, the list in the
  text's own order; lq_placeAll; Running with running_map, running_pairs, lay_flat; tabs, tablesA.
Premises. (1) The return of tablesP. It refuses at seven places (TablesP.lean's head). (2) fit: a
Boolean on lengths alone. tablesP tests it at the long tables and at no other; where it fails and
tablesP returns, the list holds an array that is shorter or longer than its run, and the equation
of tablesP_is fails while that of tablesP_lays stands.
Are the premises met? Not shown in this file. Claims/ReadsReturn.lean: the return is one Boolean
(placeOk), and fit is there a test at ten reads.
Not claimed: that a table is true of a matrix; that the smallness test takes this list; that a form
of the claims names the entry that its clause means; what the lookup's three arrays are.
Used of Johnson/Road: blockRows_getD (FormsKeysPoint.lean), a lemma on a pure function of
OnBytes/Model/Tensors.lean whose text is blockRows' of Att/Geo.lean. Of OnBytes and Johnson/Road no
routine that runs in a context is named, and no theorem on such a routine's return.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.ReadsOf
import Johnson.Desc.First.Att.Claims.TablesSpec
import Johnson.Desc.First.Att.Claims.Same
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Reads (Make ReadDecl)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T TablesP ScoreT LookIn Pts ScoreP Read Matrix Weights)

variable {α β : Type}

/-- A table without its first entry: the matrix's number, the cells in a run, one weight a cell, the number of entries. -/
structure Table where
  mat : ℕ
  len : ℕ
  phi : Array E
  entries : ℕ

/-- Tables laid one behind the other in vector number 2, from entry first on. -/
def layFrom : ℕ → List Table → List Fun1
  | _, [] => []
  | first, t :: l => ⟨t.mat, t.len, t.phi, 2, first⟩ :: layFrom (first + t.entries) l

/-- How many entries a list of tables has. -/
def total (L : List Table) : ℕ := (L.map (·.entries)).sum

theorem total_nil : total [] = 0 := rfl

theorem total_cons (t : Table) (L : List Table) : total (t :: L) = t.entries + total L := by
  unfold total
  rw [List.map_cons, List.sum_cons]

theorem total_append (L L' : List Table) : total (L ++ L') = total L + total L' := by
  unfold total
  rw [List.map_append, List.sum_append]

theorem total_parts (F : ℕ → ℕ) (len : ℕ) (phi : Array E) (w : ℕ) (qs : List ℕ) :
    total (qs.map fun q => (⟨F q, len, phi, w⟩ : Table)) = qs.length * w := by
  induction qs with
  | nil => simp [total]
  | cons q qs ih => rw [List.map_cons, total_cons, ih, List.length_cons]; ring

theorem total_flat {ι : Type} (Lx : ι → List Table) (c : ℕ) (hc : ∀ x, total (Lx x) = c) (xs : List ι) :
    total (xs.flatMap Lx) = xs.length * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => rw [List.flatMap_cons, total_append, hc, ih, List.length_cons]; ring

theorem layFrom_append : ∀ (L L' : List Table) (n : ℕ),
    layFrom n (L ++ L') = layFrom n L ++ layFrom (n + total L) L'
  | [], L', n => by simp [layFrom, total]
  | t :: L, L', n => by
    show _ :: layFrom (n + t.entries) (L ++ L') = _ :: (layFrom (n + t.entries) L ++ _)
    rw [layFrom_append L L' (n + t.entries), total_cons, Nat.add_assoc]

/-- From the first free entry n a routine of the placing lays just the tables L behind those that lie; Q: what it returns. -/
def LQ (n : ℕ) (r : T α) (Q : α → Prop) (L : List Table) : Prop :=
  ∀ s a s', s.next = n → r s = some (a, s') →
    Q a ∧ s'.funs.toList = s.funs.toList ++ layFrom n L ∧ s'.next = n + total L

theorem LQ.pure (n : ℕ) (a : α) : LQ n (Pure.pure a : T α) (fun b => b = a) [] := by
  intro s b s' hn h
  have h' : some (a, s) = some (b, s') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  exact ⟨rfl, by simp [layFrom], by simp [total, hn]⟩

theorem LQ.bind {n : ℕ} {r : T α} {k : α → T β} {Q : α → Prop} {R : β → Prop} {L L' : List Table}
    (h1 : LQ n r Q L) (h2 : ∀ a, Q a → LQ (n + total L) (k a) R L') : LQ n (r >>= k) R (L ++ L') := by
  intro s b s' hn h
  obtain ⟨y, e1, e2⟩ := tbind_some h
  obtain ⟨q, f1, n1⟩ := h1 s y.1 y.2 hn e1
  obtain ⟨r', f2, n2⟩ := h2 y.1 q y.2 b s' n1 e2
  refine ⟨r', ?_, ?_⟩
  · rw [f2, f1, layFrom_append, List.append_assoc]
  · rw [n2, total_append, Nat.add_assoc]

/-- The same where the first routine lays nothing. -/
theorem LQ.bind0 {n : ℕ} {r : T α} {k : α → T β} {Q : α → Prop} {R : β → Prop} {L' : List Table}
    (h1 : LQ n r Q []) (h2 : ∀ a, Q a → LQ n (k a) R L') : LQ n (r >>= k) R L' :=
  LQ.bind (L := []) h1 h2

theorem LQ.mono {n : ℕ} {r : T α} {Q Q' : α → Prop} {L : List Table} (h : LQ n r Q L) (f : ∀ a, Q a → Q' a) :
    LQ n r Q' L :=
  fun s a s' hn e => by
    obtain ⟨q, m⟩ := h s a s' hn e
    exact ⟨f a q, m⟩

theorem LQ.lift (n : ℕ) (x : Option α) : LQ n (monadLift x : T α) (fun _ => True) [] := by
  intro s b s' hn h
  cases x with
  | none => cases h
  | some a =>
    have h' : some (a, s) = some (b, s') := h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨trivial, by simp [layFrom], by simp [total, hn]⟩

theorem lq_weights (n m : ℕ) (f : Unit → Array E) : LQ n (P.T.weights m f) (fun a => a = f ()) [] := LQ.pure _ _

theorem lq_getAs (n : ℕ) (nm : String) (x : Option α) : LQ n (P.T.getAs nm x) (fun a => x = some a) [] := by
  cases x with
  | none => intro s a s' _ h; cases h
  | some v => exact (LQ.pure n v).mono fun a e => by rw [e]

/-- add returns the first free entry. -/
theorem lq_add (n : ℕ) (mats : Array (ℕ × ℕ)) (mat len : ℕ) (phi : Array E) (e : ℕ) :
    LQ n (P.add mats mat len phi e) (fun a => a = n) [⟨mat, len, phi, e⟩] := by
  intro s a s' hn h
  obtain ⟨_, rfl, rfl⟩ := add_some h
  exact ⟨hn, by simp [layFrom, hn], by simp [total, hn]⟩

theorem lq_parts (mats : Array (ℕ × ℕ)) (len : ℕ) (phi : Array E) (w : ℕ) :
    ∀ (qs : List ℕ) (n : ℕ), LQ n (qs.forM fun q => discard (P.add mats q len phi w)) (fun _ => True)
      (qs.map fun q => ⟨q, len, phi, w⟩)
  | [], n => (LQ.pure n PUnit.unit).mono fun _ _ => trivial
  | q0 :: qs, n => by
    intro s a s' hn h
    have h0 : ((discard (P.add mats q0 len phi w) : T PUnit) >>= fun _ =>
      qs.forM fun q => discard (P.add mats q len phi w)) s = some (a, s') := h
    obtain ⟨y, e1, e2⟩ := tbind_some h0
    obtain ⟨b, eb⟩ := discard_some (u := y.1) (s' := y.2) e1
    obtain ⟨_, f1, n1⟩ := lq_add n mats q0 len phi w s b y.2 hn eb
    obtain ⟨_, f2, n2⟩ := lq_parts mats len phi w qs _ y.2 a s' n1 e2
    refine ⟨trivial, ?_, ?_⟩
    · rw [f2, f1, List.map_cons, show (⟨q0, len, phi, w⟩ : Table) :: qs.map (fun q => (⟨q, len, phi, w⟩ : Table)) =
        [⟨q0, len, phi, w⟩] ++ qs.map (fun q => (⟨q, len, phi, w⟩ : Table)) from rfl, layFrom_append,
        List.append_assoc]
    · rw [n2, List.map_cons, show (⟨q0, len, phi, w⟩ : Table) :: qs.map (fun q => (⟨q, len, phi, w⟩ : Table)) =
        [⟨q0, len, phi, w⟩] ++ qs.map (fun q => (⟨q, len, phi, w⟩ : Table)) from rfl, total_append, Nat.add_assoc]

theorem lq_addAs (n : ℕ) (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Unit → Array E) :
    LQ n (P.addAs g mats phi) (fun a => a = n)
      ((List.range g.NAs).map fun q => ⟨q, 2 ^ g.lmS, phi (), g.kAs / g.NAs⟩) := by
  intro s a s'' hn h
  unfold P.addAs P.T.weights P.T.placed P.T.total at h
  obtain ⟨y0, e0, h⟩ := tbind_some h
  have e0' : some (phi (), s) = some y0 := e0
  obtain rfl := Option.some.inj e0'
  obtain ⟨y1, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y1 := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  obtain ⟨_, f2, n2⟩ := lq_parts mats _ _ _ _ n s y2.1 y2.2 hn e2
  obtain ⟨y3, e3, h⟩ := tbind_some h
  have e3' : some (PUnit.unit, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some y3 := e3
  obtain rfl := Option.some.inj e3'
  have h' : some (s.next, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some (a, s'') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  exact ⟨hn, f2, n2⟩

theorem lq_addRow (n : ℕ) (g : Geo) (mats : Array (ℕ × ℕ)) (psi : Unit → Array E) :
    LQ n (P.addRow g mats psi) (fun a => a = n) [⟨g.NAs, g.T, psi (), g.fillH⟩] := by
  unfold P.addRow
  exact LQ.bind0 (lq_weights _ _ _) fun w e => by rw [e]; exact lq_add n mats _ _ _ _

/-- lng lays nothing; where it returns, its weights on the positions are T, and a long run has 2^ls T cells, and zc has ls coordinates at least. -/
theorem lq_lng (n : ℕ) (g : Geo) (zc : Array E) (ptk : Unit → Array E) :
    LQ n (P.lng g zc ptk) (fun a => a = P.blockRows (P.eqTab (P.lastCoords zc g.ls)) (ptk ())) [] := by
  unfold P.lng
  refine LQ.bind0 (lq_weights _ _ _) fun w ew =>
    LQ.bind0 (LQ.lift _ _) fun _ _ =>
    LQ.bind0 (lq_getAs _ _ _) fun c hc => (lq_weights _ _ _).mono fun a ea => ?_
  have ec : c.2 = P.lastCoords zc g.ls := by
    unfold P.cutLast at hc
    split at hc
    · cases hc
    · rw [← Option.some.inj hc]
      rfl
  rw [ea, ec, ew]

theorem lq_addLong (n : ℕ) (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc : Array E) (ptk : Unit → Array E) (e : ℕ) :
    LQ n (P.addLong g mats mat zc ptk e) (fun a => a = n)
      [⟨mat, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords zc g.ls)) (ptk ()), e⟩] := by
  unfold P.addLong
  exact LQ.bind0 (lq_lng n g zc ptk) fun w ew => by rw [ew]; exact lq_add n mats _ _ _ _

/-- A routine run over a list, each run laying c entries and returning V of its first free entry. -/
theorem lq_mapML {ι : Type} (f : ι → T α) (Lx : ι → List Table) (c : ℕ) (hc : ∀ x, total (Lx x) = c) (V : ℕ → α)
    (hf : ∀ m x, LQ m (f x) (fun a => a = V m) (Lx x)) :
    ∀ (xs : List ι) (n : ℕ), LQ n (xs.mapM f)
      (fun ys => ys = (List.range xs.length).map fun u => V (n + u * c)) (xs.flatMap Lx)
  | [], n => by
    rw [List.mapM_nil]
    exact (LQ.pure _ _).mono fun _ e => by rw [e]; rfl
  | x :: xs, n => by
    rw [List.mapM_cons, List.flatMap_cons]
    have h := LQ.bind (hf n x) fun y hy => LQ.bind (lq_mapML f Lx c hc V hf xs (n + total (Lx x))) fun ys hys =>
      (LQ.pure _ (y :: ys)).mono (Q' := fun zs => zs = (List.range (x :: xs).length).map fun u => V (n + u * c))
        fun zs e => by
          rw [e, hy, hys, hc, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
          refine congrArg₂ _ (by simp) (List.map_congr_left fun u _ => ?_)
          show V (n + c + u * c) = V (n + (u + 1) * c)
          congr 1
          ring
    rwa [List.append_nil] at h

theorem lq_mapM {ι : Type} (f : ι → T α) (Lx : ι → List Table) (c : ℕ) (hc : ∀ x, total (Lx x) = c) (V : ℕ → α)
    (hf : ∀ m x, LQ m (f x) (fun a => a = V m) (Lx x)) (xs : Array ι) (n : ℕ) :
    LQ n (xs.mapM f) (fun ys => ys.toList = (List.range xs.size).map fun u => V (n + u * c))
      (xs.toList.flatMap Lx) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  have h := LQ.bind (lq_mapML f Lx c hc V hf xs.toList n) fun ys hys =>
    (LQ.pure _ ys.toArray).mono (Q' := fun zs : Array α => zs.toList = (List.range xs.size).map fun u => V (n + u * c))
      fun zs e => by rw [e, hys]; simp
  rwa [List.append_nil] at h

/-- The last three steps lay nothing; the record is made of the state. -/
theorem lq_tail (n : ℕ) (b : Placed → Bool) (nm : String) (F : Placed → TablesP) :
    ∀ s a s', s.next = n →
      (P.T.placed >>= fun t => (monadLift (P.mustAs nm (b t)) : T PUnit) >>= fun _ => Pure.pure (F t)) s =
        some (a, s') → a = F s ∧ s' = s ∧ b s = true := by
  intro s a s' _ h
  obtain ⟨y, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  cases hb : b s with
  | false =>
    have e2' : (monadLift (P.mustAs nm (b s)) : T PUnit) s = some y2 := e2
    rw [hb] at e2'
    cases e2'
  | true =>
    have e2' : (monadLift (P.mustAs nm (b s)) : T PUnit) s = some y2 := e2
    rw [hb] at e2'
    have e2'' : some (PUnit.unit, s) = some y2 := e2'
    obtain rfl := Option.some.inj e2''
    have h' : some (F s, s) = some (a, s') := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨rfl, rfl, rfl⟩

theorem lq_tailT (n nW : ℕ) (nm : String) (F : Placed → TablesP) :
    LQ n (P.T.placed >>= fun t => (monadLift (P.mustAs nm (t.next == nW)) : T PUnit) >>= fun _ => Pure.pure (F t))
      (fun a => (∃ s, a = F s) ∧ n = nW) [] := by
  intro s a s' hn h
  obtain ⟨e, rfl, hb⟩ := lq_tail n (fun t => t.next == nW) nm F s a s' hn h
  exact ⟨⟨⟨s', e⟩, by rw [← hn]; exact beq_iff_eq.1 hb⟩, by simp [layFrom], by simp [total, hn]⟩

/-- The record that a placing returns holds the list of tables that lies. -/
def FQ (r : T TablesP) : Prop := ∀ s a s', r s = some (a, s') → a.funs = s'.funs

theorem fq_bind {r : T α} {k : α → T TablesP} (h : ∀ a, FQ (k a)) : FQ (r >>= k) := by
  intro s b s' e
  obtain ⟨y, _, e2⟩ := tbind_some e
  exact h y.1 y.2 b s' e2

theorem fq_placeAll (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) :
    FQ (P.placeAll g mats nW lk p) := by
  unfold P.placeAll
  iterate 26 (refine fq_bind fun _ => ?_)
  intro s a s' h
  obtain ⟨e, rfl, _⟩ := lq_tail s.next _ _ _ s a s' rfl h
  rw [e]

/-- The tables of the placing, as its text lays them one behind the other. -/
def laidBy (g : Geo) (lk : LookIn) (p : Pts) : List Table :=
  ((List.range g.NAs).map fun q => (⟨q, 2 ^ g.lmS, P.lastN lk.zx g.lmS, g.kAs / g.NAs⟩ : Table)) ++
  (((List.range g.NAs).map fun q => (⟨q, 2 ^ g.lmS, P.lastN (P.pointM g p.d) g.lmS, g.kAs / g.NAs⟩ : Table)) ++
  (((List.range g.NAs).map fun q => (⟨q, 2 ^ g.lmS, P.lastN (P.pointD g p.d) g.lmS, g.kAs / g.NAs⟩ : Table)) ++
  ((p.scores.toList.flatMap fun k : ScoreP => [(⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩ : Table)]) ++
  ([⟨g.NAs, g.T, P.eqTab p.d.ziW, g.fillH⟩] ++
  ([⟨g.NAs, g.T, P.eqTab p.d.ziX, g.fillH⟩] ++
  ([⟨g.NAs, g.T, P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt)), g.fillH⟩] ++
  ([⟨g.NAs, g.T, P.eqTab p.x.ti, g.fillH⟩] ++
  ([⟨g.NAs, g.T, P.eqTab (p.x.pi g), g.fillH⟩] ++
  ([⟨g.NAs, g.T, P.eqTab (p.x.ri2 g), g.fillH⟩] ++
  ([⟨g.NAs + 1, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords p.d.zcW g.ls)) (P.eqTab p.d.ziW), g.fillO * g.T / 2 ^ g.la⟩] ++
  ((p.scores.toList.flatMap fun k : ScoreP =>
      [(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
          (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
      ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
          (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ [])) ++
  ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords p.d.zcW g.ls))
      (P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))), g.fillQ * g.T / 2 ^ g.la⟩] ++
  ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords p.d.zcW g.ls))
      (P.tok g p.d.wJv (P.lastCoords p.d.vpm.r g.lB)), g.fillQ * g.T / 2 ^ g.la⟩] ++
  ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords p.d.zcW g.ls))
      (P.tok g (P.eqTab (p.d.vpd.r.extract g.lgk (g.lgk + g.lnT))) (P.lastCoords p.d.vpd.r g.lB)),
      g.fillQ * g.T / 2 ^ g.la⟩] ++
  ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (p.x.rc g) g.ls)) (P.eqTab (p.x.ri g)),
      g.fillQ * g.T / 2 ^ g.la⟩] ++
  ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (p.x.rc g) g.ls)) (P.eqTab (p.x.pj g)),
      g.fillQ * g.T / 2 ^ g.la⟩] ++
  ([⟨g.NAs + 2, 2 ^ g.lmb, lk.phiB0, g.kbA⟩] ++
  ([⟨g.NAs + 2, 2 ^ g.lmb, lk.phiB1, g.kbA⟩] ++
  ([⟨g.NAs + 2, 2 ^ g.lmb, lk.phiP, g.kbA⟩] ++
  [])))))))))))))))))))

/-- A unit's two tables on qkv. -/
theorem lq_pair (m : ℕ) (g : Geo) (mats : Array (ℕ × ℕ)) (k : ScoreP) :
    LQ m (P.addLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (fun _ => P.tok g (P.scoreTiles g k).1 k.zi)
          (g.fillQ * g.T / 2 ^ g.la) >>= fun tQ =>
        P.addLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (fun _ => P.tok g (P.scoreTiles g k).2 k.zj)
          (g.fillQ * g.T / 2 ^ g.la) >>= fun tK => (Pure.pure (tQ, tK) : T (ℕ × ℕ)))
      (fun a => a = (m, m + g.fillQ * g.T / 2 ^ g.la))
      ([(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ [])) :=
  LQ.bind (lq_addLong m g mats _ _ _ _) fun tQ hQ => LQ.bind (lq_addLong _ g mats _ _ _ _) fun tK hK =>
    (LQ.pure _ (tQ, tK)).mono fun a e => by
      rw [e, hQ, hK]
      simp [total]

/-- Member u of the units' three first entries. -/
theorem score_get (tM : Array ℕ) (tQK : Array (ℕ × ℕ)) (n : ℕ) (f : ℕ → ℕ) (f2 : ℕ → ℕ × ℕ)
    (h1 : tM.toList = (List.range n).map f) (h2 : tQK.toList = (List.range n).map f2) (u : ℕ) (hu : u < n) :
    ((tM.zip tQK).map fun y => (⟨y.1, y.2.1, y.2.2⟩ : ScoreT)).getD u ⟨0, 0, 0⟩ = ⟨f u, (f2 u).1, (f2 u).2⟩ := by
  have e : ((tM.zip tQK).map fun y => (⟨y.1, y.2.1, y.2.2⟩ : ScoreT)).toList =
      (List.range n).map fun u => (⟨f u, (f2 u).1, (f2 u).2⟩ : ScoreT) := by
    rw [Array.toList_map, Array.toList_zip, h1, h2, List.zip_map', List.map_map]
    rfl
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e, List.getElem?_map, List.getElem?_range hu]
  rfl

theorem total_one (mat len : ℕ) (phi : Array E) (e : ℕ) : total [⟨mat, len, phi, e⟩] = e := by simp [total]

theorem total_range (N len : ℕ) (phi : Array E) (w : ℕ) :
    total ((List.range N).map fun q => (⟨q, len, phi, w⟩ : Table)) = N * w := by
  rw [total_parts (fun q => q), List.length_range]

/-- bind, with the number of entries that the first routine lays told. -/
theorem LQ.bindc {n c : ℕ} {r : T α} {k : α → T β} {Q : α → Prop} {R : β → Prop} {L L' : List Table}
    (h1 : LQ n r Q L) (hc : total L = c) (h2 : ∀ a, Q a → LQ (n + c) (k a) R L') : LQ n (r >>= k) R (L ++ L') := by
  subst hc
  exact LQ.bind h1 h2

/-- **What the placing lays and returns**, from entry 0 on: the tables of laidBy; under each field the declared first entry; and the declared numbers of entries add up to nW. -/
theorem lq_placeAll (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) :
    LQ 0 (P.placeAll g mats nW lk p)
      (fun t => (∀ r ∈ P.reads p.scores.size, r.first t = r.start g p.scores.size) ∧
        3 * g.nScores + (p.scores.size + 6) * g.nRows + g.nOut + (2 * p.scores.size + 5) * g.nQkv +
          3 * g.nPlanes = nW)
      (laidBy g lk p) := by
  unfold P.placeAll laidBy
  refine
    LQ.bind0 (LQ.lift _ _) fun _ _ =>
    LQ.bindc (lq_addAs _ g mats _) (total_range _ _ _ _) fun tA hA =>
    LQ.bindc (lq_addAs _ g mats _) (total_range _ _ _ _) fun tVM hVM =>
    LQ.bindc (lq_addAs _ g mats _) (total_range _ _ _ _) fun tVD hVD =>
    LQ.bindc (lq_mapM _ (fun k : ScoreP => [⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩]) g.fillH
      (fun _ => total_one _ _ _ _) (fun m => m) (fun m k => lq_addRow m g mats _) p.scores _)
      (total_flat _ g.fillH (fun _ => total_one _ _ _ _) _) fun tM hM =>
    LQ.bindc (lq_addRow _ g mats _) (total_one _ _ _ _) fun hW eW =>
    LQ.bindc (lq_addRow _ g mats _) (total_one _ _ _ _) fun hX eX =>
    LQ.bindc (lq_addRow _ g mats _) (total_one _ _ _ _) fun hE eE =>
    LQ.bindc (lq_addRow _ g mats _) (total_one _ _ _ _) fun hT eT =>
    LQ.bindc (lq_addRow _ g mats _) (total_one _ _ _ _) fun hPi ePi =>
    LQ.bindc (lq_addRow _ g mats _) (total_one _ _ _ _) fun hR2 eR2 =>
    LQ.bind0 (LQ.lift _ _) fun _ _ =>
    LQ.bindc (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun tO eO =>
    LQ.bindc (lq_mapM _ (fun k : ScoreP => [(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ []))
      (2 * (g.fillQ * g.T / 2 ^ g.la)) (fun _ => by simp [total]; omega)
      (fun m => (m, m + g.fillQ * g.T / 2 ^ g.la)) (fun m k => lq_pair m g mats k) p.scores _)
      (total_flat _ (2 * (g.fillQ * g.T / 2 ^ g.la)) (fun _ => by simp [total]; omega) _) fun tQK hQK =>
    LQ.bindc (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun qO eqO =>
    LQ.bindc (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun qVM eqVM =>
    LQ.bindc (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun qVD eqVD =>
    LQ.bindc (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun qF eqF =>
    LQ.bindc (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun qKx eqKx =>
    LQ.bind0 (LQ.lift _ _) fun _ _ =>
    LQ.bind0 (lq_weights _ _ _) fun w ew =>
    LQ.bindc (Q := fun a => a = _) (by subst ew; exact lq_add _ mats _ _ _ _) (total_one _ _ _ _) fun tB0 e0 =>
    LQ.bind0 (lq_weights _ _ _) fun w ew =>
    LQ.bindc (Q := fun a => a = _) (by subst ew; exact lq_add _ mats _ _ _ _) (total_one _ _ _ _) fun tB1 e1 =>
    LQ.bind0 (lq_weights _ _ _) fun w ew =>
    LQ.bindc (Q := fun a => a = _) (by subst ew; exact lq_add _ mats _ _ _ _) (total_one _ _ _ _) fun tPn e2 =>
    (lq_tailT _ _ _ _).mono ?_
  rintro t ⟨⟨s, rfl⟩, hn⟩
  subst hA hVM hVD eW eX eE eT ePi eR2 eO eqO eqVM eqVD eqF eqKx e0 e1 e2
  refine ⟨fun r hr => ?_, ?_⟩
  · cases r with
    | maxAtUnit u =>
      have hu : u < p.scores.size := by simpa [P.reads] using hr
      show ScoreT.tM (Array.getD _ u _) = _
      rw [score_get _ _ _ _ _ hM hQK u hu]
      simp only [P.Read.start, P.Geo.nScores, P.Geo.nRows]
      ring
    | queriesAtUnit u =>
      have hu : u < p.scores.size := by simpa [P.reads] using hr
      show ScoreT.tQ (Array.getD _ u _) = _
      rw [score_get _ _ _ _ _ hM hQK u hu]
      simp only [P.Read.start, P.Geo.nScores, P.Geo.nRows, P.Geo.nOut, P.Geo.nQkv, Array.length_toList]
      ring
    | keysAtUnit u =>
      have hu : u < p.scores.size := by simpa [P.reads] using hr
      show ScoreT.tK (Array.getD _ u _) = _
      rw [score_get _ _ _ _ _ hM hQK u hu]
      simp only [P.Read.start, P.Geo.nScores, P.Geo.nRows, P.Geo.nOut, P.Geo.nQkv, Array.length_toList]
      ring
    | _ =>
      simp only [P.Read.first, P.Read.start, P.Geo.nScores, P.Geo.nRows, P.Geo.nOut, P.Geo.nQkv, P.Geo.nPlanes,
        Array.length_toList] <;> ring
  · rw [← hn]
    simp only [P.Geo.nScores, P.Geo.nRows, P.Geo.nOut, P.Geo.nQkv, P.Geo.nPlanes, Array.length_toList]
    ring

/-! ### the first entries are the running sums -/

/-- st gives each member of the list the sum of m and of the numbers c of the members before it. -/
def Running (c st : Read → ℕ) : ℕ → List Read → Prop
  | _, [] => True
  | m, r :: l => st r = m ∧ Running c st (m + c r) l

theorem running_map {c st : Read → ℕ} {rest : List Read} (k : ℕ) :
    ∀ (n : ℕ) (F : ℕ → Read) (m : ℕ), (∀ u, c (F u) = k) → (∀ u, st (F u) = m + u * k) →
      Running c st (m + n * k) rest → Running c st m ((List.range n).map F ++ rest)
  | 0, _, m, _, _, h => by simpa using h
  | n + 1, F, m, hc, hs, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append]
    refine ⟨by simpa using hs 0, ?_⟩
    rw [hc]
    refine running_map k n (F ∘ Nat.succ) (m + k) (fun u => hc _) (fun u => ?_) ?_
    · show st (F (u + 1)) = _
      rw [hs]
      ring
    · rw [show m + k + n * k = m + (n + 1) * k by ring]
      exact h

theorem running_pairs {c st : Read → ℕ} {rest : List Read} (k : ℕ) :
    ∀ (n : ℕ) (F G : ℕ → Read) (m : ℕ), (∀ u, c (F u) = k) → (∀ u, c (G u) = k) →
      (∀ u, st (F u) = m + 2 * u * k) → (∀ u, st (G u) = m + (2 * u + 1) * k) →
      Running c st (m + 2 * n * k) rest → Running c st m ((List.range n).flatMap (fun u => [F u, G u]) ++ rest)
  | 0, _, _, m, _, _, _, _, h => by simpa using h
  | n + 1, F, G, m, hF, hG, sF, sG, h => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    refine ⟨by simpa using sF 0, ?_, ?_⟩
    · rw [hF, sG]
      ring
    · rw [hF, hG]
      refine running_pairs k n (F ∘ Nat.succ) (G ∘ Nat.succ) (m + k + k) (fun u => hF _) (fun u => hG _)
        (fun u => ?_) (fun u => ?_) ?_
      · show st (F (u + 1)) = _
        rw [sF]
        ring
      · show st (G (u + 1)) = _
        rw [sG]
        ring
      · rw [show m + k + k + 2 * n * k = m + 2 * (n + 1) * k by ring]
        exact h

/-- **The declared first entries are the running sums of the declared numbers of entries**, from 0 on, in the order of the list. -/
theorem starts_running (g : Geo) (n : ℕ) : Running (Read.count g) (Read.start g n) 0 (P.reads n) := by
  unfold P.reads
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine ⟨rfl, ?_, ?_, running_map g.nRows n _ _ (fun _ => rfl) (fun u => ?_)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, running_pairs g.nQkv n _ _ _ (fun _ => rfl) (fun _ => rfl) (fun u => ?_) (fun u => ?_)
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩⟩⟩
  all_goals
    simp only [P.Read.start, P.Read.count]
    ring

/-- Tables laid from running first entries: each member's tables lie from its own first entry on. -/
theorem lay_flat {c st : Read → ℕ} (Tb : Read → List Table) (hc : ∀ r, total (Tb r) = c r) :
    ∀ (rs : List Read) (m : ℕ), Running c st m rs →
      layFrom m (rs.flatMap Tb) = rs.flatMap fun r => layFrom (st r) (Tb r)
  | [], _, _ => rfl
  | r :: rs, m, h => by
    rw [List.flatMap_cons, List.flatMap_cons, layFrom_append, hc, lay_flat Tb hc rs _ h.2, h.1]

/-! ### from the placing's text to the declaration -/

/-- A read's tables without their first entries: one a part. -/
def tabs (g : Geo) (lk : LookIn) (p : Pts) (r : Read) : List Table :=
  (List.range ((r.of g lk p).1.parts g)).map fun q =>
    ⟨(r.of g lk p).1.number g + q, (r.of g lk p).2.len g, (r.of g lk p).2.array g,
      r.count g / (r.of g lk p).1.parts g⟩

theorem parts_eq (N x len : ℕ) (phi : Array E) :
    ((List.range N).map fun q => (⟨0 + q, len, phi, N * x / N⟩ : Table)) =
      (List.range N).map fun q => ⟨q, len, phi, x⟩ := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · rfl
  · rw [Nat.mul_div_cancel_left _ h]
    simp

theorem range_getD {ι : Type} (a : Array ι) (d : ι) (F : ι → List β) :
    (List.range a.size).flatMap (fun u => F (a.getD u d)) = a.toList.flatMap F := by
  have e : (List.range a.size).map (fun u => a.getD u d) = a.toList := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp at h1
    simp [h1]
  have e1 : (List.range a.size).flatMap (fun u => F (a.getD u d)) =
      ((List.range a.size).map fun u => a.getD u d).flatMap F := by
    rw [List.flatMap_map]
  rw [e1, e]

/-- What the placing's text lays is the declaration's list. -/
theorem laidBy_eq (g : Geo) (lk : LookIn) (p : Pts) :
    laidBy g lk p = (P.reads p.scores.size).flatMap (tabs g lk p) := by
  have u1 := range_getD p.scores P.noUnit fun k : ScoreP => [(⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩ : Table)]
  have u2 := range_getD p.scores P.noUnit fun k : ScoreP =>
      [(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
          (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table),
       ⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
          (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩]
  unfold laidBy P.reads
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatMap_map, List.flatMap_assoc,
    tabs, P.Read.of, P.Matrix.number, P.Matrix.parts, P.Weights.len, P.Weights.array, P.Read.count,
    P.Geo.nScores, P.Geo.nRows, P.Geo.nOut, P.Geo.nQkv, P.Geo.nPlanes, P.Pts.unit, parts_eq,
    List.range_one, List.map_cons, List.map_nil, Nat.add_zero, Nat.div_one,
    List.append_assoc, List.nil_append, List.append_nil, List.cons_append]
  rw [u1, u2]

theorem total_tabs (g : Geo) (lk : LookIn) (p : Pts) (r : Read) : total (tabs g lk p r) = r.count g := by
  unfold tabs
  rw [total_parts, List.length_range]
  cases r <;> simp only [P.Read.of, P.Matrix.parts, P.Read.count, Nat.div_one, Nat.one_mul]
  all_goals
    unfold P.Geo.nScores
    rcases Nat.eq_zero_or_pos g.NAs with h | h
    · rw [h]; simp
    · rw [Nat.mul_div_cancel_left _ h]

theorem lay_range (len : ℕ) (phi : Array E) (w : ℕ) (F : ℕ → ℕ) (m : ℕ) : ∀ N : ℕ,
    layFrom m ((List.range N).map fun q => (⟨F q, len, phi, w⟩ : Table)) =
      (List.range N).map fun q => ⟨F q, len, phi, 2, m + q * w⟩
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, layFrom_append, lay_range len phi w F m N,
      total_parts, List.length_range]
    rfl

/-- A read's tables with the weights as arrays. -/
def tablesA (g : Geo) (lk : LookIn) (p : Pts) (r : Read) : List Fun1 :=
  (List.range ((r.of g lk p).1.parts g)).map fun q =>
    ⟨(r.of g lk p).1.number g + q, (r.of g lk p).2.len g, (r.of g lk p).2.array g, 2,
      r.start g p.scores.size + q * (r.count g / (r.of g lk p).1.parts g)⟩

/-- **What tablesP lays, with the weights as arrays**: no premise but its return. -/
theorem tablesP_lays {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) :
    t.funs.toList = (P.reads p.scores.size).flatMap (tablesA g lk p) ∧
      (∀ r ∈ P.reads p.scores.size, r.first t = r.start g p.scores.size) ∧
      3 * g.nScores + (p.scores.size + 6) * g.nRows + g.nOut + (2 * p.scores.size + 5) * g.nQkv +
        3 * g.nPlanes = nW := by
  unfold P.tablesP at h
  have a : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  obtain ⟨y, hy, e⟩ := Option.bind_eq_some_iff.1 a
  obtain rfl := Option.some.inj e
  obtain ⟨⟨q1, q2⟩, f, _⟩ := lq_placeAll g mats nW lk p {} y.1 y.2 rfl hy
  refine ⟨?_, q1, q2⟩
  rw [fq_placeAll g mats nW lk p {} y.1 y.2 hy, f, laidBy_eq,
    lay_flat (tabs g lk p) (total_tabs g lk p) _ 0 (starts_running g p.scores.size)]
  show [] ++ _ = _
  rw [List.nil_append]
  refine List.flatMap_congr fun r _ => ?_
  exact lay_range _ _ _ _ _ _

theorem ofFn_getD (a : Array E) (n : ℕ) (h : a.size = n) : (Array.ofFn fun j : Fin n => a.getD j zeroE) = a := by
  subst h
  apply Array.ext (by simp)
  intro i h1 h2
  simp

theorem fit_at {g : Geo} {lk : LookIn} {p : Pts} (hf : P.fit g lk p = true) {r : Read}
    (hr : r ∈ P.reads p.scores.size) : ((r.of g lk p).2.array g).size = (r.of g lk p).2.len g := by
  unfold P.fit at hf
  exact beq_iff_eq.1 (List.all_eq_true.1 hf r hr)

/-- Where a read has as many weights as its run has cells, its record's tables are those with the arrays. -/
theorem tablesOf_decl (g : Geo) (lk : LookIn) (p : Pts) (r : Read)
    (h : ((r.of g lk p).2.array g).size = (r.of g lk p).2.len g) :
    P.tablesOf (r.decl g lk p) = tablesA g lk p r := by
  unfold P.tablesOf tablesA P.Read.decl
  simp only
  rw [ofFn_getD _ _ h]

/-- **tablesP's list of tables IS the declaration's, in order.** -/
theorem tablesP_is {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) (hf : P.fit g lk p = true) :
    t.funs = ((P.readsOfK5 g lk p).flatMap P.tablesOf).toArray := by
  apply Array.toList_inj.1
  rw [(tablesP_lays h).1, List.toList_toArray]
  unfold P.readsOfK5
  rw [List.flatMap_map]
  exact List.flatMap_congr fun r hr => (tablesOf_decl g lk p r (fit_at hf hr)).symm

/-- Under each field of the record stands the declared first entry. -/
theorem tablesP_firsts {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) :
    ∀ r ∈ P.reads p.scores.size, r.first t = (r.decl g lk p).start := (tablesP_lays h).2.1

/-- A declared weight is 0 from the run's length on. -/
theorem w_beyond {g : Geo} {lk : LookIn} {p : Pts} (hf : P.fit g lk p = true) {r : Read}
    (hr : r ∈ P.reads p.scores.size) (j : ℕ) (hj : (r.decl g lk p).len ≤ j) : (r.decl g lk p).w j = zeroE := by
  show ((r.of g lk p).2.array g).getD j zeroE = zeroE
  have hj' : (r.of g lk p).2.len g ≤ j := hj
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [fit_at hf hr]; exact hj')]
  rfl

/-! ### the weights of a long table, by feature and position; the cells -/

theorem lastCoords_size (z : Array E) (n : ℕ) (h : n ≤ z.size) : (P.lastCoords z n).size = n := by
  unfold P.lastCoords
  rw [Array.size_extract]
  omega

/-- **The order of a long table's weights**: the weight of feature a of the block at position i has the number a T + i; it is the product of the equality weight of a at the last ls coordinates of zc and of the position's weight. -/
theorem w_long {g : Geo} {lk : LookIn} {p : Pts} {r : Read} {zc w : Array E}
    (h : (r.of g lk p).2 = .long zc w) (hw : w.size = g.T) (hz : g.ls ≤ zc.size) {a i : ℕ} (ha : a < 2 ^ g.ls)
    (hi : i < g.T) :
    (r.decl g lk p).w (a * g.T + i) =
      mulE ((P.eqTab (P.lastCoords zc g.ls)).getD a zeroE) (w.getD i zeroE) := by
  show ((r.of g lk p).2.array g).getD (a * g.T + i) zeroE = _
  rw [h]
  have e := OnBytes.Road.blockRows_getD (P.eqTab (P.lastCoords zc g.ls)) w (r := a) (i := i)
    (by rw [eqTab_size, lastCoords_size _ _ hz]; exact ha) (by rw [hw]; exact hi)
  rw [hw] at e
  exact e

open VerifiableInference.Reads (cellOf)

/-- The one rule, inside the first part. -/
theorem cellOf_in (mat m k T F q : ℕ) (h : F < k * (m / T)) :
    cellOf mat m k T F q = (mat, F / (m / T), F % (m / T) * T + q) := by
  have h1 : F / (m / T) < k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  unfold cellOf
  rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.add_zero]

/-- **The cells of an entry of a short table**: column i / (m / len), row i % (m / len) len + j. -/
theorem cells_short (d : ReadDecl E) (m k i j : ℕ) (hm : d.make = .short) (hi : i < k * (m / d.len)) :
    d.cells m k i j = (d.mat, i / (m / d.len), i % (m / d.len) * d.len + j) := by
  unfold ReadDecl.cells
  rw [hm]
  exact cellOf_in _ _ _ _ _ _ hi

/-- **The cells of an entry of a long table**: the same column and row, where the run has block T cells and the rows are c runs. -/
theorem cells_long (d : ReadDecl E) (block T c k i j : ℕ) (hm : d.make = .long block) (hl : d.len = block * T)
    (hb : 0 < block) (hT : 0 < T) (hi : i < k * c) (hj : j < d.len) :
    d.cells (d.len * c) k i j = (d.mat, i / c, i % c * d.len + j) := by
  have e1 : d.len / block = T := by rw [hl]; exact Nat.mul_div_cancel_left _ hb
  have e2 : d.len * c / T = block * c := by
    rw [hl, show block * T * c = block * c * T by ring]
    exact Nat.mul_div_cancel _ hT
  have hr : j / T < block := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hl]; exact hj)
  have d1 : (block * i + j / T) / block = i := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, Nat.add_zero]
  have d2 : (block * i + j / T) % block = j / T := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, Nat.mul_zero] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · exact h
  unfold ReadDecl.cells
  rw [hm]
  simp only
  rw [e1, cellOf_in _ _ _ _ _ _ (by
    rw [e2]
    calc block * i + j / T < block * i + block := by omega
      _ = block * (i + 1) := by ring
      _ ≤ block * (k * c) := Nat.mul_le_mul_left _ hi
      _ = k * (block * c) := by ring), e2, ← Nat.div_div_eq_div_mul, d1, Nat.mod_mul, d2, d1]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  show (j / T + block * (i % c)) * T + j % T = i % c * d.len + j
  rw [hl]
  have := Nat.div_add_mod j T
  nlinarith [this]

/-- **The cells of an entry of a table in parts**: part i / (m / len) / k, column i / (m / len) % k, row i % (m / len) len + j. -/
theorem cells_part (d : ReadDecl E) (m k i j : ℕ) (hm : d.make = .part) :
    d.cells m k i j = (d.mat + i / (m / d.len) / k, i / (m / d.len) % k, i % (m / d.len) * d.len + j) := by
  unfold ReadDecl.cells
  rw [hm]
  rfl

/-- **The cells of an entry of a table of whole columns**, inside the first part. -/
theorem cells_column (d : ReadDecl E) (m k i j : ℕ) (hm : d.make = .column) (hi : i < k) :
    d.cells m k i j = (d.mat, i, j) := by
  unfold ReadDecl.cells
  rw [hm]
  simp only
  rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.add_zero]

end K5Law
