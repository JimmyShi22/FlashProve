-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsReturn.lean: kind K5: tablesP
(Johnson/Desc/First/Att/TablesP.lean) returns just where one Boolean says yes; and at which reads
its own tests already give as many weights as the run has cells.

Main names:
  `placeOk g mats nW lk p`: the two tests on values (mergedPlanes, mergedTokens: the units' inner
    points and the division's points share their last coordinates with the lookup's point) · the
    lookup's planesOk · every declared table fits the list of matrices (fits) · the long tables'
    three tests on lengths (longOk, lngB) · the declared numbers of entries add up to nW.
  `tablesP_isSome`: (tablesP g mats nW lk p).isSome = placeOk g mats nW lk p. `tablesP_some`.
  `theTen`, `fitTen`: the ten reads at which no test of tablesP asks that the weights are as many as
    the cells: the three in parts, the rows at the division's index point, at the drawn point and
    at the points of the sumchecks for the key and for the bits, and the lookup's three.
  `forced`: where placeOk says yes, every other read of the list has as many weights as cells.
  `fit_eq_ten`: so fit (Johnson/Desc/First/Att/ReadsOf.lean) is there the test at the ten.
Tools: fitsT; RT mats n r L b: from the first free entry n the routine r returns just where every
  table of L fits and b holds; its rules beside those of LQ (Claims/ReadsOfIs.lean); extras, the
  tests in the text's own order; rt_placeAll; longs_eq; blockRows_size, long_fit, tok_size.
What it is for. The premises of tablesP_is (the return; fit) are met just where placeOk and fitTen
say yes: two Booleans that read public numbers, lengths, and the two comparisons of coordinates.
Not shown in this file: that they say yes at any geometry.
Nothing of OnBytes is used but the field's type E, its 0 and its product mulE.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsOfIs

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Reads (Make ReadDecl)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T TablesP ScoreT LookIn Pts ScoreP Read Matrix Weights)

variable {α β : Type}

/-- The table fits the list of matrices (fits, Att/TablesP.lean). -/
def fitsT (mats : Array (ℕ × ℕ)) (t : Table) : Bool := P.fits mats t.mat t.len t.entries

/-- From the first free entry n the routine returns just where every table of L fits and b holds. -/
def RT (mats : Array (ℕ × ℕ)) (n : ℕ) (r : T α) (L : List Table) (b : Bool) : Prop :=
  ∀ s, s.next = n → (r s).isSome = (L.all (fitsT mats) && b)

variable {mats : Array (ℕ × ℕ)}

theorem RT.pure (n : ℕ) (a : α) : RT mats n (Pure.pure a : T α) [] true := fun _ _ => rfl

theorem RT.bind {n : ℕ} {r : T α} {k : α → T β} {Q : α → Prop} {L L' : List Table} {b b' : Bool}
    (h1 : RT mats n r L b) (hq : LQ n r Q L) (h2 : ∀ a, Q a → RT mats (n + total L) (k a) L' b') :
    RT mats n (r >>= k) (L ++ L') (b && b') := by
  intro s hn
  show ((r s).bind fun y => k y.1 y.2).isSome = _
  have e1 := h1 s hn
  rw [List.all_append]
  cases hr : r s with
  | none =>
    rw [hr] at e1
    have e1' : (L.all (fitsT mats) && b) = false := e1.symm
    rcases (Bool.and_eq_false_iff.1 e1') with h | h <;> simp [h]
  | some y =>
    rw [hr] at e1
    have e1' : (L.all (fitsT mats) && b) = true := e1.symm
    obtain ⟨a1, a2⟩ := Bool.and_eq_true_iff.1 e1'
    obtain ⟨q, _, n1⟩ := hq s y.1 y.2 hn hr
    show (k y.1 y.2).isSome = _
    rw [h2 y.1 q y.2 n1, a1, a2]
    simp

theorem RT.bindc {n c : ℕ} {r : T α} {k : α → T β} {Q : α → Prop} {L L' : List Table} {b b' : Bool}
    (h1 : RT mats n r L b) (hq : LQ n r Q L) (hc : total L = c)
    (h2 : ∀ a, Q a → RT mats (n + c) (k a) L' b') :
    RT mats n (r >>= k) (L ++ L') (b && b') := by
  subst hc
  exact RT.bind h1 hq h2

theorem RT.bind0 {n : ℕ} {r : T α} {k : α → T β} {Q : α → Prop} {L' : List Table} {b b' : Bool}
    (h1 : RT mats n r [] b) (hq : LQ n r Q []) (h2 : ∀ a, Q a → RT mats n (k a) L' b') :
    RT mats n (r >>= k) L' (b && b') :=
  RT.bind (L := []) h1 hq h2

theorem RT.lift (n : ℕ) (x : Option α) : RT mats n (monadLift x : T α) [] x.isSome := by
  intro s _
  cases x <;> rfl

theorem mustAs_isSome (nm : String) (b : Bool) : (P.mustAs nm b).isSome = b := by
  cases b <;> rfl

theorem rt_must (n : ℕ) (nm : String) (b : Bool) : RT mats n (monadLift (P.mustAs nm b) : T PUnit) [] b := by
  have h := RT.lift (mats := mats) n (P.mustAs nm b)
  rwa [mustAs_isSome] at h

theorem rt_weights (n m : ℕ) (f : Unit → Array E) : RT mats n (P.T.weights m f) [] true := RT.pure _ _

theorem rt_getAs (n : ℕ) (nm : String) (x : Option α) : RT mats n (P.T.getAs nm x) [] x.isSome := by
  intro s _
  cases x <;> rfl

theorem rt_add (n : ℕ) (mat len : ℕ) (phi : Array E) (e : ℕ) :
    RT mats n (P.add mats mat len phi e) [⟨mat, len, phi, e⟩] true := by
  intro s _
  unfold P.add P.mustAs
  simp only [List.all_cons, List.all_nil, Bool.and_true, fitsT]
  cases hf : P.fits mats mat len e <;> rfl

theorem rt_discard {n : ℕ} {r : T α} {L : List Table} {b : Bool} (h : RT mats n r L b) :
    RT mats n (discard r : T PUnit) L b := by
  intro s hn
  rw [← h s hn]
  show ((r s).bind fun x => some (PUnit.unit, x.2)).isSome = _
  cases r s <;> rfl

theorem lq_discard {n : ℕ} {r : T α} {Q : α → Prop} {L : List Table} (h : LQ n r Q L) :
    LQ n (discard r : T PUnit) (fun _ => True) L := by
  intro s a s' hn e
  obtain ⟨x, hx⟩ := discard_some (u := a) (s' := s') e
  exact ⟨trivial, (h s x s' hn hx).2⟩

theorem rt_parts (len : ℕ) (phi : Array E) (w : ℕ) :
    ∀ (qs : List ℕ) (n : ℕ), RT mats n (qs.forM fun q => discard (P.add mats q len phi w))
      (qs.map fun q => ⟨q, len, phi, w⟩) true
  | [], n => RT.pure n PUnit.unit
  | q0 :: qs, n => by
    have h := RT.bind (rt_discard (rt_add (mats := mats) n q0 len phi w)) (lq_discard (lq_add n mats q0 len phi w))
      fun _ _ => rt_parts len phi w qs _
    exact h

theorem rt_addAs (n : ℕ) (g : Geo) (phi : Unit → Array E) :
    RT mats n (P.addAs g mats phi) ((List.range g.NAs).map fun q => ⟨q, 2 ^ g.lmS, phi (), g.kAs / g.NAs⟩) true := by
  intro s hn
  rw [← rt_parts (mats := mats) (2 ^ g.lmS) (phi ()) (g.kAs / g.NAs) (List.range g.NAs) n s hn]
  unfold P.addAs P.T.weights P.T.placed P.T.total
  show (((List.range g.NAs).forM fun q => discard (P.add mats q (2 ^ g.lmS) (phi ()) (g.kAs / g.NAs))) s |>.bind
    fun y => _).isSome = _
  cases ((List.range g.NAs).forM fun q => discard (P.add mats q (2 ^ g.lmS) (phi ()) (g.kAs / g.NAs))) s <;> rfl

theorem rt_addRow (n : ℕ) (g : Geo) (psi : Unit → Array E) :
    RT mats n (P.addRow g mats psi) [⟨g.NAs, g.T, psi (), g.fillH⟩] true := by
  unfold P.addRow
  exact RT.bind0 (rt_weights _ _ _) (lq_weights _ _ _) fun w e => by rw [e]; exact rt_add n _ _ _ _

theorem RT.cast {n : ℕ} {r : T α} {L : List Table} {b b' : Bool} (h : RT mats n r L b) (e : b = b') :
    RT mats n r L b' := e ▸ h

theorem RT.bindPure {n : ℕ} {r : T α} {L : List Table} {b : Bool} (h : RT mats n r L b) (F : α → β) :
    RT mats n (r >>= fun a => (Pure.pure (F a) : T β)) L b := by
  intro s hn
  rw [← h s hn]
  show ((r s).bind fun y => some (F y.1, y.2)).isSome = _
  cases r s <;> rfl

/-- The tests of a long table on lengths: T weights on the positions; a long run has 2^ls T cells; zc has ls coordinates at least. -/
def lngB (g : Geo) (zc w : Array E) : Bool :=
  (w.size == g.T && 2 ^ g.la == 2 ^ g.ls * g.T) && decide (g.ls ≤ zc.size)

theorem cutLast_isSome (z : Array E) (k : ℕ) : (P.cutLast z k).isSome = decide (k ≤ z.size) := by
  unfold P.cutLast
  split
  · rename_i h
    simp [Nat.not_le.2 h]
  · rename_i h
    simp [Nat.not_lt.1 h]

theorem rt_lng (n : ℕ) (g : Geo) (zc : Array E) (ptk : Unit → Array E) :
    RT mats n (P.lng g zc ptk) [] (lngB g zc (ptk ())) := by
  unfold P.lng
  refine RT.cast (RT.bind0 (rt_weights _ _ _) (lq_weights _ _ _)
    (b' := ((ptk ()).size == g.T && 2 ^ g.la == 2 ^ g.ls * g.T) && ((P.cutLast zc g.ls).isSome && true))
    fun w ew => ?_) ?_
  · subst ew
    exact RT.bind0 (rt_must _ _ _) (LQ.lift _ _) fun _ _ =>
      RT.bind0 (rt_getAs _ _ _) (lq_getAs _ _ _) fun c _ => rt_weights _ _ _
  · rw [cutLast_isSome]
    simp [lngB]

theorem rt_addLong (n : ℕ) (g : Geo) (mat : ℕ) (zc : Array E) (ptk : Unit → Array E) (e : ℕ) :
    RT mats n (P.addLong g mats mat zc ptk e)
      [⟨mat, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords zc g.ls)) (ptk ()), e⟩] (lngB g zc (ptk ())) := by
  unfold P.addLong
  exact (RT.bind0 (rt_lng n g zc ptk) (lq_lng n g zc ptk) fun w ew => by rw [ew]; exact rt_add n _ _ _ _).cast
    (Bool.and_true _)

theorem rt_mapML {ι : Type} (f : ι → T α) (Lx : ι → List Table) (bx : ι → Bool) (Qx : ℕ → α → Prop)
    (hf : ∀ m x, RT mats m (f x) (Lx x) (bx x)) (hq : ∀ m x, LQ m (f x) (Qx m) (Lx x)) :
    ∀ (xs : List ι) (n : ℕ), RT mats n (xs.mapM f) (xs.flatMap Lx) (xs.all bx)
  | [], n => by
    rw [List.mapM_nil]
    exact RT.pure _ _
  | x :: xs, n => by
    rw [List.mapM_cons, List.flatMap_cons, List.all_cons]
    exact RT.bind (hf n x) (hq n x) fun y _ => (rt_mapML f Lx bx Qx hf hq xs _).bindPure _

theorem rt_mapM {ι : Type} (f : ι → T α) (Lx : ι → List Table) (bx : ι → Bool) (Qx : ℕ → α → Prop)
    (hf : ∀ m x, RT mats m (f x) (Lx x) (bx x)) (hq : ∀ m x, LQ m (f x) (Qx m) (Lx x)) (xs : Array ι) (n : ℕ) :
    RT mats n (xs.mapM f) (xs.toList.flatMap Lx) (xs.toList.all bx) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  exact (rt_mapML f Lx bx Qx hf hq xs.toList n).bindPure _

theorem rt_tail (n nW : ℕ) (nm : String) (F : Placed → TablesP) :
    RT mats n (P.T.placed >>= fun t => (monadLift (P.mustAs nm (t.next == nW)) : T PUnit) >>= fun _ => Pure.pure (F t))
      [] (n == nW) := by
  intro s hn
  show (((monadLift (P.mustAs nm (s.next == nW)) : T PUnit) >>= fun _ => (Pure.pure (F s) : T TablesP)) s).isSome = _
  rw [hn]
  cases (n == nW) <;> rfl

theorem rt_pair (m : ℕ) (g : Geo) (k : ScoreP) :
    RT mats m (P.addLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (fun _ => P.tok g (P.scoreTiles g k).1 k.zi)
          (g.fillQ * g.T / 2 ^ g.la) >>= fun tQ =>
        P.addLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (fun _ => P.tok g (P.scoreTiles g k).2 k.zj)
          (g.fillQ * g.T / 2 ^ g.la) >>= fun tK => (Pure.pure (tQ, tK) : T (ℕ × ℕ)))
      ([(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ []))
      (lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi) &&
        (lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj) && true)) :=
  RT.bind (rt_addLong m g _ _ _ _) (lq_addLong m g mats _ _ _ _) fun _ _ =>
    RT.bind (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) fun _ _ => RT.pure _ _

/-- The tests of the placing that are no table's fitting, in the text's order. -/
def extras (g : Geo) (nW : ℕ) (lk : LookIn) (p : Pts) : Bool :=
  P.mergedPlanes g.lmS lk.zx p.planes && (true && (true && (true && (p.scores.toList.all (fun _ => true) &&
  (true && (true && (true && (true && (true && (true &&
  (P.mergedTokens g lk.zx p.d &&
  (lngB g p.d.zcW (P.eqTab p.d.ziW) &&
  (p.scores.toList.all (fun k => lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi) &&
        (lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj) && true)) &&
  (lngB g p.d.zcW (P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))) &&
  (lngB g p.d.zcW (P.tok g p.d.wJv (P.lastCoords p.d.vpm.r g.lB)) &&
  (lngB g p.d.zcW (P.tok g (P.eqTab (p.d.vpd.r.extract g.lgk (g.lgk + g.lnT))) (P.lastCoords p.d.vpd.r g.lB)) &&
  (lngB g (p.x.rc g) (P.eqTab (p.x.ri g)) &&
  (lngB g (p.x.rc g) (P.eqTab (p.x.pj g)) &&
  (lk.planesOk && (true && (true && (true && (true && (true && (true &&
  (0 + g.NAs * (g.kAs / g.NAs) + g.NAs * (g.kAs / g.NAs) + g.NAs * (g.kAs / g.NAs) +
      p.scores.toList.length * g.fillH + g.fillH + g.fillH + g.fillH + g.fillH + g.fillH + g.fillH +
      g.fillO * g.T / 2 ^ g.la + p.scores.toList.length * (2 * (g.fillQ * g.T / 2 ^ g.la)) +
      g.fillQ * g.T / 2 ^ g.la + g.fillQ * g.T / 2 ^ g.la + g.fillQ * g.T / 2 ^ g.la + g.fillQ * g.T / 2 ^ g.la +
      g.fillQ * g.T / 2 ^ g.la + g.kbA + g.kbA + g.kbA == nW))))))))))))))))))))))))))

theorem rt_placeAll (g : Geo) (nW : ℕ) (lk : LookIn) (p : Pts) :
    RT mats 0 (P.placeAll g mats nW lk p) (laidBy g lk p) (extras g nW lk p) := by
  unfold P.placeAll laidBy extras
  exact
    RT.bind0 (rt_must _ _ _) (LQ.lift _ _) fun _ _ =>
    RT.bindc (rt_addAs _ g _) (lq_addAs _ g mats _) (total_range _ _ _ _) fun _ _ =>
    RT.bindc (rt_addAs _ g _) (lq_addAs _ g mats _) (total_range _ _ _ _) fun _ _ =>
    RT.bindc (rt_addAs _ g _) (lq_addAs _ g mats _) (total_range _ _ _ _) fun _ _ =>
    RT.bindc (rt_mapM _ (fun k : ScoreP => [⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩]) (fun _ => true)
        (fun m a => a = m) (fun m k => rt_addRow m g _) (fun m k => lq_addRow m g mats _) p.scores _)
      (lq_mapM _ (fun k : ScoreP => [⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩]) g.fillH
        (fun _ => total_one _ _ _ _) (fun m => m) (fun m k => lq_addRow m g mats _) p.scores _)
      (total_flat _ g.fillH (fun _ => total_one _ _ _ _) _) fun _ _ =>
    RT.bindc (rt_addRow _ g _) (lq_addRow _ g mats _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addRow _ g _) (lq_addRow _ g mats _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addRow _ g _) (lq_addRow _ g mats _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addRow _ g _) (lq_addRow _ g mats _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addRow _ g _) (lq_addRow _ g mats _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addRow _ g _) (lq_addRow _ g mats _) (total_one _ _ _ _) fun _ _ =>
    RT.bind0 (rt_must _ _ _) (LQ.lift _ _) fun _ _ =>
    RT.bindc (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_mapM _ (fun k : ScoreP => [(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ []))
        (fun k => lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi) &&
          (lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj) && true))
        (fun m a => a = (m, m + g.fillQ * g.T / 2 ^ g.la)) (fun m k => rt_pair m g k) (fun m k => lq_pair m g mats k)
        p.scores _)
      (lq_mapM _ (fun k : ScoreP => [(⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la, P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls)) (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ []))
        (2 * (g.fillQ * g.T / 2 ^ g.la)) (fun _ => by simp [total]; omega)
        (fun m => (m, m + g.fillQ * g.T / 2 ^ g.la)) (fun m k => lq_pair m g mats k) p.scores _)
      (total_flat _ (2 * (g.fillQ * g.T / 2 ^ g.la)) (fun _ => by simp [total]; omega) _) fun _ _ =>
    RT.bindc (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun _ _ =>
    RT.bindc (rt_addLong _ g _ _ _ _) (lq_addLong _ g mats _ _ _ _) (total_one _ _ _ _) fun _ _ =>
    RT.bind0 (rt_must _ _ _) (LQ.lift _ _) fun _ _ =>
    RT.bind0 (rt_weights _ _ _) (lq_weights _ _ _) fun w ew =>
    RT.bindc (Q := fun _ => True) (by subst ew; exact rt_add _ _ _ _ _)
      (by subst ew; exact (lq_add _ mats _ _ _ _).mono fun _ _ => trivial) (total_one _ _ _ _) fun _ _ =>
    RT.bind0 (rt_weights _ _ _) (lq_weights _ _ _) fun w ew =>
    RT.bindc (Q := fun _ => True) (by subst ew; exact rt_add _ _ _ _ _)
      (by subst ew; exact (lq_add _ mats _ _ _ _).mono fun _ _ => trivial) (total_one _ _ _ _) fun _ _ =>
    RT.bind0 (rt_weights _ _ _) (lq_weights _ _ _) fun w ew =>
    RT.bindc (Q := fun _ => True) (by subst ew; exact rt_add _ _ _ _ _)
      (by subst ew; exact (lq_add _ mats _ _ _ _).mono fun _ _ => trivial) (total_one _ _ _ _) fun _ _ =>
    rt_tail _ _ _ _

/-- The tests on lengths of a read's long table; true of every other read. -/
def longOk (g : Geo) (lk : LookIn) (p : Pts) (r : Read) : Bool :=
  match (r.of g lk p).2 with
  | .long zc w => lngB g zc w
  | _ => true

/-- **The one test under which tablesP returns**: the units' inner points and the division's points share their last coordinates with the lookup's point (two tests on values); the lookup's planes' matrix has a lawful number of row bits; every declared table fits the list of matrices; the long tables' lengths; the declared numbers of entries add up to nW. -/
def placeOk (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) : Bool :=
  P.mergedPlanes g.lmS lk.zx p.planes && P.mergedTokens g lk.zx p.d && lk.planesOk &&
  (P.reads p.scores.size).all (fun r => (tabs g lk p r).all (fitsT mats)) &&
  (P.reads p.scores.size).all (longOk g lk p) &&
  (3 * g.nScores + (p.scores.size + 6) * g.nRows + g.nOut + (2 * p.scores.size + 5) * g.nQkv + 3 * g.nPlanes == nW)

theorem range_all {ι : Type} (a : Array ι) (d : ι) (f : ι → Bool) :
    (List.range a.size).all (fun u => f (a.getD u d)) = a.toList.all f := by
  have e : (List.range a.size).map (fun u => a.getD u d) = a.toList := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp at h1
    simp [h1]
  rw [← e, List.all_map]
  rfl

theorem all_true {ι : Type} (l : List ι) : l.all (fun _ => true) = true := by
  induction l <;> simp_all

theorem longs_eq (g : Geo) (lk : LookIn) (p : Pts) :
    (P.reads p.scores.size).all (longOk g lk p) =
      (lngB g p.d.zcW (P.eqTab p.d.ziW) &&
      (p.scores.toList.all (fun k => lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi) &&
        (lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj) && true)) &&
      (lngB g p.d.zcW (P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))) &&
      (lngB g p.d.zcW (P.tok g p.d.wJv (P.lastCoords p.d.vpm.r g.lB)) &&
      (lngB g p.d.zcW (P.tok g (P.eqTab (p.d.vpd.r.extract g.lgk (g.lgk + g.lnT))) (P.lastCoords p.d.vpd.r g.lB)) &&
      (lngB g (p.x.rc g) (P.eqTab (p.x.ri g)) && lngB g (p.x.rc g) (P.eqTab (p.x.pj g)))))))) := by
  have u := range_all p.scores P.noUnit fun k : ScoreP =>
    lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi) &&
      (lngB g (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj) && true)
  rw [← u]
  unfold P.reads
  simp only [List.all_append, List.all_cons, List.all_nil, List.all_map, List.all_flatMap, longOk, P.Read.of,
    P.Pts.unit, Function.comp_def, Bool.and_true, Bool.true_and, all_true, Bool.and_assoc]

/-- **tablesP returns just where placeOk says yes.** -/
theorem tablesP_isSome (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) :
    (P.tablesP g mats nW lk p).isSome = placeOk g mats nW lk p := by
  have h := rt_placeAll (mats := mats) g nW lk p {} rfl
  have e : (P.tablesP g mats nW lk p).isSome = (P.placeAll g mats nW lk p {}).isSome := by
    unfold P.tablesP
    show ((P.placeAll g mats nW lk p {}).bind fun y => some y.1).isSome = _
    cases P.placeAll g mats nW lk p {} <;> rfl
  rw [e, h, laidBy_eq, List.all_flatMap]
  unfold placeOk extras
  rw [longs_eq]
  have s : 0 + g.NAs * (g.kAs / g.NAs) + g.NAs * (g.kAs / g.NAs) + g.NAs * (g.kAs / g.NAs) +
      p.scores.toList.length * g.fillH + g.fillH + g.fillH + g.fillH + g.fillH + g.fillH + g.fillH +
      g.fillO * g.T / 2 ^ g.la + p.scores.toList.length * (2 * (g.fillQ * g.T / 2 ^ g.la)) +
      g.fillQ * g.T / 2 ^ g.la + g.fillQ * g.T / 2 ^ g.la + g.fillQ * g.T / 2 ^ g.la + g.fillQ * g.T / 2 ^ g.la +
      g.fillQ * g.T / 2 ^ g.la + g.kbA + g.kbA + g.kbA =
      3 * g.nScores + (p.scores.size + 6) * g.nRows + g.nOut + (2 * p.scores.size + 5) * g.nQkv + 3 * g.nPlanes := by
    simp only [P.Geo.nScores, P.Geo.nRows, P.Geo.nOut, P.Geo.nQkv, P.Geo.nPlanes, Array.length_toList]
    ring
  rw [s]
  simp only [all_true, Bool.true_and, Bool.and_true, Bool.and_assoc]
  ac_rfl

/-- So the premise of tablesP_is is met just where placeOk and fit say yes. -/
theorem tablesP_some {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts}
    (h : placeOk g mats nW lk p = true) : ∃ t, P.tablesP g mats nW lk p = some t :=
  Option.isSome_iff_exists.1 (by rw [tablesP_isSome]; exact h)

/-! ### which reads have as many weights as cells by the text's own tests -/

theorem blockRows_size (low tok : Array E) : (P.blockRows low tok).size = low.size * tok.size := by
  have key : ∀ l : List E, (l.flatMap fun a => (tok.map fun b => mulE a b).toList).length = l.length * tok.size := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons, Array.length_toList, Array.size_map]
      ring
  unfold P.blockRows
  rw [← Array.length_toList, Array.toList_flatMap, key, Array.length_toList]

theorem long_fit {g : Geo} {zc w : Array E} (h : lngB g zc w = true) :
    (P.blockRows (P.eqTab (P.lastCoords zc g.ls)) w).size = 2 ^ g.la ∧ w.size = g.T := by
  unfold lngB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨by rw [blockRows_size, eqTab_size, lastCoords_size _ _ h3, h1, h2], h1⟩

theorem tok_size (g : Geo) (hi lo : Array E) : (P.tok g hi lo).size = g.T := by
  unfold P.tok
  simp

/-- The ten reads at which no test of tablesP asks that the weights are as many as the cells. -/
def theTen : List Read :=
  [.planesAtKeys, .planesAtBelow, .planesAtOn, .rowsAtIndex, .rowsAtDrawn, .rowsAtKey, .rowsAtBits,
   .bitsAtLeaves, .bitsAtBits, .counts]

/-- The test fit at these ten alone. -/
def fitTen (g : Geo) (lk : LookIn) (p : Pts) : Bool :=
  theTen.all fun r => ((r.of g lk p).2.array g).size == (r.of g lk p).2.len g

theorem ten_in (n : ℕ) : ∀ r ∈ theTen, r ∈ P.reads n := by
  intro r hr
  simp only [theTen, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [P.reads]

/-- **Where tablesP returns, every read but the ten has as many weights as its run has cells**: the long tables by their own test; the units' maxima by the make of their weights; the rows at the division's point and at its sumcheck's point because a long table's test is on the same array. -/
theorem forced {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} (h : placeOk g mats nW lk p = true) :
    ∀ r ∈ P.reads p.scores.size, r ∉ theTen →
      ((r.of g lk p).2.array g).size = (r.of g lk p).2.len g := by
  unfold placeOk at h
  simp only [Bool.and_eq_true] at h
  have hl : ∀ r ∈ P.reads p.scores.size, longOk g lk p r = true := List.all_eq_true.1 h.1.2
  intro r hr hn
  cases r with
  | maxAtUnit u => exact tok_size _ _ _
  | rowsAtDivide => exact (long_fit (hl .outAtDivide (by simp [P.reads]))).2
  | rowsAtProduct => exact (long_fit (hl .outputsAtProduct (by simp [P.reads]))).2
  | outAtDivide => exact (long_fit (hl _ hr)).1
  | queriesAtUnit u => exact (long_fit (hl _ hr)).1
  | keysAtUnit u => exact (long_fit (hl _ hr)).1
  | outputsAtProduct => exact (long_fit (hl _ hr)).1
  | valuesAtBelow => exact (long_fit (hl _ hr)).1
  | valuesAtOn => exact (long_fit (hl _ hr)).1
  | queriesAtIndex => exact (long_fit (hl _ hr)).1
  | keysAtIndex => exact (long_fit (hl _ hr)).1
  | _ => exact absurd (by simp [theTen]) hn

/-- So, where tablesP returns, fit is the test at the ten. -/
theorem fit_eq_ten {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} (h : placeOk g mats nW lk p = true) :
    P.fit g lk p = fitTen g lk p := by
  rw [Bool.eq_iff_iff]
  unfold P.fit fitTen
  rw [List.all_eq_true, List.all_eq_true]
  refine ⟨fun a r hr => a r (ten_in _ r hr), fun a r hr => ?_⟩
  by_cases hn : r ∈ theTen
  · exact a r hn
  · exact beq_iff_eq.2 (forced h r hr hn)

end K5Law
