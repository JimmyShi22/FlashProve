-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean: the weights that the smallness test declares for its virtual
rows, on the body of HTailF2.coefficientsF.

A virtual row of an array is a combination of the array's rows. HTailF2.coefficientsF writes each
virtual row's weights into the state of the sub-proof (HRow.coef), by a chain of writes (onRow).

 - coefficientsF_eq: the routine is five stages, one after the other (by rfl): the tables' rows, the
   rows of the pieces of the two lookup calls, two rows of ZZ under powers, BZ's three rows, the
   matrices' rows. coefficientsF_ok: a run that returns leaves coefAll tl g F and the same context.
 - rowAt, HasRow, Frame; rowAt_onRow_eq, rowAt_onRow_ne, frame_onRow: one write.
 - foldl_writes, foldl_last: a row of writes: what it leaves alone; at places that differ each place
   holds what its own write laid.
 - frame_all: the routine turns no array's number of rows or of virtual rows.
 - coef_bz: behind the routine, BZ's virtual rows 0 and 1 have the weights eqTab of the first five
   coordinates of the two points at which the planes are read, and row 2 has 32 ones. Premises: the
   state has the three rows; no matrix's array is BZ.
 - coef_piece: the virtual row of a piece p of call q has the weights pieceW: on the rows r0, ..,
   r0 + Rp - 1 the equality table of p.a coordinates of the call's point, 0 elsewhere. Premises: the
   state has the row; the pieces' rows differ from each other, from the two rows under powers, from
   BZ's and from the matrices'.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a virtual row's entries are the combination under these weights (RowsLaw,
OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean, is a hypothesis). Nor is anything claimed on the product
forms (rowPoint, rowLo, rowHi), which the chain takes and rowWeights compares with coef.

-/
import OnBytes.Model.Tail
import OnBytes.Tie.Pv.Psc.PscRun

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.PscRun

/-- The tables' rows. -/
def coefTables (tl : HTailF2) (F : Fork) : Fork := Id.run do
  let mut F := F
  for n in List.range 4 do
    if let some t := tl.ix.U.getD n none then
      if (F.trees.getD t {}).kind == .table then
        F := onRow F t 0 fun row => formOnes { row with coef := #[oneE] }
  return F

/-- The weights of a piece's virtual row. -/
def pieceW (c : CallZ) (zk : Array E) (p : Piece) (R : Nat) : Array E :=
  (Array.range R).map fun r =>
    if p.r0 ≤ r ∧ r < p.r0 + p.Rp then
      (eqTab (zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a))).getD (r - p.r0) zeroE
    else zeroE

/-- The pieces' rows. -/
def coefPieces (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Fork := Id.run do
  let mut F := F
  for q in [0, 1] do
    let c := tl.zOf q
    let zk := g.zk.getD q #[]
    for p in c.pieces do
      let zr := zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a)
      let e := eqTab zr
      let R := (F.trees.getD p.tree {}).R
      let w := (Array.range R).map fun r =>
        if p.r0 ≤ r ∧ r < p.r0 + p.Rp then e.getD (r - p.r0) zeroE else zeroE
      F := onRow F p.tree p.row fun row => formPoint { row with coef := w } zr p.r0
  return F

/-- The two rows of ZZ under powers. -/
def coefPowers (tl : HTailF2) (theta : E) (F : Fork) : Fork :=
  onRow (onRow F tl.ix.ZZ tl.zzRowReads fun row => formPowers { row with coef := tl.vt } theta
      tl.tau)
    tl.ix.ZZ tl.zzRowTies fun row => formPowers { row with coef := tl.vp } theta tl.tau

/-- BZ's three rows. -/
def coefBZ (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Fork :=
  onRow (onRow (onRow F tl.ix.BZ 0 fun row =>
      formPoint { row with coef := eqTab ((g.zb 0).extract 0 5) } ((g.zb 0).extract 0 5) 0)
    tl.ix.BZ 1 fun row =>
      formPoint { row with coef := eqTab ((g.zb 1).extract 0 5) } ((g.zb 1).extract 0 5) 0)
    tl.ix.BZ 2 fun row => formOnes { row with coef := Array.replicate 32 oneE }

/-- The matrices' rows. -/
def coefMats (tl : HTailF2) (theta : E) (F : Fork) : Fork := Id.run do
  let mut F := F
  for mu in List.range tl.NM do
    F := onRow F (tl.gtTree.getD mu 0) 0 fun row =>
      formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
        (tl.shp.getD mu {}).mS
  return F

/-- The routine, stage by stage. -/
theorem coefficientsF_eq (tl : HTailF2) :
    tl.coefficientsF = (do
      let g ← SubM.get tl.heard
      modify fun F => coefMats tl F.theta (coefBZ tl g (coefPowers tl F.theta
        (coefPieces tl g (coefTables tl F))))) := rfl

/-! ### one write -/

/-- Virtual row e of array t. -/
def rowAt (F : Fork) (t e : Nat) : HRow := (F.trees.getD t {}).rows.getD e {}

/-- The state has virtual row e of array t. -/
def HasRow (F : Fork) (t e : Nat) : Prop := t < F.trees.size ∧ e < (F.trees.getD t {}).rows.size

/-- The arrays, their numbers of rows and of virtual rows are the same. -/
def Frame (F G : Fork) : Prop :=
  G.trees.size = F.trees.size ∧ ∀ t, (G.trees.getD t {}).R = (F.trees.getD t {}).R ∧
    (G.trees.getD t {}).rows.size = (F.trees.getD t {}).rows.size

theorem Frame.refl (F : Fork) : Frame F F := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem Frame.trans {F G H : Fork} (h1 : Frame F G) (h2 : Frame G H) : Frame F H :=
  ⟨h2.1.trans h1.1, fun t => ⟨(h2.2 t).1.trans (h1.2 t).1, (h2.2 t).2.trans (h1.2 t).2⟩⟩

theorem Frame.hasRow {F G : Fork} (h : Frame F G) {t e : Nat} (hr : HasRow F t e) : HasRow G t e :=
  ⟨h.1 ▸ hr.1, (h.2 t).2 ▸ hr.2⟩

theorem getD_modify {α : Type} (a : Array α) (i j : Nat) (f : α → α) (d : α) :
    (a.modify i f).getD j d = if i = j ∧ j < a.size then f (a.getD j d) else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · simp [hi]
    · simp [hi]
  · simp [hij]

theorem tree_onRow (F : Fork) (t r t' : Nat) (f : HRow → HRow) :
    (onRow F t r f).trees.getD t' {} =
      if t = t' ∧ t' < F.trees.size then
        { F.trees.getD t' {} with rows := (F.trees.getD t' {}).rows.modify r f }
      else F.trees.getD t' {} := getD_modify _ _ _ _ _

theorem frame_onRow (F : Fork) (t r : Nat) (f : HRow → HRow) : Frame F (onRow F t r f) := by
  refine ⟨by simp [onRow], fun t' => ?_⟩
  rw [tree_onRow]
  split
  · exact ⟨rfl, by simp⟩
  · exact ⟨rfl, rfl⟩

theorem rowAt_onRow_ne (F : Fork) {t r t' r' : Nat} (f : HRow → HRow) (h : ¬ (t = t' ∧ r = r')) :
    rowAt (onRow F t r f) t' r' = rowAt F t' r' := by
  unfold rowAt
  rw [tree_onRow]
  split
  · rename_i ht
    show ((F.trees.getD t' {}).rows.modify r f).getD r' {} = _
    rw [getD_modify, if_neg (fun hh => h ⟨ht.1, hh.1⟩)]
  · rfl

theorem rowAt_onRow_eq (F : Fork) {t r : Nat} (f : HRow → HRow) (h : HasRow F t r) :
    rowAt (onRow F t r f) t r = f (rowAt F t r) := by
  unfold rowAt
  rw [tree_onRow, if_pos ⟨rfl, h.1⟩]
  show ((F.trees.getD t {}).rows.modify r f).getD r {} = _
  rw [getD_modify, if_pos ⟨rfl, h.2⟩]

/-! ### loops -/

theorem forIn_foldl {α σ : Type} (step : σ → α → σ) : ∀ (l : List α) (s : σ),
    (forIn l s (fun a r => (pure (ForInStep.yield (step r a)) : Id (ForInStep σ))) : Id σ) =
      l.foldl step s
  | [], _ => rfl
  | a :: l, s => by
    rw [List.forIn_cons]
    exact forIn_foldl step l (step s a)

/-- A row of writes keeps the frame, and leaves alone every place at which none of them writes. -/
theorem foldl_writes {α : Type} (tr ro : α → Nat) (f : Fork → α → HRow → HRow) :
    ∀ (l : List α) (F : Fork),
      Frame F (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F) ∧
      ∀ t e, (∀ a ∈ l, ¬ (tr a = t ∧ ro a = e)) →
        rowAt (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F) t e = rowAt F t e
  | [], F => ⟨Frame.refl F, fun _ _ _ => rfl⟩
  | a :: l, F => by
    obtain ⟨h1, h2⟩ := foldl_writes tr ro f l (onRow F (tr a) (ro a) (f F a))
    refine ⟨(frame_onRow F _ _ _).trans h1, fun t e h => ?_⟩
    show rowAt (l.foldl _ (onRow F (tr a) (ro a) (f F a))) t e = _
    rw [h2 t e fun b hb => h b (List.mem_cons_of_mem _ hb),
      rowAt_onRow_ne F _ (h a List.mem_cons_self)]

/-- In a row of writes at places that differ, each place holds what its own write laid. -/
theorem foldl_last {α : Type} (tr ro : α → Nat) (f : Fork → α → HRow → HRow) (val : α → Array E)
    (I : Fork → Prop) (hI : ∀ F a, I F → I (onRow F (tr a) (ro a) (f F a)))
    (hv : ∀ F a row, I F → (f F a row).coef = val a) :
    ∀ (l : List α) (F : Fork), I F → (l.map fun a => (tr a, ro a)).Nodup →
      ∀ a ∈ l, HasRow F (tr a) (ro a) →
        (rowAt (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F) (tr a) (ro a)).coef = val a
  | [], _, _, _, _, h, _ => by cases h
  | b :: l, F, hF, hn, a, ha, hr => by
    rw [List.map_cons, List.nodup_cons] at hn
    show (rowAt (l.foldl _ (onRow F (tr b) (ro b) (f F b))) (tr a) (ro a)).coef = _
    by_cases hal : a ∈ l
    · exact foldl_last tr ro f val I hI hv l _ (hI F b hF) hn.2 a hal
        ((frame_onRow F _ _ _).hasRow hr)
    · have hab : a = b := by
        rcases List.mem_cons.1 ha with h | h
        · exact h
        · exact absurd h hal
      subst hab
      rw [(foldl_writes tr ro f l _).2 (tr a) (ro a) fun c hc hh =>
        hn.1 (List.mem_map.2 ⟨c, hc, Prod.ext hh.1 hh.2⟩), rowAt_onRow_eq F _ hr]
      exact hv F a _ hF

theorem forIn_inv {α σ : Type} (I : σ → Prop) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ a s, I s → ∃ s', f a s = (pure (ForInStep.yield s') : Id (ForInStep σ)) ∧ I s') :
    ∀ (l : List α) (s : σ), I s → I (forIn l s f : Id σ)
  | [], _, h => h
  | a :: l, s, h => by
    obtain ⟨s', e, h'⟩ := hf a s h
    rw [List.forIn_cons, e]
    exact forIn_inv I f hf l s' h'

/-! ### the stages -/

theorem frame_tables (tl : HTailF2) (F : Fork) : Frame F (coefTables tl F) := by
  unfold coefTables
  refine forIn_inv (Frame F) _ (fun n s hs => ?_) _ _ (Frame.refl F)
  dsimp only
  split
  · split
    · exact ⟨_, rfl, hs.trans (frame_onRow _ _ _ _)⟩
    · exact ⟨_, rfl, hs⟩
  · exact ⟨_, rfl, hs⟩

/-- One piece's write. a: the call's number and the piece. -/
def pieceF (tl : HTailF2) (g : Forest.Heard) (F : Fork) (a : Nat × Piece) (row : HRow) : HRow :=
  formPoint
    { row with coef := pieceW (tl.zOf a.1) (g.zk.getD a.1 #[]) a.2 (F.trees.getD a.2.tree {}).R }
    ((g.zk.getD a.1 #[]).extract ((tl.zOf a.1).call.n - a.2.b)
        ((tl.zOf a.1).call.n - a.2.b + a.2.a))
    a.2.r0

/-- The pieces of the two calls, each with its call's number. -/
def allPieces (tl : HTailF2) : List (Nat × Piece) :=
  (tl.zOf 0).pieces.toList.map (fun p => (0, p)) ++ (tl.zOf 1).pieces.toList.map fun p => (1, p)

theorem coefPieces_eq (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    coefPieces tl g F =
      (allPieces tl).foldl (fun F a => onRow F a.2.tree a.2.row (pieceF tl g F a)) F := by
  have inner : ∀ (q : Nat) (F : Fork),
      (forIn (tl.zOf q).pieces F (fun p r =>
        (pure (ForInStep.yield (onRow r p.tree p.row (pieceF tl g r (q, p)))) :
          Id (ForInStep Fork))) : Id Fork) =
        ((tl.zOf q).pieces.toList.map fun p => (q, p)).foldl
          (fun F a => onRow F a.2.tree a.2.row (pieceF tl g F a)) F := by
    intro q F
    rw [← Array.forIn_toList, List.foldl_map]
    exact forIn_foldl (fun r p => onRow r p.tree p.row (pieceF tl g r (q, p))) _ _
  unfold allPieces
  rw [List.foldl_append, ← inner 0 F, ← inner 1]
  rfl

theorem coefMats_eq (tl : HTailF2) (theta : E) (F : Fork) :
    coefMats tl theta F = (List.range tl.NM).foldl (fun F mu => onRow F (tl.gtTree.getD mu 0) 0
      ((fun _ mu row => formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
        (tl.shp.getD mu {}).mS) F mu)) F :=
  forIn_foldl (fun F mu => onRow F (tl.gtTree.getD mu 0) 0 fun row =>
    formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
      (tl.shp.getD mu {}).mS) _ _

/-- The state behind the routine. -/
def coefAll (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Fork :=
  coefMats tl F.theta (coefBZ tl g (coefPowers tl F.theta (coefPieces tl g (coefTables tl F))))

/-- A run that returns. -/
theorem coefficientsF_ok (tl : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.coefficientsF F c = .ok (((), G), c')) :
    ∃ g, tl.heard = some g ∧ G = coefAll tl g F ∧ c' = c := by
  rw [coefficientsF_eq] at h
  obtain ⟨g, F1, c1, h1, h2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨g', e1, e2⟩ := (get_ok _ F c _).1 h1
  cases e2
  have e3 : (((), coefAll tl g F), c) = (((), G), c') := Except.ok.inj h2
  cases e3
  exact ⟨g, e1, rfl, rfl⟩

theorem frame_pieces (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    Frame F (coefPieces tl g F) := by
  rw [coefPieces_eq]
  exact (foldl_writes (fun a : Nat × Piece => a.2.tree) (fun a => a.2.row) (pieceF tl g) _ F).1

theorem frame_powers (tl : HTailF2) (theta : E) (F : Fork) : Frame F (coefPowers tl theta F) :=
  (frame_onRow _ _ _ _).trans (frame_onRow _ _ _ _)

theorem frame_bz (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Frame F (coefBZ tl g F) :=
  ((frame_onRow _ _ _ _).trans (frame_onRow _ _ _ _)).trans (frame_onRow _ _ _ _)

theorem frame_mats (tl : HTailF2) (theta : E) (F : Fork) : Frame F (coefMats tl theta F) := by
  rw [coefMats_eq]
  exact (foldl_writes (fun mu => tl.gtTree.getD mu 0) (fun _ => 0) _ _ F).1

theorem frame_all (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Frame F (coefAll tl g F) :=
  ((((frame_tables tl F).trans (frame_pieces tl g _)).trans (frame_powers tl _ _)).trans
    (frame_bz tl g _)).trans (frame_mats tl _ _)

theorem rowAt_mats (tl : HTailF2) (theta : E) (F : Fork) (t e : Nat)
    (h : ∀ mu < tl.NM, ¬ (tl.gtTree.getD mu 0 = t ∧ 0 = e)) :
    rowAt (coefMats tl theta F) t e = rowAt F t e := by
  rw [coefMats_eq]
  exact (foldl_writes (fun mu => tl.gtTree.getD mu 0) (fun _ => 0) _ _ F).2 t e
    fun mu hmu => h mu (List.mem_range.1 hmu)

/-- **The declared weights of BZ's three virtual rows.** -/
theorem coef_bz (tl : HTailF2) (g : Forest.Heard) (F : Fork) (h0 : HasRow F tl.ix.BZ 0)
    (h1 : HasRow F tl.ix.BZ 1) (h2 : HasRow F tl.ix.BZ 2)
    (hm : ∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ) :
    (rowAt (coefAll tl g F) tl.ix.BZ 0).coef = eqTab (g.zb0.extract 0 5) ∧
    (rowAt (coefAll tl g F) tl.ix.BZ 1).coef = eqTab (g.zb1.extract 0 5) ∧
    (rowAt (coefAll tl g F) tl.ix.BZ 2).coef = Array.replicate 32 oneE := by
  have fr := ((frame_tables tl F).trans (frame_pieces tl g _)).trans (frame_powers tl F.theta _)
  unfold coefAll
  refine ⟨?_, ?_, ?_⟩
  · rw [rowAt_mats _ _ _ _ _ fun mu hmu hh => hm mu hmu hh.1]
    unfold coefBZ
    rw [rowAt_onRow_ne _ _ (by omega), rowAt_onRow_ne _ _ (by omega),
      rowAt_onRow_eq _ _ (fr.hasRow h0)]
    rfl
  · rw [rowAt_mats _ _ _ _ _ fun mu hmu hh => hm mu hmu hh.1]
    unfold coefBZ
    rw [rowAt_onRow_ne _ _ (by omega),
      rowAt_onRow_eq _ _ ((fr.trans (frame_onRow _ _ _ _)).hasRow h1)]
    rfl
  · rw [rowAt_mats _ _ _ _ _ fun mu hmu hh => hm mu hmu hh.1]
    unfold coefBZ
    rw [rowAt_onRow_eq _ _
      (((fr.trans (frame_onRow _ _ _ _)).trans (frame_onRow _ _ _ _)).hasRow h2)]
    rfl

/-- **The declared weights of a piece's virtual row.** a: the call's number and the piece. -/
theorem coef_piece (tl : HTailF2) (g : Forest.Heard) (F : Fork) (a : Nat × Piece)
    (ha : a ∈ allPieces tl) (hn : ((allPieces tl).map fun a => (a.2.tree, a.2.row)).Nodup)
    (hr : HasRow F a.2.tree a.2.row)
    (hR : ¬ (tl.ix.ZZ = a.2.tree ∧ tl.zzRowReads = a.2.row))
    (hT : ¬ (tl.ix.ZZ = a.2.tree ∧ tl.zzRowTies = a.2.row)) (hB : tl.ix.BZ ≠ a.2.tree)
    (hm : ∀ mu < tl.NM, ¬ (tl.gtTree.getD mu 0 = a.2.tree ∧ 0 = a.2.row)) :
    (rowAt (coefAll tl g F) a.2.tree a.2.row).coef =
      pieceW (tl.zOf a.1) (g.zk.getD a.1 #[]) a.2 (F.trees.getD a.2.tree {}).R := by
  unfold coefAll
  rw [rowAt_mats _ _ _ _ _ hm]
  unfold coefBZ
  rw [rowAt_onRow_ne _ _ (fun h => hB h.1), rowAt_onRow_ne _ _ (fun h => hB h.1),
    rowAt_onRow_ne _ _ (fun h => hB h.1)]
  unfold coefPowers
  rw [rowAt_onRow_ne _ _ hT, rowAt_onRow_ne _ _ hR, coefPieces_eq]
  exact foldl_last (fun a : Nat × Piece => a.2.tree) (fun a => a.2.row) (pieceF tl g)
    (fun a => pieceW (tl.zOf a.1) (g.zk.getD a.1 #[]) a.2 (F.trees.getD a.2.tree {}).R)
    (fun F' => ∀ t, (F'.trees.getD t {}).R = (F.trees.getD t {}).R)
    (fun F' b h t => ((frame_onRow F' _ _ _).2 t).1.trans (h t))
    (fun F' b row h => by
      show pieceW _ _ _ (F'.trees.getD b.2.tree {}).R = _
      rw [h])
    _ _ (fun t => ((frame_tables tl F).2 t).1) hn a ha ((frame_tables tl F).hasRow hr)

end Fo
