-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FourRunsTie.lean: THE HEAD's HALF OF THE EXCHANGE AT THE HEAD's FOUR RUNS
(Law/FourRunsCell.lean's armCellIn_K6) FROM THE TIE OF THE APPROXIMATE RANGE PROOF (TieOf, TieAt:
Johnson/Desc/First/K8/LawItems.lean) at a state of the verifier behind the sub-protocol that makes
the head's tables: that theorem's named premises hTw and hSame are paid here. Statements and
proofs.

WHAT IT IS NOT. Implications. Nothing on soundness. THE TIE IS A PREMISE, and so is hRun (the run's
points and vectors are the kind's letters). The full size alone (FullH and the layers' three
structures of numerals are premises, as of the library's trueH_of_public). No values are shown at
which the premises hold together. THREE PREMISES OF THE TOPS ON THE ARRAYS: hArr (the part's list
of arrays names the reads' array): shown nowhere here · hlab (it names the symbol arrays of the four
ranges' matrices by the matrices' labels) · hride (the cells of these arrays are read alike in the
committed data behind and in front of the sending): brought down by lab_of_calls and ride_of_seated
to sentences that other files name (CallsSeated, MatsSeated, the test laidThere) and
to Rides: these are premises there; the two payers are not called by the tops.

WHY TWO STRUCTURES OF CELLS. The head's arm of the stated data reads the integer cells cellsOfData
(Law/CellsOfData.lean), which are CUT to the four ranges of the head's cells: 0 outside. The tie
speaks of integers at all matrices of the segment, the planes' among them, and the library's map of
cells (Hd.cellsH) walks into the neighbour's matrix beyond a matrix's features. So "the images of
cellsOfData's cells are the tie's entries" (Law/TieReads.lean: CellsAre, over all features) is not
to be had. Here: the twelve tables are worth the reads in truth AT THE UNCUT CELLS of the tie's
integers (tieCells); and these agree with cellsOfData inside the ranges that the head's relation
names (Law/CellsAlike.lean: SameCells): which is all that a read below its length reads
(Law/FourRunsCell.lean: readAt_same, readAtN_same).

  own_of_packs     in a column to whose symbols, read in the data, small integers pack: segment
                   24's own integers made of the data are these.
  sameCells_of_packs   STANDS ALONE (data alone: no witness, no state): see its docstring.
  holds_below      the tie's third clause gives the library's sentence Holds for every table of the
                   closed list, where the world's entries are the tie's cells BELOW THE WIDTH
                   (Law/TieReads.lean's holds_of_tie asks them at all positions).
  ok_of_tables     where the IOP's own text makes the head's tables, the program's routine tablesOf
                   returns them.
  tieCells X tl A  the uncut cells of THE integers behind the symbols that A shows
                   (Johnson/Meaning/PlanesTieK8Cells.lean: cellZ): nothing under "there is".
  twelve_at_tie    TieOf tl A gives TwelveTrue at tieCells.
  packs_in_front   the tie's first two clauses, read in the data in front of the sending.
  cell_wider, ride_of_seated, lab_of_calls   payers of the tops' hride and hlab: see above.
  TablesCome X s s'   A NAMED SENTENCE ON TWO STATES: the closed list behind is the list of the
                   tables that the arm reads in front; the other numbers are the public parameters'.
  tablesCome_of_head   it holds behind an accept of the sub-protocol that makes and closes the list.
                   Of that sub-protocol under a guard or another dress nothing is said here.
  armCellIn_K6_of_tie   MAIN, general in the table of cells: see its docstring.
  armCellIn_K6_at_table   the same at the letters of the composed meaning of the open claims.

LETTERS. No letter stands under "there is" in a conclusion. In hRun: o, cov, x, t: pinned by the
five equations. cU: pinned by hArr. l, piece: read by K6States alone. z: read by the tie alone,
through cellsAt.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.FourRunsCell
import Johnson.Desc.Kinds.Law.HeadCellsMeet
import Johnson.Desc.Kinds.Law.HeadCellsAtCaller
import Johnson.Desc.Kinds.Law.HeadPlanesTie
import Johnson.Road.HeadMade
import Johnson.Desc.Sound.CellsAtName
import Johnson.Desc.Kinds.Law.DataSeatedOfLaid
import Johnson.Desc.Kinds.Law.HeadSymsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf)
open OnBytes.Road (Holds)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.First.K8 (TieOf)
open Meaning.Reads (cellZ TieWith tie_named)
open Norm (lt ls d T)

/-- **In a column to whose symbols, read in the data, small integers pack, segment 24's own
integers made of the data are these.** -/
theorem own_of_packs (X : OnBytes.Model.Verify.Public) (D : Bound K) (a : Nat → Nat → Nat → Int)
    (μ : Fin (Meaning.sizesOf X 24).NM) (c : Fin ((Meaning.sizesOf X 24).k μ))
    (h1 : ∀ i : Fin ((Meaning.sizesOf X 24).m μ),
      |a μ.val i.val c.val| < 2 * ((Meaning.sizesOf X 24).beta : Int))
    (h2 : ∀ i' : Fin (Alg.symRows ((Meaning.sizesOf X 24).m μ)),
      D.cell (Meaning.ownerK (Meaning.labAt X 24 μ.val))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ.val))) i'.val c.val =
        ((Alg.pack ((Meaning.sizesOf X 24).rad : Int)
          (fun i : Fin ((Meaning.sizesOf X 24).m μ) => a μ.val i.val c.val) i' : Int) : K))
    (r : Fin ((Meaning.sizesOf X 24).m μ)) :
    Meaning.ownOf (Meaning.sizesOf X) (symD X (Meaning.sizesOf X) D) 24 μ.val r.val c.val =
      a μ.val r.val c.val := by
  have ha : Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL K (Meaning.sizesOf X 24))
      (symD X (Meaning.sizesOf X) D 24) μ c (fun i => a μ.val i.val c.val) := ⟨h1, h2⟩
  have e := Cb.Pv.Tail.packs_unique (Cb.Pv.Tail.symL K (Meaning.sizesOf X 24)) Cb.Gl.p
    (OnBytes.Tie.Pv.Tail.sizeOf_uniq (Meaning.tlAt X 24)) (fun _ => rfl) ha
    (Cb.Pv.Tail.packs_cellsOf (Cb.Pv.Tail.symL K (Meaning.sizesOf X 24)) ⟨_, ha⟩)
  unfold Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
  rw [dif_pos μ.isLt, dif_pos c.isLt, dif_pos r.isLt]
  exact (congrFun e r).symm

/-- **THE UNCUT CELLS OF SMALL INTEGERS THAT PACK TO THE DATA's SYMBOLS, AND THE HEAD's CELLS MADE
OF THE DATA, AGREE INSIDE THE RANGES THAT THE HEAD's RELATION NAMES.** D: the data; a: integers, one
for each (matrix, row, column). hG: the places of the features that the relation names lie in the
four ranges; hsz: the four ranges lie inside segment 24's sizes; h1, h2: in every column of the four
ranges the integers are small and pack to the symbols that the data hold. -/
theorem sameCells_of_packs [Sizes] [Policy] [Request] [Token] (X : OnBytes.Model.Verify.Public)
    (D : Bound K) (a : Nat → Nat → Nat → Int)
    (hG : InRanges X.hS X.HLy (borderOf X.y))
    (hsz : ∀ μ r c, InFour X.hS X.HLy (borderOf X.y) μ r c →
      μ < (Meaning.sizesOf X 24).NM ∧ c < (Meaning.sizesOf X 24).k μ ∧
        r < (Meaning.sizesOf X 24).m μ)
    (h1 : ∀ (μ : Fin (Meaning.sizesOf X 24).NM) (c : Fin ((Meaning.sizesOf X 24).k μ)),
      ColFour X.hS X.HLy (borderOf X.y) μ.val c.val →
      ∀ i : Fin ((Meaning.sizesOf X 24).m μ),
        |a μ.val i.val c.val| < 2 * ((Meaning.sizesOf X 24).beta : Int))
    (h2 : ∀ (μ : Fin (Meaning.sizesOf X 24).NM) (c : Fin ((Meaning.sizesOf X 24).k μ)),
      ColFour X.hS X.HLy (borderOf X.y) μ.val c.val →
      ∀ i' : Fin (Alg.symRows ((Meaning.sizesOf X 24).m μ)),
        D.cell (Meaning.ownerK (Meaning.labAt X 24 μ.val))
            (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ.val))) i'.val c.val =
          ((Alg.pack ((Meaning.sizesOf X 24).rad : Int)
            (fun i : Fin ((Meaning.sizesOf X 24).m μ) => a μ.val i.val c.val) i' : Int) : K)) :
    SameCells (cellsBack (OnBytes.Road.Hd.cellsH X.hS X.HLy (borderOf X.y) a) fun _ _ => 0)
      (cellsOfData X (Meaning.sizesOf X) D) := by
  have key : ∀ μ r c, InFour X.hS X.HLy (borderOf X.y) μ r c →
      a μ r c = cutM X.hS X.HLy (borderOf X.y)
        (Meaning.ownOf (Meaning.sizesOf X) (symD X (Meaning.sizesOf X) D) 24) μ r c := by
    intro μ r c hin
    obtain ⟨g1, g2, g3⟩ := hsz μ r c hin
    unfold cutM
    rw [if_pos hin]
    exact (own_of_packs X D a ⟨μ, g1⟩ ⟨c, g2⟩ (h1 ⟨μ, g1⟩ ⟨c, g2⟩ (Came.colFour_of_in hin))
      (h2 ⟨μ, g1⟩ ⟨c, g2⟩ (Came.colFour_of_in hin)) ⟨r, g3⟩).symm
  exact ⟨fun f t hf ht => key _ _ _ (hG.wide f t hf ht),
    fun f t hf ht => key _ _ _ (hG.act f t hf ht),
    fun f t hf ht => key _ _ _ (hG.row f t hf ht),
    fun f t hf ht => key _ _ _ (hG.stream f t hf ht), fun _ _ _ _ => rfl⟩

/-- **The tie's third clause gives the library's Holds for every table of the closed list**, where
every place that a table names lies below K3 and the world's entries of row 0 of the reads' array
are the tie's cells below K3. -/
theorem holds_below {tl : HTailF2} {u3 : Nat} {A : Nat → Nat → Nat → K}
    {a : Nat → Nat → Nat → Int} (hT : TieThird tl u3 A a) {W : World K} {iU3 K3 : Nat}
    (hpos : ∀ (n : Nat) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < K3)
    (hW : ∀ pos, pos < K3 → W.entry iU3 0 pos = A u3 0 pos) :
    ∀ Fn ∈ tl.funs, Holds Reading.gl W tl iU3 K3 (fun μ i c => ((a μ i c : Int) : K)) Fn := by
  intro Fn hFn c sg pos hp
  obtain ⟨n, hn⟩ := Array.mem_iff_getElem?.mp hFn
  have hlt := hpos n Fn hn c sg pos hp
  rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hW pos hlt]
  exact hT n Fn hn c sg pos hp

/-- **WHERE THE IOP's OWN TEXT MAKES THE HEAD's TABLES, THE PROGRAM's ROUTINE tablesOf RETURNS
THEM**, from every state and context, which it leaves as they are: step by step, by
Johnson/Desc/Own/HeadTabsAgree.lean's five agreements. -/
theorem ok_of_tables {h : OnBytes.Model.Head.Shape} {L : OnBytes.Model.Head.HL}
    {hp : OnBytes.Model.Head.HPlanH2} {cov : OnBytes.Model.Head.Covered}
    {x : OnBytes.Model.Head.Heard} {t : OnBytes.Model.Head.Tables}
    (e : K8.ReadsQuiet.tables h L hp cov x = .ok t) (F : Fork) (C : OnBytes.Ctx) :
    OnBytes.Road.Hd.Ok (OnBytes.Model.Head.tablesOf h L hp cov x) F C t F C := by
  unfold K8.ReadsQuiet.tables at e
  obtain ⟨_, q0, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨ZV, p1, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨lowN, p2, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨_, q4, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨qFC, p3, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨qROW, p4, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨b0, z0, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨b1, z1, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨t', e3, e⟩ := K8.ReadsQuiet.bind_ok e
  obtain ⟨_, q10, e⟩ := K8.ReadsQuiet.bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  unfold OnBytes.Model.Head.tablesOf
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨(), F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.mustAs_ok _ _ _ _ _).mpr ⟨K8.ReadsQuiet.need_ok q0, rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨ZV, F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.held_ok _ _ _ _).mpr ⟨OnBytes.Road.ok_of_toOption
      ((Own.tailOf_agrees _ _).trans (K8.ReadsQuiet.named_ok p1)), rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨lowN, F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.held_ok _ _ _ _).mpr ⟨OnBytes.Road.ok_of_toOption
      ((Own.cutTail_agrees _ _).trans (K8.ReadsQuiet.named_ok p2)), rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨(), F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.mustAs_ok _ _ _ _ _).mpr ⟨K8.ReadsQuiet.need_ok q4, rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨qFC, F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.getAs_ok _ _ _ _ _).mpr ⟨K8.ReadsQuiet.named_ok p3, rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨qROW, F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.getAs_ok _ _ _ _ _).mpr ⟨K8.ReadsQuiet.named_ok p4, rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨b0, F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.getAs_ok _ _ _ _ _).mpr ⟨(Own.planeWeights_agrees _ _ _).trans
      (K8.ReadsQuiet.named_ok z0), rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨b1, F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.getAs_ok _ _ _ _ _).mpr ⟨(Own.planeWeights_agrees _ _ _).trans
      (K8.ReadsQuiet.named_ok z1), rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨t', F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.getAs_ok _ _ _ _ _).mpr ⟨K8.ReadsQuiet.named_ok e3, rfl⟩, rfl⟩, ?_⟩
  refine (OnBytes.Road.Hd.ok_bind _ _ _ _ _ _ _).mpr ⟨(), F, C,
    (OnBytes.Road.Hd.ok_lift _ _ _ _ _ _).mpr
    ⟨(OnBytes.Road.Hd.mustAs_ok _ _ _ _ _).mpr ⟨K8.ReadsQuiet.need_ok q10, rfl⟩, rfl⟩, ?_⟩
  exact (OnBytes.Road.Hd.ok_pure _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The uncut cells of THE integers behind the symbols that the table of cells A shows at the
symbol arrays of tl. -/
def tieCells (X : OnBytes.Model.Verify.Public) (tl : HTailF2) (A : Nat → Nat → Nat → K) : NCells :=
  cellsBack (OnBytes.Road.Hd.cellsH X.hS X.HLy (borderOf X.y) (cellZ tl A)) fun _ _ => 0

open OnBytes.Road.Hd (FullH) in
open OnBytes.Road (Switches Sized Sized2) in
open OnBytes.Model.Verify (layerShape) in
/-- **THE TIE GIVES THE TWELVE AT THE UNCUT CELLS OF ITS OWN INTEGERS**, at public parameters that
the verifier's own maker returns, at the full size. tl: the approximate range proof's state with
the public parameters' matrices and the closed list of the tables t; W: a world whose entries of
row 0 of the reads' array are A's below K3. -/
theorem twelve_at_tie [Sizes] {pol KL : ByteArray} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hX : publicOf pol KL lay = .ok X) (hF : FullH X.hS)
    (Sw : Switches (layerShape X.P))
    (Z1 : Sized (layerShape X.P) Inst.Model.All.DF)
    (Z2 : Sized2 (layerShape X.P) Inst.Model.All.DF)
    {cov : OnBytes.Model.Head.Covered} {x : OnBytes.Model.Head.Heard}
    {t : OnBytes.Model.Head.Tables} (hmade : K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t)
    {tl : HTailF2} (hm : tl.mats = X.H.tl.mats) (hNM : tl.NM = X.H.tl.NM)
    (hfuns : tl.funs = t.funs) (hix : OnBytes.Tie.Pv.Tail.Port.u3Of tl = readsOf X)
    {A : Nat → Nat → Nat → K} (htie : TieOf tl A) {W : World K} {K3 : Nat}
    (hK : X.H.nU.getD 2 0 ≤ K3)
    (hW : ∀ pos, pos < K3 → W.entry (readsOf X) 0 pos = A (readsOf X) 0 pos)
    (hlt : X.hS.lt = lt) (hls : X.hS.ls = ls) (hla : X.hS.la = ls + lt) :
    TwelveTrue W ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩ K3 (tieCells X tl A) := by
  obtain ⟨_, _, h3⟩ := tie_named htie
  have h3' : TieThird tl (readsOf X) A (cellZ tl A) := by
    rw [← hix]
    exact h3
  have A0 := OnBytes.Road.Hd.publicH_of_public hX
  obtain ⟨H0, hH, e⟩ := A0.plan
  have hH' := holds_below h3' (k6_places_below hmade tl hfuns hm hK) hW
  rw [hfuns] at hH'
  have TT := OnBytes.Road.Hd.trueH_of_holds
    (R := ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩) hH
    (show X.H.tl.mats = H0.tl.mats by rw [e]) (show X.H.tl.NM = H0.tl.NM by rw [e]) hF
    (OnBytes.Road.Hd.numH_of_layout hF A0.head)
    (OnBytes.Road.Hd.borderH_of_layout A0.lay Sw Z1 Z2)
    (ok_of_tables hmade {} { ch := { dry := true, entries := [] } }) hm hNM hH'
  exact Came.twelve_of_trueH
    (Came.cellsAre_int X.hS X.HLy (borderOf X.y) (cellZ tl A) (tieCells X tl A) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl) hlt hls hla TT

/-- **The tie's first two clauses, read in the data in front of the sending.** D: the data in
front; hm, hNM: tl has the public parameters' matrices; hsym: in a column of the four ranges the
symbol that A shows at tl's symbol array of the matrix is the element that the data in front hold
under the matrix's label. -/
theorem packs_in_front (X : OnBytes.Model.Verify.Public) (D : Bound K) {tl : HTailF2}
    (hm : tl.mats = X.H.tl.mats) (hNM : tl.NM = X.H.tl.NM) {A : Nat → Nat → Nat → K}
    (htie : TieOf tl A)
    (hsym : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      A (tl.gtTree.getD μ 0) i' c =
        D.cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c) :
    (∀ (μ : Fin (Meaning.sizesOf X 24).NM) (c : Fin ((Meaning.sizesOf X 24).k μ)),
      ColFour X.hS X.HLy (borderOf X.y) μ.val c.val →
      ∀ i : Fin ((Meaning.sizesOf X 24).m μ),
        |cellZ tl A μ.val i.val c.val| < 2 * ((Meaning.sizesOf X 24).beta : Int)) ∧
    (∀ (μ : Fin (Meaning.sizesOf X 24).NM) (c : Fin ((Meaning.sizesOf X 24).k μ)),
      ColFour X.hS X.HLy (borderOf X.y) μ.val c.val →
      ∀ i' : Fin (Alg.symRows ((Meaning.sizesOf X 24).m μ)),
        D.cell (Meaning.ownerK (Meaning.labAt X 24 μ.val))
            (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ.val))) i'.val c.val =
          ((Alg.pack ((Meaning.sizesOf X 24).rad : Int)
            (fun i : Fin ((Meaning.sizesOf X 24).m μ) => cellZ tl A μ.val i.val c.val) i' : Int) :
            K)) := by
  obtain ⟨g1, g2, _⟩ := tie_named htie
  have em : tl.mats = (Meaning.tlAt X 24).mats := by rw [hm, Came.tlAt_head]
  have eN : tl.NM = (Meaning.tlAt X 24).NM := by rw [hNM, Came.tlAt_head]
  rw [em, eN] at g1 g2
  have eN' : (Meaning.tlAt X 24).NM = X.H.tl.NM := by rw [Came.tlAt_head]
  refine ⟨fun μ c _ i => g1 μ.val μ.isLt c.val c.isLt i.val i.isLt, fun μ c hc i' => ?_⟩
  rw [← hsym μ.val c.val i'.val (eN' ▸ μ.isLt) c.isLt i'.isLt hc]
  exact g2 μ.val μ.isLt c.val c.isLt i'.val i'.isLt

open VerifiableInference.Desc.Sound (dataQ) in
/-- A cell of an array that is seated at a seat of the shorter list is read alike through a longer
list of seats. -/
theorem cell_wider (own own' : List (Nat × Nat)) (hsub : ∀ x ∈ own, x ∈ own') (b : K9.Part)
    (rd : Nat × Nat → Sound.MsgQ) (c : Nat × String) (A : OnBytes.Params.ReqArray) (o : Nat)
    (x : Nat × Nat) (hA : OnBytes.reqArray b.L.check.rows.layout c.1 c.2 = some A)
    (ho : b.L.check.frame.whereIs c.1 A.message = some o)
    (hx : K9.seatAt own b.d.book o = some x) (r i : Nat) :
    (dataQ own' b rd).cell c.1 c.2 r i = (dataQ own b rd).cell c.1 c.2 r i := by
  have hx' : K9.seatAt own' b.d.book o = some x := by
    unfold K9.seatAt at hx ⊢
    obtain ⟨y, h1, hy⟩ := Option.bind_eq_some_iff.1 hx
    rw [h1]
    by_cases hc : own.contains y = true
    · rw [if_pos hc] at hy
      have h2 : own'.contains y = true := by
        simpa using hsub y (by simpa using hc)
      show (if own'.contains y = true then some y else none) = some x
      rw [if_pos h2]
      exact hy
    · rw [if_neg hc] at hy
      cases hy
  have ht : ∀ part, Sound.tabQ own' b.d.st b.d.book rd o part =
      Sound.tabQ own b.d.st b.d.book rd o part := by
    intro part
    funext J
    unfold Sound.tabQ
    rw [hx, hx']
  simp only [Sound.dataQ, K9L.dataOf, hA, ho, ht]

open VerifiableInference.Desc.Sound (dataQ) in
open VerifiableInference.Desc.First (Numbers) in
/-- **A PAYER OF hride**: the cells of the symbol arrays of the four ranges' matrices are read alike
behind, through a longer list of seats, and in front: where the part behind rides on the part in
front (Johnson/Desc/Sound/FormsQ.lean: Rides), the layout lays the matrices' symbols (laidThere) and
the matrices are seated at the state in front (Law/DataSeatedOfLaid.lean: MatsSeated). -/
theorem ride_of_seated (X : OnBytes.Model.Verify.Public) (own own' : List (Nat × Nat))
    (a b : K9.Part) (rd : Nat × Nat → Sound.MsgQ) (hsub : ∀ x ∈ own, x ∈ own')
    (hR : Sound.Rides own a b) (arr : Nat → Nat → Nat) (N : Numbers) (num : Nat → Nat → Nat)
    (lay : OnBytes.Params.ReqLayout)
    (T : Meaning.laidThere X (Meaning.sizesOf X) lay = true)
    (hlay : a.L.check.rows.layout = lay)
    (hM : MatsSeated (ColFour X.hS X.HLy (borderOf X.y)) arr N X own a num lay) :
    ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ own' b rd).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a rd).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c := by
  intro μ c i' hμ hc hi hcol
  have hμ' : μ < (Meaning.sizesOf X 24).NM := by
    show μ < (Meaning.tlAt X 24).NM
    rw [Came.tlAt_head]
    exact hμ
  obtain ⟨A, rp, hA, _, _, _, _⟩ := Meaning.seat_of_laidThere T num (k := 24) (by decide)
    (⟨μ, hμ'⟩ : Fin (Meaning.sizesOf X 24).NM) hi hc
  obtain ⟨o, x, m3, _, m5, _, _⟩ := hM ⟨μ, hμ'⟩ c hc hcol A hA
  subst hlay
  have hAa : OnBytes.reqArray a.L.check.rows.layout
      (Meaning.ownerK (Meaning.labAt X 24 μ), Meaning.nameOf (Meaning.ownerA
        (Meaning.labAt X 24 μ))).1
      (Meaning.ownerK (Meaning.labAt X 24 μ), Meaning.nameOf (Meaning.ownerA
        (Meaning.labAt X 24 μ))).2 = some A := hA
  exact (cell_wider own own' hsub b rd (Meaning.ownerK (Meaning.labAt X 24 μ),
      Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) A o x (by rw [hR.rows]; exact hAa)
      (hR.sent _ _ _ m3) (K9.seatAt_rides own a.d.book b.d.book o x (hR.book o) m5) i' c).trans
    (Sound.cell_rides own a b rd hR (Meaning.ownerK (Meaning.labAt X 24 μ),
      Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) A o x hAa m3 m5 i' c)

open VerifiableInference.Desc.First (Numbers) in
open VerifiableInference.Desc.First.Look (Sent sigListCalls) in
open VerifiableInference.Desc.Sound (Mem) in
/-- **A PAYER OF hlab**: the part's list of arrays names the symbol arrays of the four ranges'
matrices by the matrices' labels: where that list is the written list of link i (hL), the layout
lays the matrices' symbols, and the caller's public letters are tied to the table's
(Law/HeadSymsMeet.lean: CallsSeated: its first clause). -/
theorem lab_of_calls (X : OnBytes.Model.Verify.Public) (a : K9.Part) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (lay : OnBytes.Params.ReqLayout) (num : Nat → Nat → Nat)
    (D : Sent) (rad : OnBytes.OracleShape → Nat) (i : Nat)
    (seatT : Fin (sigListCalls D rad i).length → Nat × Nat)
    (T : Meaning.laidThere X (Meaning.sizesOf X) lay = true)
    (hL : a.L.arrayOf = D.arrayOf.getD i #[])
    (hC : CallsSeated (ColFour X.hS X.HLy (borderOf X.y)) arr msR N X lay num D rad i seatT) :
    ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      a.L.arrayOf[X.H.tl.gtTree.getD μ 0]? = some (Meaning.ownerK (Meaning.labAt X 24 μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) := by
  intro μ c i' hμ hc hi hcol
  have hμ' : μ < (Meaning.sizesOf X 24).NM := by
    show μ < (Meaning.tlAt X 24).NM
    rw [Came.tlAt_head]
    exact hμ
  obtain ⟨A, rp, hA, _, _, _, _⟩ := Meaning.seat_of_laidThere T num (k := 24) (by decide)
    (⟨μ, hμ'⟩ : Fin (Meaning.sizesOf X 24).NM) hi hc
  obtain ⟨_, _, _, _, c1, _⟩ := hC ⟨μ, hμ'⟩ c hc hcol A hA
  rw [hL, ← Came.tlAt_head X]
  exact c1

open VerifiableInference.Desc.First (S HeadOwn) in
/-- **THE TABLES THAT THE ARM READS IN FRONT ARE THOSE THAT STAND BEHIND.** s: the verifier's state
in front of the sub-protocol that makes the head's tables; s': a state behind it. The state of the
approximate range proof at s' has, as its closed list, the tables that the silent step makes at s;
its matrices, their number, the numbers of the arrays of reads and of the symbol arrays are the
public parameters'. -/
def TablesCome (X : OnBytes.Model.Verify.Public) (s s' : S) : Prop :=
  ∀ (e : S) (o : HeadOwn) (t : OnBytes.Model.Head.Tables) (tl : HTailF2),
    withTables (p8K6 X 24) s = some e → e.here = .head o → o.t = some t → s'.tl? = some tl →
      tl.funs = t.funs ∧ tl.mats = X.H.tl.mats ∧ tl.NM = X.H.tl.NM ∧ tl.ix = X.H.tl.ix ∧
        tl.gtTree = X.H.tl.gtTree

open VerifiableInference.Desc.First (S HeadOwn) in
/-- **They come so behind an accept of the sub-protocol that makes and closes the list**, as it is
laid at piece 5 of the head's link. -/
theorem tablesCome_of_head (X : OnBytes.Model.Verify.Public) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (K8.ReadsQuiet.head (p8K6 X 24)).decide s rs gs = .ok s') : TablesCome X s s' := by
  intro e o t tl he ho ht' htl
  obtain ⟨a0, cov0, x0, t0, tl', hs0, hop, hcov, hx0, ht0, hcl, rfl⟩ := K8.ReadsQuiet.head_ok hd
  obtain ⟨_, e2, e3, e4, _, _, _, _, _, e10, e11⟩ := K8.ReadsQuiet.closed_fields hcl
  have htl' : ({ s with here := .head { a0 with t := some t0, tl := tl' } } : S).tl? =
      some tl' := by
    simp [S.tl?, hop]
  obtain rfl : tl' = tl := Option.some.inj (htl'.symm.trans htl)
  have e0 : withTables (p8K6 X 24) s = some { s with here := .head { a0 with t := some t0 } } :=
    (withTables_iff _ _ _).2 ⟨a0, cov0, x0, t0, hs0, hop, hcov, hx0, ht0, rfl⟩
  obtain rfl := Option.some.inj (e0.symm.trans he)
  have ho' : ({ a0 with t := some t0 } : HeadOwn) = o := by
    simpa using ho
  subst ho'
  obtain rfl : t0 = t := Option.some.inj ht'
  exact ⟨e2, e4, e3, e11, e10⟩

open OnBytes.Road.Hd (FullH) in
open OnBytes.Road (Switches Sized Sized2) in
open OnBytes.Model.Verify (layerShape) in
open VerifiableInference.Desc.First (S HeadOwn) in
open VerifiableInference.Desc.K9 (Readers RunOf) in
open VerifiableInference.Desc.Sound (worldOwn dataQ) in
/-- **THE HEAD's HALF OF THE EXCHANGE AT THE HEAD's FOUR RUNS, FROM THE TIE.** s, a: the
verifier's state in front of the sub-protocol that makes the head's tables, and its part; s', b:
a state behind it, at which the tables stand (hCome), and a part. Where the tie of the approximate
range proof holds at s' at a table of cells A w (htie) that reads the arrays by their names in the
committed data behind (hA); the run's points and vectors are the kind's letters (hRun); the symbol
arrays of the four ranges' matrices bear the matrices' labels in the part's list (hlab) and their
cells are read alike behind and in front (hride): at every entry that a form of one of the four
runs names, the committed cell is uHeadK6 X 24 at the state in front. -/
theorem armCellIn_K6_of_tie {pol KL : ByteArray} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hX : publicOf pol KL lay = .ok X) (hF : FullH X.hS)
    (Sw : Switches (layerShape X.P)) (Z1 : Sized (layerShape X.P) Inst.Model.All.DF)
    (Z2 : Sized2 (layerShape X.P) Inst.Model.All.DF)
    (hG : @InRanges (parOf X.hS (workOf X)).sizes X.hS X.HLy (borderOf X.y))
    (hsz : ∀ μ r c, InFour X.hS X.HLy (borderOf X.y) μ r c →
      μ < (Meaning.sizesOf X 24).NM ∧ c < (Meaning.sizesOf X 24).k μ ∧
        r < (Meaning.sizesOf X 24).m μ)
    (l piece blk : Nat) (states : Nat → List (RunOf S))
    (KS : K6States X.hS (readsOf X) (parOf X.hS (workOf X)) l piece states blk)
    (Rd : Readers) (own own' : List (Nat × Nat)) (s s' : S) (a b : K9.Part)
    (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent (p8K6 X 24) states blk name s)
    (hok : (parOf X.hS (workOf X)).ok = true)
    (hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → X.H.nU.getD 2 0 ≤ tr.K)
    (hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩))
    (hCome : TablesCome X s s')
    {Wt : Type} (A : Wt → Nat → Nat → Nat → K) (w : Wt) (htie : First.K8.TieAt A s' w)
    (hA : ∀ t c r i, b.L.arrayOf[t]? = some c → A w t r i = (dataQ own' b rdW).cell c.1 c.2 r i)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf X]? = some cU)
    (hlab : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      a.L.arrayOf[X.H.tl.gtTree.getD μ 0]? = some (Meaning.ownerK (Meaning.labAt X 24 μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))))
    (hride : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ own' b rdW).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a rdW).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c)
    (name : String) (hn : K6Name name) :
    Sound.ArmCellIn Rd own own' blk name s a b rdW (uHeadK6 X 24) := by
  obtain ⟨tl, htl, ht⟩ := htie
  have hla : X.hS.la = X.hS.ls + X.hS.lt := by
    show X.hS.la = X.hS.la - X.hS.lt + X.hS.lt
    rw [hF.la, hF.lt]
  have sizes : ∀ e v, lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      v.1.sizes = (parOf X.hS (workOf X)).sizes := by
    intro e v hv
    obtain ⟨_, _, k1, _⟩ := lettersAt_ok X.hS (readsOf X) (parOf X.hS (workOf X)) hv
    obtain ⟨z, y', hgf⟩ := given_form k1
    rw [hgf]
  refine armCellIn_K6 X l piece blk states KS Rd own own' s a b rdW hRd hok hT hbare harr hwide
    hla (tieCells X tl (A w)) hRun ?_ ?_ name hn
  · intro e v o cov x t F tr he hv ho _ _ ht' hmade hFk htr
    obtain ⟨e2, e4, e3, e11, _⟩ := hCome e o t tl he ho ht' htl
    have hix : OnBytes.Tie.Pv.Tail.Port.u3Of tl = readsOf X := by
      unfold OnBytes.Tie.Pv.Tail.Port.u3Of
      rw [e11]
      rfl
    have hsv := sizes _ v hv
    letI := v.1
    refine twelve_at_tie hX hF Sw Z1 Z2 hmade e4 e3 e2 hix ht (hwide _ F tr he hFk htr)
      (fun pos _ => ?_) ?_ ?_ ?_
    · show (match b.L.arrayOf[readsOf X]? with
        | some q => (dataQ own' b rdW).cell q.1 q.2 0 pos
        | none => 0) = _
      rw [harr, hArr]
      exact (hA _ cU 0 pos (by rw [harr]; exact hArr)).symm
    · show X.hS.lt = v.1.sizes.lt
      rw [hsv]
      rfl
    · show X.hS.ls = v.1.sizes.ls
      rw [hsv]
      rfl
    · show X.hS.la = v.1.sizes.ls + v.1.sizes.lt
      rw [hsv]
      exact hla
  · intro e v he hv
    obtain ⟨o, _, _, t, ho, _, _, ht', _, _⟩ := hRun e v he hv
    obtain ⟨_, e4, e3, _, e10⟩ := hCome e o t tl he ho ht' htl
    have hsv := sizes e v hv
    obtain ⟨p1, p2⟩ := packs_in_front X (dataQ own a rdW) e4 e3 ht fun μ c i' hμ hk hi hc => by
      rw [e10, hA _ _ i' c (by rw [harr]; exact hlab μ c i' hμ hk hi hc)]
      exact hride μ c i' hμ hk hi hc
    letI := v.1
    exact sameCells_of_packs X _ _ (hsv.symm ▸ hG) hsz p1 p2

open OnBytes.Road.Hd (FullH) in
open OnBytes.Road (Switches Sized Sized2) in
open OnBytes.Model.Verify (layerShape) in
open VerifiableInference.Desc.First (S Numbers) in
open VerifiableInference.Desc.K9 (Readers RunOf) in
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab) in
/-- **THE SAME AT THE LETTERS OF THE COMPOSED MEANING OF THE OPEN CLAIMS**: the tie reads the
witness through cellsAt (Johnson/Desc/Sound/CellsAt.lean) at segment m and the state behind; the
committed data behind are read at segment m's group, through seatTab; b is the part of the state
behind. The premise hA is paid by Johnson/Desc/Sound/CellsAtName.lean's cellsAt_name. -/
theorem armCellIn_K6_at_table {pol KL : ByteArray} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hX : publicOf pol KL lay = .ok X) (hF : FullH X.hS)
    (Sw : Switches (layerShape X.P)) (Z1 : Sized (layerShape X.P) Inst.Model.All.DF)
    (Z2 : Sized2 (layerShape X.P) Inst.Model.All.DF)
    (hG : @InRanges (parOf X.hS (workOf X)).sizes X.hS X.HLy (borderOf X.y))
    (hsz : ∀ μ r c, InFour X.hS X.HLy (borderOf X.y) μ r c →
      μ < (Meaning.sizesOf X 24).NM ∧ c < (Meaning.sizesOf X 24).k μ ∧
        r < (Meaning.sizesOf X 24).m μ)
    (l piece blk : Nat) (states : Nat → List (RunOf S))
    (KS : K6States X.hS (readsOf X) (parOf X.hS (workOf X)) l piece states blk)
    (Rd : Readers) (own : List (Nat × Nat)) (s s' : S) (a b : K9.Part)
    {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (ms : List Mem)
    (N : Numbers) (m : Nat) (z : P) (w : Wit Cells Tok MsgT)
    (hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent (p8K6 X 24) states blk name s)
    (hok : (parOf X.hS (workOf X)).ok = true)
    (hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → X.H.nU.getD 2 0 ≤ tr.K)
    (hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩))
    (hCome : TablesCome X s s') (hb : K9.segAt? s' = some b)
    (htie : First.K8.TieAt (cellsAt cs arr ms N m (z, s')) s' w)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf X]? = some cU)
    (hlab : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      a.L.arrayOf[X.H.tl.gtTree.getD μ 0]? = some (Meaning.ownerK (Meaning.labAt X 24 μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))))
    (hride : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ (N.group m) b (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c)
    (name : String) (hn : K6Name name) :
    Sound.ArmCellIn Rd own (N.group m) blk name s a b (seatTab cs arr ms w) (uHeadK6 X 24) :=
  armCellIn_K6_of_tie hX hF Sw Z1 Z2 hG hsz l piece blk states KS Rd own (N.group m) s s' a b
    (seatTab cs arr ms w) hRd hok hT hbare harr hwide hRun hCome (cellsAt cs arr ms N m (z, s')) w
    htie (fun t c r i hc => Sound.cellsAt_name cs arr ms N m z s' w b hb t c hc r i) cU hArr hlab
    hride name hn

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.armCellIn_K6_at_table
#print axioms VerifiableInference.Desc.Kinds.Head.Law.cell_wider
#print axioms VerifiableInference.Desc.Kinds.Head.Law.ride_of_seated
#print axioms VerifiableInference.Desc.Kinds.Head.Law.lab_of_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tablesCome_of_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.armCellIn_K6_of_tie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.own_of_packs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sameCells_of_packs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.holds_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.ok_of_tables
#print axioms VerifiableInference.Desc.Kinds.Head.Law.twelve_at_tie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.packs_in_front
