-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/FullIsLayInScope.lean

Two terms for the matrices of cells of the model's run are one, for public files in the goals' scope
and off the planes: the trace "trFull" (Johnson/HonestTrace/Full.lean) and the laying by formula
"lay" at the reference numbers (Johnson/HonestTrace/Places.lean). This file states no goal.

The two terms. "trFull X pl i x" goes by numbers: sub-proof's number, number in the list, row,
column. It lays the library's honest cells "honAt X i x" by "Cm.Seg.toMat", which picks the name at
a place by choice, reads the result back into the lists, and cuts it to the shapes of the plans that
the verifier's "publicOf" returns in X. "lay S Y" goes by names: segment, matrix's name, row,
column. It reads a source Y of cells through "Sz.nameAt", a formula on the numbers S of a parameter
file, typed by hand for the full-size example as "Sz.ref"; it reads no X. "The verifier" is, in this
file, the verifier of OnBytes/Model/ ("OnBytes.Model.Verify").

The three premises. "In scope" means: "VerifierAndGoals.InScope Z = true" (see its definition in Ladder.lean),
"VerifierAndGoals.readFiles Z = .ok pp", and "publicOf Z.pol Z.KL ly = .ok X".

Main theorems:
* "trFull_eq_lay_in_scope": in scope, for every pl, index, request and counts m, every segment σ of
  a proof with 12 groups and every name μ that has the number a in σ's list and is not the name of
  σ's planes, at all rows and columns: trFull X pl i x (σ.no 12) a r c = lay Sz.ref ⟨honAt X i x, m⟩
  σ μ r c.
* "byName_eq_lay_in_scope": so the trace read by names, "byName X (trFull X pl i x)", is "lay" at
  every segment and every name but the segment's planes'.
* "trFull_eq_lay_core": the first under "publicOf" returns X and "Hd.PublicCore X.P".
* "ff_sizes", "kAs_core": in numerals, the rows and columns of the six matrices of a group other
  than the planes, and the 7,200 columns of "as".
* "own_cell": the step for one own matrix, at any X: if the plan's entry has the rows and columns of
  "Sz.ref.shape" and the list reads the matrix's slot of the library's matrix.
Helpers: "inShape_iff", "shape_of_mu", "mu_ref", "ff_own", "ff_all", "att_all", "head_all",
"lay_of_mu_none".

How it goes. For an own matrix: the plan's rows and columns are those of "Sz.ref.shape", in
numerals; inside them both terms are the same entry of "Cm.Seg.toMat" ("lay_ref_toMat",
Johnson/HonestTrace/PlacesAtRef.lean; the slots of "Hd.zOf" and "zsOf"); outside them both are 0. A
borrowed matrix is its owner's on both sides ("borrowed_core", FullInScope.lean in this folder;
"lay_owner", Johnson/HonestTrace/PlacesBack.lean).

Limits. All is at the reference model's sizes. The planes (b, bA, bH) are left out: there "trFull"
is pl inside the plan's shape and "lay" is a binary digit of m inside "Sz.ref.shape", and this file
does not compare these two shapes. Every statement in scope is an implication from "publicOf ... =
.ok X"; that it returns at the stored full-size files is known in this library by an evaluation
("#guard", Johnson/Goal/Meaning/ScopeRun.lean). The request need not be served: the equations hold
at every index and request. "Sz.ref" is typed by hand; that its numbers are the parameter file's is
shown here only as far as the shapes of the matrices of cells go.

Not claimed: that a prover's committed cells are either term; anything on a proof. The program does
not import this file.

-/
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.HonestTrace.PlacesAtRef

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)
open Cb.Pv.Tail (Size)
open Meaning

/-! ## One own matrix -/

/-- If a is a number of the plan's list of sub-proof k and entry a has R rows and Kc columns, a
place (a, r, c) is inside the shape exactly if r < R and c < Kc. -/
theorem inShape_iff {X : Model.Verify.Public} {k a R Kc : ℕ} (hs : a < (planMats X k).size)
    (hm : ((planMats X k).getD a {}).m = R) (hk : ((planMats X k).getD a {}).k = Kc) (r c : ℕ) :
    InShape X k a r c ↔ r < R ∧ c < Kc := by
  unfold InShape
  rw [hm, hk]
  exact ⟨fun H => H.2, fun H => ⟨hs, H⟩⟩

/-- **One own matrix of cells**, at any X. If σ owns μ and μ holds no planes ("ownsCells"), "Sz.ref"
gives μ the shape (R, Kc), entry a of X's plan of sub-proof σ.no 12 has R rows and Kc columns and is
not the planes', and the list without planes and cut reads at (a, r, c) the entry of the library's
matrix of the honest cells at row 65,536 slot(μ) + r and column c: then the trace at number a is
"lay" at μ, at all rows and columns, whatever pl and the counts m are. -/
theorem own_cell (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref)
    (m : Seg → ℕ → ℕ → ℕ) {σ : Seg} {μ : MatName} {a R Kc : ℕ} (ho : ownsCells σ μ = true)
    (hsh : Sz.ref.shape σ μ = (R, Kc)) (hs : a < (planMats X (σ.no 12)).size)
    (hm : ((planMats X (σ.no 12)).getD a {}).m = R)
    (hk : ((planMats X (σ.no 12)).getD a {}).k = Kc) (hb : a ≠ bNo X (σ.no 12))
    (hl : ∀ r c, listsOf X (honMx X i x) (σ.no 12) a r c =
      honMx X i x (σ.no 12) (slot μ * 65536 + r) c) (r c : ℕ) :
    trFull X pl i x (σ.no 12) a r c = lay Sz.ref ⟨honAt X i x, m⟩ σ μ r c := by
  by_cases H : r < R ∧ c < Kc
  · rw [trFull_cells X pl i x ((inShape_iff hs hm hk r c).2 H) hb, hl,
      lay_ref_toMat ⟨honAt X i x, m⟩ σ μ r c ho (by rw [hsh]; exact H.1) (by rw [hsh]; exact H.2)]
    rfl
  · rw [trFull_out X pl i x fun I => H ((inShape_iff hs hm hk r c).1 I),
      lay_off Sz.ref _ σ μ r c (by rw [hsh]; exact H)]

section Core
variable {pol KL : ByteArray} {ly : Option ByteArray} {X : Model.Verify.Public}

/-! ## The plans' rows and columns, in numerals -/

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds: in the layers' layout a part of af has
65,536 rows and 5,990 columns, ad 32,768 and 3,200, ar 8,192 and 324, qa 65,536 and 1,536, and each
of the two streams 65,536 and 400. -/
theorem ff_sizes (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) :
    (rowsM X.y 0 = 65536 ∧ colsM X.y 0 = 5990) ∧ (rowsM X.y 1 = 32768 ∧ colsM X.y 1 = 3200) ∧
    (rowsM X.y 2 = 8192 ∧ colsM X.y 2 = 324) ∧ (rowsM X.y 3 = 65536 ∧ colsM X.y 3 = 1536) ∧
    (rowsM X.y 4 = 65536 ∧ colsM X.y 4 = 400) ∧ (rowsM X.y 5 = 65536 ∧ colsM X.y 5 = 400) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨e, -⟩ := laid_of_layout B.lay B.switches.p3
  have S' : Switches X.y.h := by rw [e]; exact B.switches
  have Z' : Sized X.y.h DF := by rw [e]; exact B.sized
  have Z2' : Sized2 X.y.h DF := by rw [e]; exact B.sized2
  have p4 : X.y.h.p4 = true := by rw [e]; exact B.p4
  have L2 := laid2_of_layout B.lay
  obtain ⟨-, c1, c2, c3, c4, c5⟩ := nCol_eq L2 S' Z' Z2'
  obtain ⟨s0, -, s1, s2, -, s3, s4, s5, -⟩ := Inst.Model.FFSeg.ref_shapes
  exact ⟨⟨(rowsM_eq L2 Z' Z2' (μ := .af) (by decide)).trans (by decide),
      (afCols_eq L2 S' Z' Z2').trans s0⟩,
    ⟨(rowsM_eq L2 Z' Z2' (μ := .ad) (by decide)).trans (by decide), c1.trans s1⟩,
    ⟨(rowsM_eq L2 Z' Z2' (μ := .ar) (by decide)).trans (by decide), c2.trans s2⟩,
    ⟨(rowsM_eq L2 Z' Z2' (μ := .qa) (by decide)).trans (by decide), (c3 p4).trans s3⟩,
    ⟨(rowsM_eq L2 Z' Z2' (μ := .xin) (by decide)).trans (by decide), c4.trans s4⟩,
    ⟨(rowsM_eq L2 Z' Z2' (μ := .xout) (by decide)).trans (by decide), c5.trans s5⟩⟩

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds: for g < 12 the matrix "as" of group g's
attention shape has 7,200 columns, all parts together. -/
theorem kAs_core (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12) :
    (Hd.shapeA X g).kAs = 7200 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have F := Hd.fillRef_of_core C B
  obtain ⟨-, -, n1, -⟩ := matsAt_att_gid h C hg
  obtain ⟨lines, A0, seenG, seenA, -, H⟩ := Hd.groups_of_public h B.p4
  obtain ⟨Xg, Ag, s, hG, -, -, -, -, -, -, -, eS⟩ := H g (by rw [B.groups]; exact hg)
  obtain ⟨cf, hf, hp, -⟩ := group_plan hG
  obtain ⟨hc, -, -, -⟩ := cfRef_of_fill hf F
  have P := shaped_of_hid (plan_shape hp).1
  rw [eS] at n1 ⊢
  rw [P.cfg] at n1
  rw [P.kAs]
  simp [Attention.nMOf, Attention.nDOf, hc.ll, hc.H, hc.lgk, hc.lt, hc.lB, hc.lmS, n1]

/-! ## Shapes and numbers at the reference numbers -/

/-- At the reference numbers the shape of a matrix that has a number in the segment's list is its
rows and its columns. -/
theorem shape_of_mu {σ : Seg} {μ : MatName} {a R Kc : ℕ} (hμ : Sz.ref.mu σ μ = some a)
    (hR : Sz.ref.rows μ = R) (hK : Sz.ref.k σ μ = Kc) : Sz.ref.shape σ μ = (R, Kc) := by
  unfold Sz.shape
  rw [hμ, hR, hK]
  rfl

/-- "Sz.mu" at a segment of the proof is "MatName.no?" at 3, 1, 1, 4. -/
theorem mu_ref {σ : Seg} (hσ : σ.Below 12) (μ : MatName) :
    Sz.ref.mu σ μ = MatName.no? 3 1 1 4 σ μ := if_pos hσ

/-! ## The feed-forward segments -/

/-- One own matrix of cells of group g < 12, if "publicOf" returns X and "Hd.PublicCore X.P" holds:
"own_cell" with its premises paid from the layout's rows and columns of part p of the matrix number
mat, which has the number a in the list and fills slot t of the library's matrix. -/
theorem ff_own (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) (pl : ℕ → ℕ → ℕ → ℤ)
    (i : Cm.Idx) (x : Instance ppref) (m : Seg → ℕ → ℕ → ℕ) {g : ℕ} (hg : g < 12) {μ : MatName}
    {a t mat p R Kc : ℕ} (ho : ownsCells (.ff g) μ = true)
    (hμ : MatName.no? 3 1 1 4 (.ff g) μ = some a)
    (hR' : Sz.ref.rows μ = R) (hK' : Sz.ref.k (.ff g) μ = Kc) (hmat : mat ≤ 5)
    (hp : p < partsM X.y mat) (ea : firstM X.y mat + p = a) (hR : rowsM X.y mat = R)
    (hK : colsM X.y mat = Kc) (ht : t < 8) (es : Hd.slotNo X.y t = a) (h6 : t = 6 → g = 0)
    (et : slot μ = t) (ha9 : a < 9) (hb : a ≠ 5) (r c : ℕ) :
    trFull X pl i x (2 * g) a r c = lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) μ r c := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  refine own_cell X pl i x m (σ := .ff g) ho
    (shape_of_mu ((mu_ref (σ := .ff g) hg μ).trans hμ) hR' hK') ?_ ?_ ?_ ?_ ?_ r c
  · show a < (planMats X (2 * g)).size
    rw [planMats_eq, size_even h C hg]
    exact ha9
  · show ((planMats X (2 * g)).getD a {}).m = R
    rw [planMats_eq, ← ea, (entry_eq h C hg hmat hp).1, hR]
  · show ((planMats X (2 * g)).getD a {}).k = Kc
    rw [planMats_eq, ← ea, (entry_eq h C hg hmat hp).2, hK]
  · show a ≠ bNo X (2 * g)
    rw [bNo_even X hg]
    show a ≠ X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1
    rw [p0, p1]
    exact hb
  · intro r c
    show listsOf X (honMx X i x) (2 * g) a r c = honMx X i x (2 * g) (slot μ * 65536 + r) c
    rw [(listsOf_eq_true X i x).1 g hg]
    show Hd.zOf (honMx X i x) (labA X.y g a) r c = _
    rw [← es, Hd.zOf_slot p0 p1 _ hg ht h6 r c, et]

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds, for g < 12, every pl, index, request and
counts m, at all rows and columns: the trace's numbers 0, 1, 2 | 3 | 4 | 6 | 7 of sub-proof 2 g are
"lay" at the three parts of af | ad | ar | qa | xbO of the feed-forward segment of group g; and in
group 0 number 8 is "lay" at xbI. -/
theorem ff_all (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) (pl : ℕ → ℕ → ℕ → ℤ)
    (i : Cm.Idx) (x : Instance ppref) (m : Seg → ℕ → ℕ → ℕ) {g : ℕ} (hg : g < 12) :
    (∀ p < 3, ∀ r c, trFull X pl i x (2 * g) p r c =
      lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) (.af p) r c) ∧
    (∀ r c, trFull X pl i x (2 * g) 3 r c = lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) (.ad 0) r c) ∧
    (∀ r c, trFull X pl i x (2 * g) 4 r c = lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) .ar r c) ∧
    (∀ r c, trFull X pl i x (2 * g) 6 r c = lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) .qa r c) ∧
    (∀ r c, trFull X pl i x (2 * g) 7 r c = lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) .xbO r c) ∧
    (g = 0 → ∀ r c, trFull X pl i x (2 * g) 8 r c =
      lay Sz.ref ⟨honAt X i x, m⟩ (.ff g) .xbI r c) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨⟨r0, c0⟩, ⟨r1, c1⟩, ⟨r2, c2⟩, ⟨r3, c3⟩, ⟨r4, c4⟩, ⟨r5, c5⟩⟩ := ff_sizes h C
  have e4 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 = 4 := by rw [p0, p1]
  have e6 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6 := by rw [p0, p1]
  have e7 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7 := by rw [p0, p1]
  have e8 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8 := by rw [p0, p1]
  refine ⟨fun p hp => ?_, ?_, ?_, ?_, ?_, fun g0 => ?_⟩
  · have c3' : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases c3' with rfl | rfl | rfl
    · exact ff_own h C pl i x m hg (μ := .af 0) (t := 0) (mat := 0) (p := 0) rfl rfl rfl (kF_af 0)
        (by norm_num) (by show 0 < X.y.parts.getD 0 0; omega) rfl r0 c0 (by norm_num) rfl
        (by norm_num) rfl (by norm_num) (by norm_num)
    · exact ff_own h C pl i x m hg (μ := .af 1) (t := 1) (mat := 0) (p := 1) rfl rfl rfl (kF_af 1)
        (by norm_num) (by show 1 < X.y.parts.getD 0 0; omega) rfl r0 c0 (by norm_num) rfl
        (by norm_num) rfl (by norm_num) (by norm_num)
    · exact ff_own h C pl i x m hg (μ := .af 2) (t := 2) (mat := 0) (p := 2) rfl rfl rfl (kF_af 2)
        (by norm_num) (by show 2 < X.y.parts.getD 0 0; omega) rfl r0 c0 (by norm_num) rfl
        (by norm_num) rfl (by norm_num) (by norm_num)
  · exact ff_own h C pl i x m hg (μ := .ad 0) (t := 3) (mat := 1) (p := 0) rfl rfl rfl (kF_ad 0)
      (by norm_num) (by show 0 < X.y.parts.getD 1 0; omega) p0 r1 c1 (by norm_num) p0
      (by norm_num) rfl (by norm_num) (by norm_num)
  · exact ff_own h C pl i x m hg (μ := .ar) (t := 4) (mat := 2) (p := 0) rfl rfl rfl kF_ar
      (by norm_num) Nat.one_pos e4 r2 c2 (by norm_num) e4 (by norm_num) rfl (by norm_num)
      (by norm_num)
  · exact ff_own h C pl i x m hg (μ := .qa) (t := 5) (mat := 3) (p := 0) rfl rfl rfl kF_qa
      (by norm_num) Nat.one_pos e6 r3 c3 (by norm_num) e6 (by norm_num) rfl (by norm_num)
      (by norm_num)
  · exact ff_own h C pl i x m hg (μ := .xbO) (t := 7) (mat := 5) (p := 0) rfl rfl rfl kF_xbO
      (by norm_num) Nat.one_pos e7 r5 c5 (by norm_num) e7 (by norm_num) rfl (by norm_num)
      (by norm_num)
  · subst g0
    exact ff_own h C pl i x m hg (μ := .xbI) (t := 6) (mat := 4) (p := 0) rfl rfl rfl kF_xbI
      (by norm_num) Nat.one_pos e8 r4 c4 (by norm_num) e8 (fun _ => rfl) rfl (by norm_num)
      (by norm_num)

/-! ## The attention segments -/

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds, for g < 12, every pl, index, request and
counts m, at all rows and columns: the trace's numbers 0 | 1 | 2 of sub-proof 2 g + 1 are "lay" at
as | ah | ao of the attention segment of group g. -/
theorem att_all (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) (pl : ℕ → ℕ → ℕ → ℤ)
    (i : Cm.Idx) (x : Instance ppref) (m : Seg → ℕ → ℕ → ℕ) {g : ℕ} (hg : g < 12) :
    (∀ r c, trFull X pl i x (2 * g + 1) 0 r c =
      lay Sz.ref ⟨honAt X i x, m⟩ (.att g) (.as 0) r c) ∧
    (∀ r c, trFull X pl i x (2 * g + 1) 1 r c = lay Sz.ref ⟨honAt X i x, m⟩ (.att g) .ah r c) ∧
    (∀ r c, trFull X pl i x (2 * g + 1) 2 r c = lay Sz.ref ⟨honAt X i x, m⟩ (.att g) .ao r c) := by
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  have hS := E.2.1 g hg
  obtain ⟨-, -, n1, -⟩ := matsAt_att_gid h C hg
  have PS := planSizes_of_follows h C (follows_sizesAt X 0 0) hg
  obtain ⟨fH, fO, -⟩ := fills_eq_of_core h C g hg
  have kA := kAs_core h C hg
  have gen : ∀ {μ : MatName} {a R Kc : ℕ}, ownsCells (.att g) μ = true →
      MatName.no? 3 1 1 4 (.att g) μ = some a → Sz.ref.rows μ = R → Sz.ref.k (.att g) μ = Kc →
      a < 3 → (sizesAt X 0 0 (2 * g + 1)).m a = R → (sizesAt X 0 0 (2 * g + 1)).k a = Kc →
      slot μ = a → ∀ r c, trFull X pl i x (2 * g + 1) a r c =
        lay Sz.ref ⟨honAt X i x, m⟩ (.att g) μ r c := by
    intro μ a R Kc ho hμ hR' hK' ha hm hk et r c
    refine own_cell X pl i x m (σ := .att g) ho
      (shape_of_mu ((mu_ref (σ := .att g) hg μ).trans hμ) hR' hK') ?_ ?_ ?_ ?_ ?_ r c
    · show a < (planMats X (2 * g + 1)).size
      rw [planMats_eq, size_odd h C hg]
      omega
    · show ((planMats X (2 * g + 1)).getD a {}).m = R
      rw [planMats_eq]
      exact hm
    · show ((planMats X (2 * g + 1)).getD a {}).k = Kc
      rw [planMats_eq]
      exact hk
    · show a ≠ bNo X (2 * g + 1)
      rw [bNo_odd, n1]
      omega
    · intro r c
      show listsOf X (honMx X i x) (2 * g + 1) a r c =
        honMx X i x (2 * g + 1) (slot μ * 65536 + r) c
      rw [(listsOf_eq_true X i x).2.1 g]
      show zsOf (Hd.shapeA X g) g (honMx X i x) a r c = _
      rw [zsOf_own1 n1 g _ ha, et]
  refine ⟨gen (μ := .as 0) rfl rfl rfl (kF_as 0) (by norm_num) ?_ ?_ rfl,
    gen (μ := .ah) rfl rfl rfl kF_ah (by norm_num) ?_ ?_ rfl,
    gen (μ := .ao) rfl rfl rfl kF_ao (by norm_num) ?_ ?_ rfl⟩
  · rw [PS.asM 0 (by omega), hS.lmS]
    rfl
  · rw [PS.asK 0 (by omega), kA, n1]
  · have e := PS.ahM
    rw [n1, hS.wcH, hS.T] at e
    exact e
  · have e := PS.ahK
    rw [n1, fH, hS.wcH] at e
    exact e
  · have e := PS.aoM
    rw [n1, hS.wcO, hS.T] at e
    exact e
  · have e := PS.aoK
    rw [n1, fO, hS.wcO] at e
    exact e

/-! ## The head -/

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds, for every pl, index, request and counts
m, at all rows and columns: the trace's numbers 0 to 3 | 4 | 5 of sub-proof 24 are "lay" at the four
parts of hf | hd | hr of the head. -/
theorem head_all (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) (pl : ℕ → ℕ → ℕ → ℤ)
    (i : Cm.Idx) (x : Instance ppref) (m : Seg → ℕ → ℕ → ℕ) :
    (∀ p < 4, ∀ r c, trFull X pl i x 24 p r c = lay Sz.ref ⟨honAt X i x, m⟩ .head (.hf p) r c) ∧
    (∀ r c, trFull X pl i x 24 4 r c = lay Sz.ref ⟨honAt X i x, m⟩ .head .hd r c) ∧
    (∀ r c, trFull X pl i x 24 5 r c = lay Sz.ref ⟨honAt X i x, m⟩ .head .hr r c) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have N := Hd.numH_of_layout B.full B.head
  obtain ⟨q1, q2, q3, -⟩ := head_in h C (follows_sizesAt X 0 0)
  rw [N.NHf] at q1 q2 q3
  have gen : ∀ {μ : MatName} {a R Kc : ℕ}, ownsCells .head μ = true →
      MatName.no? 3 1 1 4 .head μ = some a → Sz.ref.rows μ = R → Sz.ref.k .head μ = Kc →
      a < 6 → (sizesAt X 0 0 24).m a = R → (sizesAt X 0 0 24).k a = Kc →
      slot μ = a → ∀ r c, trFull X pl i x 24 a r c =
        lay Sz.ref ⟨honAt X i x, m⟩ .head μ r c := by
    intro μ a R Kc ho hμ hR' hK' ha hm hk et r c
    refine own_cell X pl i x m (σ := .head) ho
      (shape_of_mu ((mu_ref (σ := .head) trivial μ).trans hμ) hR' hK') ?_ ?_ ?_ ?_ ?_ r c
    · show a < (planMats X 24).size
      rw [planMats_eq, size_head h C]
      omega
    · show ((planMats X 24).getD a {}).m = R
      rw [planMats_eq]
      exact hm
    · show ((planMats X 24).getD a {}).k = Kc
      rw [planMats_eq]
      exact hk
    · show a ≠ bNo X 24
      rw [bNo_head, N.NHf]
      omega
    · intro r c
      show listsOf X (honMx X i x) 24 a r c = honMx X i x 24 (slot μ * 65536 + r) c
      rw [(listsOf_eq_true X i x).2.2]
      show Hd.zOf (honMx X i x) (Hd.labH X.hS X.y a) r c = _
      unfold Hd.labH
      rw [if_neg (by rw [N.NHf]; omega), B.groups]
      unfold Hd.zOf
      rw [if_pos (by omega), show ((1 + 12) * 256 + a) % 256 = a by omega, et]
  refine ⟨fun p hp => ?_, gen (μ := .hd) rfl rfl rfl kF_hd (by norm_num) ?_ ?_ rfl,
    gen (μ := .hr) rfl rfl rfl kF_hr (by norm_num) ?_ ?_ rfl⟩
  · exact gen (μ := .hf p) (R := 65536) (Kc := 4816) rfl (if_pos hp)
      (by norm_num [Sz.rows, Sz.wc, Sz.ref]) (kF_hf p) (by omega)
      ((q1 p hp).2.1.trans N.m) ((q1 p hp).2.2.trans N.k) rfl
  · exact q2.2.1.trans N.mD
  · exact q2.2.2.trans N.kD
  · exact q3.2.1.trans N.mR
  · exact q3.2.2.trans N.kR

/-! ## All matrices of cells -/

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds: for every pl, index, request and counts
m, every segment σ of a proof with 12 groups and every name μ that has the number a in σ's list at
the reference numbers and is not the name of σ's planes, at all rows and columns, the trace at (σ.no
12, a) is "lay Sz.ref" of the honest cells at (σ, μ). -/
theorem trFull_eq_lay_core (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P)
    (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref) (m : Seg → ℕ → ℕ → ℕ) {σ : Seg}
    {μ : MatName} {a : ℕ} (hσ : σ.Below 12) (hμ : Sz.ref.mu σ μ = some a) (hp : μ ≠ planeOf σ)
    (r c : ℕ) :
    trFull X pl i x (σ.no 12) a r c = lay Sz.ref ⟨honAt X i x, m⟩ σ μ r c := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨b1, b2, b3⟩ := borrowed_core h C pl i x
  have hQA : (matIx X.y).iQA = 6 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6
    rw [p0, p1]
  have hXO : (matIx X.y).iXO = 7 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7
    rw [p0, p1]
  have hXI : (matIx X.y).iXI = 8 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8
    rw [p0, p1]
  rw [mu_ref hσ] at hμ
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ
    obtain ⟨f0, f3, f4, f6, f7, f8⟩ := ff_all h C pl i x m hg
    show trFull X pl i x (2 * g) a r c = _
    cases μ <;> simp only [MatName.no?] at hμ
    case af p =>
      split at hμ
      · rename_i hp3
        obtain rfl := Option.some.inj hμ
        exact f0 _ hp3 r c
      · exact absurd hμ (by simp)
    case ad p =>
      split at hμ
      · rename_i hp1
        obtain rfl := Option.some.inj hμ
        obtain rfl : p = 0 := Nat.lt_one_iff.1 hp1
        exact f3 r c
      · exact absurd hμ (by simp)
    case ar =>
      obtain rfl := Option.some.inj hμ
      exact f4 r c
    case b => exact absurd rfl hp
    case qa =>
      obtain rfl := Option.some.inj hμ
      exact f6 r c
    case xbO =>
      obtain rfl := Option.some.inj hμ
      exact f7 r c
    case xbI =>
      obtain rfl := Option.some.inj hμ
      by_cases g0 : g = 0
      · exact f8 g0 r c
      · have e1 := b1 g (Nat.pos_of_ne_zero g0) hg r c
        rw [hXI, hXO] at e1
        have eo : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg g0
        rw [lay_owner Sz.ref ref_ok.1 _ (.ff g) hg .xbI, eo]
        exact e1.trans ((ff_all h C pl i x m (g := g - 1) (by omega)).2.2.2.2.1 r c)
    all_goals exact absurd hμ (by simp)
  | att g =>
    have hg : g < 12 := hσ
    obtain ⟨a0, a1, a2⟩ := att_all h C pl i x m hg
    obtain ⟨-, -, n1, -⟩ := matsAt_att_gid h C hg
    show trFull X pl i x (2 * g + 1) a r c = _
    cases μ <;> simp only [MatName.no?] at hμ
    case as p =>
      split at hμ
      · rename_i hp1
        obtain rfl := Option.some.inj hμ
        obtain rfl : p = 0 := Nat.lt_one_iff.1 hp1
        exact a0 r c
      · exact absurd hμ (by simp)
    case ah =>
      obtain rfl := Option.some.inj hμ
      exact a1 r c
    case ao =>
      obtain rfl := Option.some.inj hμ
      exact a2 r c
    case bA => exact absurd rfl hp
    case qa =>
      obtain rfl := Option.some.inj hμ
      have e1 := b2 g hg r c
      rw [n1, hQA] at e1
      rw [lay_owner Sz.ref ref_ok.1 _ (.att g) hg .qa]
      exact e1.trans ((ff_all h C pl i x m hg).2.2.2.1 r c)
    all_goals exact absurd hμ (by simp)
  | head =>
    obtain ⟨h0, h4, h5⟩ := head_all h C pl i x m
    show trFull X pl i x 24 a r c = _
    cases μ <;> simp only [MatName.no?] at hμ
    case hf p =>
      split at hμ
      · rename_i hp4
        obtain rfl := Option.some.inj hμ
        exact h0 _ hp4 r c
      · exact absurd hμ (by simp)
    case hd =>
      obtain rfl := Option.some.inj hμ
      exact h4 r c
    case hr =>
      obtain rfl := Option.some.inj hμ
      exact h5 r c
    case bH => exact absurd rfl hp
    case xbL =>
      obtain rfl := Option.some.inj hμ
      have e1 := b3 r c
      rw [B.full.NHf, hXO] at e1
      rw [lay_owner Sz.ref ref_ok.1 _ .head trivial .xbL]
      exact e1.trans ((ff_all h C pl i x m (g := 11) (by norm_num)).2.2.2.2.1 r c)
    all_goals exact absurd hμ (by simp)

end Core

/-! ## In scope -/

/-- **The trace is the laying by formula, off the planes.** Under the three premises on the public
files (Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X): for every pl,
index i, request x (served or not) and counts m, every segment σ of a proof with 12 groups and every
name μ that has the number a in σ's list at the reference numbers and is not the name of σ's planes,
at all rows r and columns c: trFull X pl i x (σ.no 12) a r c = lay Sz.ref ⟨honAt X i x, m⟩ σ μ r c.
-/
theorem trFull_eq_lay_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {ly : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL ly = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref)
    (m : Seg → ℕ → ℕ → ℕ) {σ : Seg} {μ : MatName} {a : ℕ} (hσ : σ.Below 12)
    (hμ : Sz.ref.mu σ μ = some a) (hp : μ ≠ planeOf σ) (r c : ℕ) :
    trFull X pl i x (σ.no 12) a r c = lay Sz.ref ⟨honAt X i x, m⟩ σ μ r c :=
  trFull_eq_lay_core h (Hd.core_of_scope hZ hR h) pl i x m hσ hμ hp r c

/-- Where a name has no number in a segment's list, the laid matrix is 0. -/
theorem lay_of_mu_none (Y : Src) {σ : Seg} {μ : MatName} (hm : Sz.ref.mu σ μ = none) (r c : ℕ) :
    lay Sz.ref Y σ μ r c = 0 := by
  refine lay_off Sz.ref Y σ μ r c fun H => ?_
  have e : Sz.ref.shape σ μ = (0, 0) := by
    unfold Sz.shape
    rw [hm]
    rfl
  rw [e] at H
  exact absurd H.1 (Nat.not_lt_zero _)

/-- **The trace read by names is the laying by formula, off the planes.** Under the three premises
on the public files (Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X):
for every pl, index, request and counts m, EVERY segment σ and every name μ but the name of σ's
planes, at all rows and columns: byName X (trFull X pl i x) σ μ r c = lay Sz.ref ⟨honAt X i x, m⟩ σ
μ r c. Where μ has no number in σ's list, and at a group from 12 on, both sides are 0. -/
theorem byName_eq_lay_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {ly : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL ly = .ok X) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref)
    (m : Seg → ℕ → ℕ → ℕ) (σ : Seg) {μ : MatName} (hp : μ ≠ planeOf σ) (r c : ℕ) :
    byName X (trFull X pl i x) σ μ r c = lay Sz.ref ⟨honAt X i x, m⟩ σ μ r c := by
  by_cases hσ : σ.Below 12
  · obtain ⟨p0, p1, pA, pH⟩ := parts_in_scope hZ hR h
    have en : noAt X σ μ = Sz.ref.mu σ μ := by
      rw [mu_ref hσ]
      unfold noAt
      rw [p0, p1, pH]
      cases σ with
      | ff g => cases μ <;> rfl
      | att g =>
        have e : Seg.no 12 (.att g) / 2 = g := by
          show (2 * g + 1) / 2 = g
          omega
        rw [e, pA g hσ]
      | head => cases μ <;> rfl
    unfold byName
    rw [if_pos (Seg.ofNo_no hσ), en]
    cases hm : Sz.ref.mu σ μ with
    | some a => exact trFull_eq_lay_in_scope hZ hR h pl i x m hσ hm hp r c
    | none => exact (lay_of_mu_none _ hm r c).symm
  · unfold byName
    rw [if_neg fun e => hσ (Seg.of_ofNo e).1]
    exact (lay_of_mu_none _ (if_neg hσ) r c).symm

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.inShape_iff
#print axioms OnBytes.HonestTrace.own_cell
#print axioms OnBytes.HonestTrace.ff_sizes
#print axioms OnBytes.HonestTrace.kAs_core
#print axioms OnBytes.HonestTrace.shape_of_mu
#print axioms OnBytes.HonestTrace.mu_ref
#print axioms OnBytes.HonestTrace.ff_own
#print axioms OnBytes.HonestTrace.ff_all
#print axioms OnBytes.HonestTrace.att_all
#print axioms OnBytes.HonestTrace.head_all
#print axioms OnBytes.HonestTrace.trFull_eq_lay_core
#print axioms OnBytes.HonestTrace.trFull_eq_lay_in_scope
#print axioms OnBytes.HonestTrace.lay_of_mu_none
#print axioms OnBytes.HonestTrace.byName_eq_lay_in_scope
