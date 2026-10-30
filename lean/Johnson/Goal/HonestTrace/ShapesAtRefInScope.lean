-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/ShapesAtRefInScope.lean

For public files in the goals' scope, the rows and columns of the matrices of cells in the
verifier's plans are those of "Sz.ref" (Johnson/HonestTrace/Places.lean), but for the planes. This
file states no goal.

"Sz.ref" holds the full-size example's numbers, typed by hand, and "Sz.ref.shape σ μ" computes from
them the rows of cells and the columns of the matrix μ in the list of the segment σ. The verifier of
OnBytes/Model/ ("OnBytes.Model.Verify") computes its plans from the public files: "publicOf" returns
X, and "planMats X k" (Johnson/HonestTrace/Full.lean) is the list of matrices in the plan of
sub-proof k, each with its rows and columns. This file shows that the two agree, entry by entry.

The three premises. "In scope" means: "VerifierAndGoals.InScope Z = true" (see its definition in Ladder.lean),
"VerifierAndGoals.readFiles Z = .ok pp", and "publicOf Z.pol Z.KL ly = .ok X".

Main definitions and theorems:
* "EntryIs X σ μ a": entry a of the plan's list of sub-proof σ.no 12 is there, and has the rows and
  the columns of "Sz.ref.shape σ μ".
* "entryIs_in_scope": in scope, "EntryIs X σ μ a" for every segment σ of a proof with 12 groups and
  every name μ that has the number a in σ's list and is not the name of σ's planes: own matrices and
  borrowed ones. "entryIs_core": the same if "publicOf" returns X and "Hd.PublicCore X.P" holds.
* "inShape_iff_ref_in_scope": so a place (a, r, c) is inside the plan's shape ("InShape") exactly if
  r and c are inside "Sz.ref.shape σ μ".
* "shapeNo_in_scope", "packedShape_in_scope": the same by numbers: where "Sz.ref.matAt l mu" is a
  matrix that holds no planes, "Sz.ref.shapeNo l mu" is the rows and columns of the plan's entry mu
  of sub-proof l, and "Sz.ref.packedShape l mu" (Johnson/HonestTrace/Packed.lean) is the packed rows
  of these rows, and these columns.
* "msgOf_eq_packedOf_in_scope": "msgOf_eq_packedOf" (PackedIsMsg.lean in this folder) at "Sz.ref",
  with its premises on the sizes paid: for sizes s that follow X's plans with the radix 2^20.
Helpers: "entryIs_of", "entry_ff", "kF_xbL".

Limits. All is at the reference model's sizes. The planes (b, bA, bH) are left out: of their entries
in the plans this file says nothing. Every statement in scope is an implication from "publicOf ... =
.ok X"; that it returns at the stored full-size files is known in this library by an evaluation
("#guard", Johnson/Goal/Meaning/ScopeRun.lean). Rows and columns alone are compared: not the names
(for these see "planName_ff_in_scope" and its two like, FullInScope.lean in this folder), not the
labels, and no place of a cell. The shapes are those of the plans' lists; that a run's smallness
test goes by the same lists is not shown here.

Not claimed: anything on a proof, a prover or a verifier's answer. The program does not import this
file.

-/
import Johnson.Goal.HonestTrace.FullIsLayInScope
import Johnson.Goal.HonestTrace.PackedIsMsg

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size)
open Meaning

/-- Entry a of the plan's list of sub-proof σ.no 12 is there and has the rows and columns that
"Sz.ref" gives the matrix μ in the segment σ. -/
def EntryIs (X : Model.Verify.Public) (σ : Seg) (μ : MatName) (a : ℕ) : Prop :=
  a < (planMats X (σ.no 12)).size ∧
    ((planMats X (σ.no 12)).getD a {}).m = (Sz.ref.shape σ μ).1 ∧
    ((planMats X (σ.no 12)).getD a {}).k = (Sz.ref.shape σ μ).2

/-- "EntryIs" from one pair of numbers: if "Sz.ref.shape σ μ" is (R, Kc), and entry a of the plan's
list is there with R rows and Kc columns. -/
theorem entryIs_of {X : Model.Verify.Public} {σ : Seg} {μ : MatName} {a R Kc : ℕ}
    (hsh : Sz.ref.shape σ μ = (R, Kc)) (hs : a < (planMats X (σ.no 12)).size)
    (hm : ((planMats X (σ.no 12)).getD a {}).m = R)
    (hk : ((planMats X (σ.no 12)).getD a {}).k = Kc) : EntryIs X σ μ a :=
  ⟨hs, by rw [hsh]; exact hm, by rw [hsh]; exact hk⟩

/-- At the reference numbers the stream that the head borrows has 400 columns. -/
theorem kF_xbL : Sz.ref.kF .xbL = 400 := by decide +kernel

section Core
variable {pol KL : ByteArray} {ly : Option ByteArray} {X : Model.Verify.Public}

/-- One entry of the plan of group g < 12, if "publicOf" returns X and "Hd.PublicCore X.P" holds:
part p of the layout's matrix number mat has the number a in the list; the layout gives it R rows
and Kc columns, and so does "Sz.ref" give μ, which has the number a. -/
theorem entry_ff (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {μ : MatName} {a mat p R Kc : ℕ} (hμ : MatName.no? 3 1 1 4 (.ff g) μ = some a)
    (hR' : Sz.ref.rows μ = R) (hK' : Sz.ref.k (.ff g) μ = Kc) (hmat : mat ≤ 5)
    (hp : p < partsM X.y mat) (ea : firstM X.y mat + p = a) (hR : rowsM X.y mat = R)
    (hK : colsM X.y mat = Kc) (ha9 : a < 9) : EntryIs X (.ff g) μ a := by
  refine entryIs_of (shape_of_mu ((mu_ref (σ := .ff g) hg μ).trans hμ) hR' hK') ?_ ?_ ?_
  · show a < (planMats X (2 * g)).size
    rw [planMats_eq, size_even h C hg]
    exact ha9
  · show ((planMats X (2 * g)).getD a {}).m = R
    rw [planMats_eq, ← ea, (entry_eq h C hg hmat hp).1, hR]
  · show ((planMats X (2 * g)).getD a {}).k = Kc
    rw [planMats_eq, ← ea, (entry_eq h C hg hmat hp).2, hK]

/-- If "publicOf" returns X and "Hd.PublicCore X.P" holds: for every segment σ of a proof with 12
groups and every name μ that has the number a in σ's list at the reference numbers and is not the
name of σ's planes, entry a of the plan's list of sub-proof σ.no 12 is there and has the rows and
columns of "Sz.ref.shape σ μ". -/
theorem entryIs_core (h : publicOf pol KL ly = .ok X) (C : Hd.PublicCore X.P) {σ : Seg}
    {μ : MatName} {a : ℕ} (hσ : σ.Below 12) (hμ : Sz.ref.mu σ μ = some a) (hp : μ ≠ planeOf σ) :
    EntryIs X σ μ a := by
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  rw [mu_ref hσ] at hμ
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ
    obtain ⟨⟨r0, c0⟩, ⟨r1, c1⟩, ⟨r2, c2⟩, ⟨r3, c3⟩, ⟨r4, c4⟩, ⟨r5, c5⟩⟩ := ff_sizes h C
    have e4 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 = 4 := by rw [p0, p1]
    have e6 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6 := by rw [p0, p1]
    have e7 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7 := by rw [p0, p1]
    have e8 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8 := by rw [p0, p1]
    have hμ0 := hμ
    cases μ <;> simp only [MatName.no?] at hμ
    case af p =>
      split at hμ
      · rename_i hp3
        obtain rfl := Option.some.inj hμ
        exact entry_ff h C hg (mat := 0) (p := p) (R := 65536) hμ0
          (by norm_num [Sz.rows, Sz.wc, Sz.ref]) (kF_af p) (by norm_num)
          (by show p < X.y.parts.getD 0 0; omega) (Nat.zero_add p) r0 c0 (by omega)
      · exact absurd hμ (by simp)
    case ad p =>
      split at hμ
      · rename_i hp1
        obtain rfl := Option.some.inj hμ
        obtain rfl : p = 0 := Nat.lt_one_iff.1 hp1
        exact entry_ff h C hg (mat := 1) (p := 0) (R := 32768) hμ0
          (by norm_num [Sz.rows, Sz.wc, Sz.ref]) (kF_ad 0) (by norm_num)
          (by show 0 < X.y.parts.getD 1 0; omega) p0 r1 c1 (by norm_num)
      · exact absurd hμ (by simp)
    case ar =>
      obtain rfl := Option.some.inj hμ
      exact entry_ff h C hg (mat := 2) (p := 0) (R := 8192) hμ0
        (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_ar (by norm_num) Nat.one_pos e4 r2 c2
        (by norm_num)
    case b => exact absurd rfl hp
    case qa =>
      obtain rfl := Option.some.inj hμ
      exact entry_ff h C hg (mat := 3) (p := 0) (R := 65536) hμ0
        (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_qa (by norm_num) Nat.one_pos e6 r3 c3
        (by norm_num)
    case xbO =>
      obtain rfl := Option.some.inj hμ
      exact entry_ff h C hg (mat := 5) (p := 0) (R := 65536) hμ0
        (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_xbO (by norm_num) Nat.one_pos e7 r5 c5
        (by norm_num)
    case xbI =>
      obtain rfl := Option.some.inj hμ
      exact entry_ff h C hg (mat := 4) (p := 0) (R := 65536) hμ0
        (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_xbI (by norm_num) Nat.one_pos e8 r4 c4
        (by norm_num)
    all_goals exact absurd hμ (by simp)
  | att g =>
    have hg : g < 12 := hσ
    have hS := E.2.1 g hg
    obtain ⟨-, -, n1, -⟩ := matsAt_att_gid h C hg
    have PS := planSizes_of_follows h C (follows_sizesAt X 0 0) hg
    obtain ⟨fH, fO, fQ⟩ := fills_eq_of_core h C g hg
    have kA := kAs_core h C hg
    have gen : ∀ {μ : MatName} {a R Kc : ℕ}, MatName.no? 3 1 1 4 (.att g) μ = some a →
        Sz.ref.rows μ = R → Sz.ref.k (.att g) μ = Kc → a < 5 →
        (sizesAt X 0 0 (2 * g + 1)).m a = R → (sizesAt X 0 0 (2 * g + 1)).k a = Kc →
        EntryIs X (.att g) μ a := by
      intro μ a R Kc hμ hR' hK' ha hm hk
      refine entryIs_of (shape_of_mu ((mu_ref (σ := .att g) hg μ).trans hμ) hR' hK') ?_ ?_ ?_
      · show a < (planMats X (2 * g + 1)).size
        rw [planMats_eq, size_odd h C hg]
        exact ha
      · show ((planMats X (2 * g + 1)).getD a {}).m = R
        rw [planMats_eq]
        exact hm
      · show ((planMats X (2 * g + 1)).getD a {}).k = Kc
        rw [planMats_eq]
        exact hk
    have hμ0 := hμ
    cases μ <;> simp only [MatName.no?] at hμ
    case as p =>
      split at hμ
      · rename_i hp1
        obtain rfl := Option.some.inj hμ
        obtain rfl : p = 0 := Nat.lt_one_iff.1 hp1
        refine gen (R := 65536) hμ0 (by norm_num [Sz.rows, Sz.ref]) (kF_as 0) (by norm_num) ?_ ?_
        · rw [PS.asM 0 (by omega), hS.lmS]
          norm_num
        · rw [PS.asK 0 (by omega), kA, n1]
      · exact absurd hμ (by simp)
    case ah =>
      obtain rfl := Option.some.inj hμ
      refine gen (R := 8192) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_ah (by norm_num) ?_ ?_
      · have e := PS.ahM
        rw [n1, hS.wcH, hS.T] at e
        exact e
      · have e := PS.ahK
        rw [n1, fH, hS.wcH] at e
        exact e
    case ao =>
      obtain rfl := Option.some.inj hμ
      refine gen (R := 65536) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_ao (by norm_num) ?_ ?_
      · have e := PS.aoM
        rw [n1, hS.wcO, hS.T] at e
        exact e
      · have e := PS.aoK
        rw [n1, fO, hS.wcO] at e
        exact e
    case bA => exact absurd rfl hp
    case qa =>
      obtain rfl := Option.some.inj hμ
      refine gen (R := 65536) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_qa (by norm_num) ?_ ?_
      · have e := PS.qaM
        rw [n1, hS.wcQ, hS.T] at e
        exact e
      · have e := PS.qaK
        rw [n1, fQ, hS.wcQ] at e
        exact e
    all_goals exact absurd hμ (by simp)
  | head =>
    have N := Hd.numH_of_layout B.full B.head
    have Bd := Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
    obtain ⟨q1, q2, q3, q4⟩ := head_in h C (follows_sizesAt X 0 0)
    rw [N.NHf] at q1 q2 q3 q4
    have gen : ∀ {μ : MatName} {a R Kc : ℕ}, MatName.no? 3 1 1 4 .head μ = some a →
        Sz.ref.rows μ = R → Sz.ref.k .head μ = Kc → a < 8 →
        (sizesAt X 0 0 24).m a = R → (sizesAt X 0 0 24).k a = Kc → EntryIs X .head μ a := by
      intro μ a R Kc hμ hR' hK' ha hm hk
      refine entryIs_of (shape_of_mu ((mu_ref (σ := .head) trivial μ).trans hμ) hR' hK') ?_ ?_ ?_
      · show a < (planMats X 24).size
        rw [planMats_eq, size_head h C]
        exact ha
      · show ((planMats X 24).getD a {}).m = R
        rw [planMats_eq]
        exact hm
      · show ((planMats X 24).getD a {}).k = Kc
        rw [planMats_eq]
        exact hk
    have hμ0 := hμ
    cases μ <;> simp only [MatName.no?] at hμ
    case hf p =>
      split at hμ
      · rename_i hp4
        obtain rfl := Option.some.inj hμ
        exact gen (R := 65536) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) (kF_hf p) (by omega)
          ((q1 p hp4).2.1.trans N.m) ((q1 p hp4).2.2.trans N.k)
      · exact absurd hμ (by simp)
    case hd =>
      obtain rfl := Option.some.inj hμ
      exact gen (R := 16384) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_hd (by norm_num)
        (q2.2.1.trans N.mD) (q2.2.2.trans N.kD)
    case hr =>
      obtain rfl := Option.some.inj hμ
      exact gen (R := 8192) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_hr (by norm_num)
        (q3.2.1.trans N.mR) (q3.2.2.trans N.kR)
    case bH => exact absurd rfl hp
    case xbL =>
      obtain rfl := Option.some.inj hμ
      exact gen (R := 65536) hμ0 (by norm_num [Sz.rows, Sz.wc, Sz.ref]) kF_xbL (by norm_num)
        (q4.2.1.trans Bd.mxb) (q4.2.2.trans Bd.kxb)
    all_goals exact absurd hμ (by simp)

end Core

/-! ## In scope -/

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {ly : Option ByteArray} {X : Model.Verify.Public}

/-- **The plans' entries have the shapes of "Sz.ref", but for the planes.** Under the three premises
on the public files (Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X):
for every segment σ of a proof with 12 groups and every name μ that has the number a in σ's list at
the reference numbers and is not the name of σ's planes, entry a of the plan's list of sub-proof
σ.no 12 is there and has the rows and columns of "Sz.ref.shape σ μ". -/
theorem entryIs_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL ly = .ok X) {σ : Seg} {μ : MatName} {a : ℕ} (hσ : σ.Below 12)
    (hμ : Sz.ref.mu σ μ = some a) (hp : μ ≠ planeOf σ) : EntryIs X σ μ a :=
  entryIs_core h (Hd.core_of_scope hZ hR h) hσ hμ hp

/-- **Inside the plan's shape is inside the shape of "Sz.ref", but for the planes.** Under the three
premises on the public files (Z is in the goals' scope; the goals' reader returns pp; "publicOf"
returns X), for σ, μ and a as in "entryIs_in_scope", at all r and c: InShape X (σ.no 12) a r c
exactly if r is below the rows and c below the columns of "Sz.ref.shape σ μ". -/
theorem inShape_iff_ref_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL ly = .ok X) {σ : Seg}
    {μ : MatName} {a : ℕ} (hσ : σ.Below 12) (hμ : Sz.ref.mu σ μ = some a) (hp : μ ≠ planeOf σ)
    (r c : ℕ) :
    InShape X (σ.no 12) a r c ↔ r < (Sz.ref.shape σ μ).1 ∧ c < (Sz.ref.shape σ μ).2 := by
  obtain ⟨hs, hm, hk⟩ := entryIs_in_scope hZ hR h hσ hμ hp
  exact inShape_iff hs hm hk r c

/-- The same by numbers. Under the three premises on the public files (Z is in the goals' scope; the
goals' reader returns pp; "publicOf" returns X): if "Sz.ref.matAt l mu" is (σ, μ) and μ is not the
name of σ's planes, then l < 25, mu is a number of the plan's list of sub-proof l, and that entry's
rows and columns are "Sz.ref.shapeNo l mu". -/
theorem shapeNo_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL ly = .ok X) {l mu : ℕ} {σ : Seg} {μ : MatName}
    (hM : Sz.ref.matAt l mu = some (σ, μ)) (hp : μ ≠ planeOf σ) :
    l < 25 ∧ mu < (planMats X l).size ∧
      ((planMats X l).getD mu {}).m = (Sz.ref.shapeNo l mu).1 ∧
      ((planMats X l).getD mu {}).k = (Sz.ref.shapeNo l mu).2 := by
  obtain ⟨hσ, hl, hμ⟩ := (matAt_eq_some_iff Sz.ref l mu σ μ).1 hM
  have hσ' : σ.Below 12 := hσ
  have hl' : σ.no 12 = l := hl
  obtain ⟨hs, hm, hk⟩ := entryIs_in_scope hZ hR h hσ' hμ hp
  have e : Sz.ref.shapeNo l mu = Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [hM]
  rw [e, ← hl']
  refine ⟨?_, hs, hm, hk⟩
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ'
    show 2 * g < 25
    omega
  | att g =>
    have hg : g < 12 := hσ'
    show 2 * g + 1 < 25
    omega
  | head => exact (by norm_num : 2 * 12 < 25)

/-- **The packed shape is the plan's.** Under the three premises on the public files (Z is in the
goals' scope; the goals' reader returns pp; "publicOf" returns X): if "Sz.ref.matAt l mu" is (σ, μ)
and μ is not the name of σ's planes, "Sz.ref.packedShape l mu" is ("Alg.symRows" of the rows, the
columns) of entry mu of the plan's list of sub-proof l. -/
theorem packedShape_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL ly = .ok X) {l mu : ℕ} {σ : Seg} {μ : MatName}
    (hM : Sz.ref.matAt l mu = some (σ, μ)) (hp : μ ≠ planeOf σ) :
    Sz.ref.packedShape l mu =
      (Alg.symRows ((planMats X l).getD mu {}).m, ((planMats X l).getD mu {}).k) := by
  obtain ⟨-, -, hm, hk⟩ := shapeNo_in_scope hZ hR h hM hp
  unfold Sz.packedShape
  rw [hm, hk]

/-- **An entry of "msgOf" is the image of an entry of "packedOf Sz.ref".** Under the three premises
on the public files (Z is in the goals' scope; the goals' reader returns pp; "publicOf" returns X),
for sizes s that follow X's plans and have the radix 2^20 at all 25 sub-proofs, every family T of
integers by numbers and every label lab whose owner's numbers name, by "Sz.ref.matAt", a matrix that
holds no planes: at a column c below that matrix's columns, the entry (i, c) of the message with the
number lab, in either sort of row, is the image in E of "packedOf Sz.ref T" at the owner's numbers,
i and c. -/
theorem msgOf_eq_packedOf_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL ly = .ok X) {s : ℕ → Size}
    (Fo : Follows X s) (hr : ∀ k < 25, (s k).rad = 2 ^ 20) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (lab : ℕ)
    (b : Bool) (i c : ℕ) {σ : Seg} {μ : MatName}
    (hM : Sz.ref.matAt (ownerK lab) (ownerA lab) = some (σ, μ)) (hp : μ ≠ planeOf σ)
    (hc : c < (Sz.ref.shapeNo (ownerK lab) (ownerA lab)).2) :
    msgOf s T lab b i c =
      algebraMap Cb.Gl.F Cb.Gl.E (packedOf Sz.ref T (ownerK lab) (ownerA lab) i c) := by
  obtain ⟨hk, hs, hm, -⟩ := shapeNo_in_scope hZ hR h hM hp
  rw [planMats_eq] at hs hm
  exact msgOf_eq_packedOf Sz.ref s T lab b i c (hr _ hk) ((Fo.m _ hk _ hs).trans hm) hc

end Scope

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.EntryIs
#print axioms OnBytes.HonestTrace.entryIs_of
#print axioms OnBytes.HonestTrace.kF_xbL
#print axioms OnBytes.HonestTrace.entry_ff
#print axioms OnBytes.HonestTrace.entryIs_core
#print axioms OnBytes.HonestTrace.entryIs_in_scope
#print axioms OnBytes.HonestTrace.inShape_iff_ref_in_scope
#print axioms OnBytes.HonestTrace.shapeNo_in_scope
#print axioms OnBytes.HonestTrace.packedShape_in_scope
#print axioms OnBytes.HonestTrace.msgOf_eq_packedOf_in_scope
