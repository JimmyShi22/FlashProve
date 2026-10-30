-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadMet.lean: the hypotheses on the world under the theorems on the output head's forms
can be met, at any entries of the matrices and any values of the slots.

The theorem trueH_of_holds (Johnson/Road/HeadReads.lean) begins "if every record of the list of
tables holds in the world W what it says of the matrices M" (Holds, Johnson/Road/FormsKeysMat.lean).
This file shows that such a world exists for every M: the world in which each place of the reads
holds the sum that the record which owns the place says. That is the honest prover's direction, and
it is true by construction. What has to be shown is that no place is owned twice.

What is compared with what: two texts of the verifier: addFun and tablesOf
(OnBytes/Model/HeadTables.lean) with tabAt (OnBytes/Model/Tail.lean). Apart and holds_of_apart are
those of Johnson/Road/FormsKeysMet.lean, which speak of any record of the smallness test and any
list of tables. The library is mentioned only through the type of the cells.

Main definitions: widF, TiledF (the records lie one behind the other); PointsH (the lengths of the
points); AtPoints (the twelve tables on cells, each true in the sense in which the theorems on the
forms ask for it).
Main theorems.
 - tiled_step, tiled_list, tiled_addAsk, tiled_fold: adding tables keeps TiledF.
 - apartH: no place of the reads belongs to two records of the list that tablesOf returns, or twice
   to one. All fifteen tables are covered, those on bH too; nothing is asked of the matrices' sizes.
 - holds_of_entry, TrueH.of_entry: both read the entries of a world alone, not its slots.
 - holdsH_met, trueH_met: for every M and every choice of the slots' values there is a world.
 - phiC_value, rhoC_value; shortAt_masked, sumAt_masked, flatAt_masked: the three tables under the
   weights of the positions with a cost.
 - atPoints_of_true, atPoints_met: all twelve tables on cells in the senses of
   Johnson/Road/HeadLines.lean and Johnson/Road/HeadPolicy.lean, in one world with any slots.
 - LongAt.congr, ShortAt.congr, FlatAt.congr: a table that is true at a point is true at every point
   with the same coordinates.

The hypotheses, and where they are met: those of trueH_of_holds without the one on the world.
PointsH: nine lengths of points that the check receives or draws; in the run of
Johnson/Road/HeadPlaceRun.lean the made-up points have them; that the check's own routine gives them
is not shown.

The guard at the end is a run at the full-size example: in all fifteen tables the places of tabAt,
part by part, column by column, run by run, are the table's entries in rising order, and the tables
follow each other without a gap from entry 0 to the length of the reads.

What is not claimed. The verifier never tests Holds; how its random combinations lead there is not
looked at. The world is made for the matrices; nothing is said of other worlds. That the slots which
the theorems on the forms name are different slots is not shown here. The program does not import
this file.
-/
import Johnson.Road.HeadReads
import Johnson.Road.HeadPolicy
import Johnson.Road.HeadPlaceRun
import Johnson.Road.FormsKeysMet

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World HFun HTailF2 TMat Fork Settings eqTab longPhi longPoint lastOf
  cutLast)
open OnBytes.Model.Head (Owner HPlanH2 Tables planH2 tablesOf costWeights zjOf ztOf callNo)

/-! ## The records lie one behind the other -/

/-- The number of entries of a record: one for each column and each run of rows of its matrix. -/
def widF (mats : Array TMat) (Fn : HFun) : ℕ :=
  (mats.getD Fn.mat {}).k * ((mats.getD Fn.mat {}).m / Fn.len)

/-- Each record of the list ends at or before entry p, and two records that have an entry in common
are one record. -/
structure TiledF (mats : Array TMat) (funs : Array HFun) (p : ℕ) : Prop where
  ends : ∀ Fn ∈ funs, Fn.start + widF mats Fn ≤ p
  apart : ∀ Fn ∈ funs, ∀ Fn' ∈ funs, ∀ pos, Fn.start ≤ pos → pos < Fn.start + widF mats Fn →
    Fn'.start ≤ pos → pos < Fn'.start + widF mats Fn' → Fn = Fn'

/-- The step of addFun for one part keeps TiledF. -/
theorem tiled_step (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) (s : Array HFun × ℕ) (q : ℕ)
    (T : TiledF mats s.1 s.2) :
    TiledF mats (partStep mats M0 Lf phi s q).1 (partStep mats M0 Lf phi s q).2 := by
  have mem : ∀ Fn, Fn ∈ (partStep mats M0 Lf phi s q).1 → Fn ∈ s.1 ∨
      Fn = { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 } :=
    fun Fn h => Array.mem_push.mp h
  have hp : (partStep mats M0 Lf phi s q).2 = s.2 +
      widF mats { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 } := rfl
  refine ⟨fun Fn hF => ?_, fun Fn hF Fn' hF' pos a1 a2 b1 b2 => ?_⟩
  · rw [hp]
    rcases mem Fn hF with h1 | h1
    · have := T.ends Fn h1
      omega
    · rw [h1]
  · rcases mem Fn hF with h1 | h1 <;> rcases mem Fn' hF' with h2 | h2
    · exact T.apart Fn h1 Fn' h2 pos a1 a2 b1 b2
    · have := T.ends Fn h1
      rw [h2] at b1
      have b1' : s.2 ≤ pos := b1
      omega
    · have := T.ends Fn' h2
      rw [h1] at a1
      have a1' : s.2 ≤ pos := a1
      omega
    · rw [h1, h2]

/-- So do the steps for a list of parts. -/
theorem tiled_list (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) : ∀ (l : List ℕ)
    (s : Array HFun × ℕ), TiledF mats s.1 s.2 →
    TiledF mats (l.foldl (partStep mats M0 Lf phi) s).1 (l.foldl (partStep mats M0 Lf phi) s).2
  | [], _, T => T
  | q :: l, s, T => tiled_list mats M0 Lf phi l _ (tiled_step mats M0 Lf phi s q T)

/-- Adding a table keeps TiledF. -/
theorem tiled_addAsk {mats : Array TMat} {t t' : Tables} {a : Ask}
    (T : TiledF mats t.funs t.p) (h : addAsk mats t a = some t') : TiledF mats t'.funs t'.p := by
  have T' := tiled_list mats a.1 a.2.2.1 a.2.2.2.1 (List.range a.2.1) (t.funs, t.p) T
  unfold addAsk at h
  rw [addFun_eq] at h
  generalize (List.range a.2.1).foldl (partStep mats a.1 a.2.2.1 a.2.2.2.1) (t.funs, t.p) = r
    at T' h
  by_cases hz : (r.2 == t.p) = true
  · rw [if_pos hz] at h
    cases h
  · rw [if_neg hz] at h
    have e := (Option.some.inj h).symm
    subst e
    exact T'

/-- Adding a list of tables keeps TiledF. -/
theorem tiled_fold (mats : Array TMat) : ∀ (asks : List Ask) (t t' : Tables),
    TiledF mats t.funs t.p → asks.foldlM (addAsk mats) t = some t' → TiledF mats t'.funs t'.p
  | [], t, t', T, h => by
    have e : t' = t := (Option.some.inj h).symm
    subst e
    exact T
  | a :: rest, t, t', T, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t1, h1, h2⟩ := bind_some h
    exact tiled_fold mats rest t1 t' (tiled_addAsk T h1) h2

/-- **No place of the reads is owned twice.** For the tables that a list of lines leaves, from the
empty list, over the matrices of the smallness test's record tl: if tl has one place for column c,
run sg of a record of the list and for column c', run sg' of a record of the list, the records, the
columns and the runs are the same. -/
theorem apartH {tl : HTailF2} {asks : List Ask} {t : Tables}
    (hf : asks.foldlM (addAsk tl.mats) {} = some t) : Apart tl t.funs := by
  have T0 : TiledF tl.mats ({} : Tables).funs ({} : Tables).p :=
    ⟨fun Fn h => absurd h (Array.not_mem_empty Fn), fun Fn h => absurd h (Array.not_mem_empty Fn)⟩
  have T := tiled_fold tl.mats asks {} t T0 hf
  have iv : ∀ (Fn : HFun) (c sg pos : ℕ), tl.tabAt Fn c sg = some pos →
      Fn.start ≤ pos ∧ pos < Fn.start + widF tl.mats Fn ∧
        sg < (tl.mats.getD Fn.mat {}).m / Fn.len ∧
        pos = Fn.start + (c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg) := by
    intro Fn c sg pos h
    obtain ⟨-, -, h3, h4, h5⟩ := tailAt_inv tl Fn h
    unfold widF
    generalize (tl.mats.getD Fn.mat {}).m / Fn.len = n at h4 h5 ⊢
    generalize (tl.mats.getD Fn.mat {}).k = k at h3 ⊢
    have h6 := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h3)
    rw [Nat.succ_mul] at h6
    refine ⟨by omega, by omega, h4, by omega⟩
  intro Fn hF Fn' hF' c sg c' sg' pos h h'
  obtain ⟨a1, a2, a3, a4⟩ := iv Fn c sg pos h
  obtain ⟨b1, b2, b3, b4⟩ := iv Fn' c' sg' pos h'
  have e : Fn = Fn' := T.apart Fn hF Fn' hF' pos a1 a2 b1 b2
  subst e
  obtain ⟨e3, e4⟩ := layer_column a3 b3
    (by omega : c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg =
      c' * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg')
  exact ⟨rfl, e3, e4⟩

/-! ## A world for any matrices and any slots -/

section Met

variable {K : Type} [Field K] {ρ : Reading K}

/-- Whether a record holds depends on the entries of a world alone, not on its slots. -/
theorem holds_of_entry {W W' : World K} (h : W'.entry = W.entry) {tl : HTailF2} {iU3 K3 : ℕ}
    {M : Mats K} {Fn : HFun} (H : Holds ρ W tl iU3 K3 M Fn) : Holds ρ W' tl iU3 K3 M Fn := by
  intro c sg pos hp
  rw [h]
  exact H c sg pos hp

/-- So does whether the reads are true of cells. -/
theorem TrueH.of_entry {W W' : World K} (h : W'.entry = W.entry) {R : Model.Head.Run} {K3 : ℕ}
    {t : Inst.Model.Head.Cells K} (T : TrueH ρ W R K3 t) : TrueH ρ W' R K3 t := by
  have e : ∀ x, rdW W' R.iU3 K3 x = rdW W R.iU3 K3 x := by
    intro x
    unfold rdW
    rw [h]
  exact {
    hfZ := fun tb hs b hv => by rw [e]; exact T.hfZ tb hs b hv
    hfPhiZ := fun tb hs b hv => by rw [e]; exact T.hfPhiZ tb hs b hv
    xZV := fun Z hZ tb hs b hv => by rw [e]; exact T.xZV Z hZ tb hs b hv
    xYN := fun l hl tb hs b hv => by rw [e]; exact T.xYN l hl tb hs b hv
    hdFC := fun q hq tb hs b hv => by rw [e]; exact T.hdFC q hq tb hs b hv
    hdRH := fun tb hs b hv => by rw [e]; exact T.hdRH tb hs b hv
    hrROW := fun q hq tb hs b hv => by rw [e]; exact T.hrROW q hq tb hs b hv
    hrPV := fun tb hs b hv => by rw [e]; exact T.hrPV tb hs b hv
    hrTV := fun tb hs b hv => by rw [e]; exact T.hrTV tb hs b hv
    hrTN := fun tb hs b hv => by rw [e]; exact T.hrTN tb hs b hv
    hrPhiC := fun tb hs b hv => by rw [e]; exact T.hrPhiC tb hs b hv
    hrRhoC := fun tb hs b hv => by rw [e]; exact T.hrRhoC tb hs b hv }

variable (ρ)

/-- **Holds can be met**, at any matrices M and any values σ of the slots: if tablesOf succeeds,
then for every record tl of the smallness test with the plan's list of matrices there is a world
with the slots σ in which every record of the list of tables, those on bH among them, holds what it
says of M. K3 is any number, 0 too. -/
theorem holdsH_met {R : Model.Head.Run} {F G : Fork} {C D : Ctx}
    (ht : Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {tl : HTailF2}
    (hm : tl.mats = R.hp.tl.mats) (K3 : ℕ) (M : Mats K) (σ : ℕ → K) :
    ∃ W : World K, W.slot = σ ∧ ∀ Fn ∈ R.t.funs, Holds ρ W tl R.iU3 K3 M Fn := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, hf⟩ := tables_of_ok ht
  rw [← hm] at hf
  obtain ⟨W, hW⟩ := holds_of_apart ρ (apartH hf) R.iU3 K3 M
  exact ⟨⟨σ, W.entry⟩, rfl, fun Fn hF => holds_of_entry rfl (hW Fn hF)⟩

/-- **The hypothesis on the world under the theorems on the head's forms can be met**, at any
matrices and any slots. Under the hypotheses of trueH_of_holds but the one on the world: there is a
world with the slots σ in which every record holds what it says of M and the reads are true of the
cells that are read in the entries of M. -/
theorem trueH_met {R : Model.Head.Run} {g : Settings} {O : Owner} {NGr lkW : ℕ} {H0 : HPlanH2}
    (hpl : planH2 g R.h R.L R.b O NGr lkW = .ok H0) (hm0 : R.hp.tl.mats = H0.tl.mats)
    (hN0 : R.hp.tl.NM = H0.tl.NM) (hF : FullH R.h) (N : NumH R.h R.L) (Bd : BorderH R.b)
    {F G : Fork} {C D : Ctx} (ht : Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D)
    {tl : HTailF2} (hm : tl.mats = R.hp.tl.mats) (hNM : tl.NM = R.hp.tl.NM) (K3 : ℕ) (M : Mats K)
    (σ : ℕ → K) :
    ∃ W : World K, W.slot = σ ∧ (∀ Fn ∈ R.t.funs, Holds ρ W tl R.iU3 K3 M Fn) ∧
      TrueH ρ W R K3 (cellsH R.h R.L R.b M) := by
  obtain ⟨W, hs, hW⟩ := holdsH_met ρ ht hm K3 M σ
  exact ⟨W, hs, hW, trueH_of_holds hpl hm0 hN0 hF N Bd ht hm hNM hW⟩

/-! ## The tables at their points -/

/-- The lengths of the points from which tablesOf makes weights, but for the two whose lengths it
tests itself. -/
structure PointsH (R : Model.Head.Run) : Prop where
  Zl : R.x.Zl.size = R.h.ls + R.h.lt
  zFC : ∀ q, callNo R.L "CNF" = some q → (ztOf R.h R.L R.x.g1 q).size = R.h.lt
  zROW : ∀ q, callNo R.L "ROW" = some q → (ztOf R.h R.L R.x.g1 q).size = R.h.lt
  zH : (ztOf R.h R.L R.x.g1 R.x.qH).size = R.h.lt
  tH : R.x.tH.r.size = R.h.lt
  PV : R.x.PV.size = R.h.lt
  tV : R.x.tV.r.size = R.h.lt
  tN : R.x.tN.r.size = R.h.lt

variable {ρ}

/-- The weight of a position in the vector phiC: the equality weight of the point zt, times f, a
function that is 1 at the positions with a cost and 0 elsewhere. -/
theorem phiC_value (cov : Model.Head.Covered) {zt : Array E} {lt : ℕ} (hz : zt.size = lt)
    (f : ℕ → K) {i : ℕ} (hi : i < 2 ^ lt) (hf : f i = if cov.hOnC.getD i false then 1 else 0) :
    ρ.val ((costWeights cov zt).1.getD i zeroE) = Blocks.eqN lt 0 (pt ρ zt) i * f i := by
  have hi' : i < 2 ^ zt.size := by rw [hz]; exact hi
  have e : (costWeights cov zt).1 =
      (eqTab zt).mapIdx fun t x => if cov.hOnC.getD t false then x else zeroE := rfl
  rw [e, getD_mapIdx_lt _ _ (by rw [eqTab_size]; exact hi') zeroE zeroE, hf]
  by_cases hc : cov.hOnC.getD i false = true
  · rw [if_pos hc, if_pos hc, eqTab_value ρ zt i hi', hz, mul_one]
  · rw [if_neg hc, if_neg hc, ρ.zero, mul_zero]

/-- The weight of a position in the vector rhoCv: f. -/
theorem rhoC_value (cov : Model.Head.Covered) {zt : Array E} {lt : ℕ} (hz : zt.size = lt)
    (f : ℕ → K) {i : ℕ} (hi : i < 2 ^ lt) (hf : f i = if cov.hOnC.getD i false then 1 else 0) :
    ρ.val ((costWeights cov zt).2.2.getD i zeroE) = f i := by
  have hi' : i < 2 ^ zt.size := by rw [hz]; exact hi
  have e : (costWeights cov zt).2.2 =
      (eqTab zt).mapIdx fun t _ => if cov.hOnC.getD t false then oneE else zeroE := rfl
  rw [e, getD_mapIdx_lt _ _ (by rw [eqTab_size]; exact hi') zeroE zeroE, hf]
  by_cases hc : cov.hOnC.getD i false = true
  · rw [if_pos hc, if_pos hc, ρ.one]
  · rw [if_neg hc, if_neg hc, ρ.zero]

/-- A short table under phiC is true, at the point zt, of the cells times f. -/
theorem shortAt_masked {W : World K} {R : Model.Head.Run} {K3 : ℕ} {nm : String} {zt : Array E}
    {c : ℕ → ℕ → K} (hz : zt.size = R.h.lt) (f : ℕ → K)
    (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOnC.getD i false then 1 else 0)
    (h : SumShort ρ W R K3 nm (costWeights R.cov zt).1 c) :
    ShortAt W R K3 nm R.h.lt (pt ρ zt) (fun φ i => f i * c φ i) := by
  intro tb hst φ hv
  rw [h tb hst φ hv]
  show ∑ i ∈ range (2 ^ R.h.lt), ρ.val ((costWeights R.cov zt).1.getD i zeroE) * c φ i =
    ∑ X ∈ range (2 ^ R.h.lt), Blocks.eqN R.h.lt 0 (pt ρ zt) X * (f X * c φ X)
  refine sum_congr rfl fun i hi => ?_
  rw [phiC_value R.cov hz f (mem_range.mp hi) (hf i (mem_range.mp hi)), mul_assoc]

/-- A short table under rhoCv holds the plain sums of the cells times f. -/
theorem sumAt_masked {W : World K} {R : Model.Head.Run} {K3 : ℕ} {nm : String} {zt : Array E}
    {c : ℕ → ℕ → K} (hz : zt.size = R.h.lt) (f : ℕ → K)
    (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOnC.getD i false then 1 else 0)
    (h : SumShort ρ W R K3 nm (costWeights R.cov zt).2.2 c) :
    SumAt W R K3 nm (2 ^ R.h.lt) (fun φ i => f i * c φ i) := by
  intro tb hst φ hv
  rw [h tb hst φ hv]
  show ∑ i ∈ range (2 ^ R.h.lt), ρ.val ((costWeights R.cov zt).2.2.getD i zeroE) * c φ i =
    ∑ i ∈ range (2 ^ R.h.lt), f i * c φ i
  refine sum_congr rfl fun i hi => ?_
  rw [rhoC_value R.cov hz f (mem_range.mp hi) (hf i (mem_range.mp hi))]

/-- A long table whose weights repeat phiC for every feature of a block is true, at the point zt and
with the weight 1 on each feature of a block, of the cells times f. Asked beside: a block's row has
ls + lt bits. -/
theorem flatAt_masked {W : World K} {R : Model.Head.Run} {K3 : ℕ} {nm : String} {zt : Array E}
    {c : ℕ → ℕ → K} (hz : zt.size = R.h.lt) (hla : R.h.la = R.h.ls + R.h.lt) (f : ℕ → K)
    (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOnC.getD i false then 1 else 0)
    (h : SumLong ρ W R K3 nm ((Array.range (2 ^ R.h.la)).map fun j =>
      (costWeights R.cov zt).1.getD (j % R.h.T) zeroE) c) :
    FlatAt W R K3 nm R.h.ls R.h.lt (pt ρ zt) (fun φ i => f i * c φ i) := by
  intro tb hst b hv
  rw [h tb hst b hv]
  show ∑ r ∈ range (2 ^ R.h.ls), ∑ i ∈ range (2 ^ R.h.lt),
      ρ.val (((Array.range (2 ^ R.h.la)).map fun j =>
        (costWeights R.cov zt).1.getD (j % R.h.T) zeroE).getD (r * 2 ^ R.h.lt + i) zeroE) *
        c (b * 2 ^ R.h.ls + r) i =
    ∑ s ∈ range (2 ^ R.h.ls), ∑ X ∈ range (2 ^ R.h.lt),
      Blocks.eqN R.h.lt 0 (pt ρ zt) X * (f X * c (b * 2 ^ R.h.ls + s) X)
  refine sum_congr rfl fun r hr => sum_congr rfl fun i hi => ?_
  have hr' := mem_range.mp hr
  have hi' := mem_range.mp hi
  have hlt : r * 2 ^ R.h.lt + i < 2 ^ R.h.la := by
    rw [hla, pow_add]
    have h1 := Nat.mul_le_mul_right (2 ^ R.h.lt) (Nat.succ_le_of_lt hr')
    rw [Nat.succ_mul] at h1
    omega
  have e0 : (Array.range (2 ^ R.h.la)).getD (r * 2 ^ R.h.lt + i) 0 = r * 2 ^ R.h.lt + i := by
    simp [Array.getD, hlt]
  have e1 : (r * 2 ^ R.h.lt + i) % R.h.T = i := by
    show (r * 2 ^ R.h.lt + i) % 2 ^ R.h.lt = i
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
  rw [getD_map_lt _ _ (by simpa using hlt) zeroE 0, e0, e1,
    phiC_value R.cov hz f hi' (hf i hi'), mul_assoc]

/-- A long table that is true at a point is true at every point with the same coordinates. -/
theorem LongAt.congr {W : World K} {R : Model.Head.Run} {K3 : ℕ} {nm : String} {ls lt : ℕ}
    {low low' u u' : ℕ → K} {c : ℕ → ℕ → K} (h1 : ∀ j, j < ls → low j = low' j)
    (h2 : ∀ j, j < lt → u j = u' j) (h : LongAt W R K3 nm ls lt low u c) :
    LongAt W R K3 nm ls lt low' u' c := by
  intro tb hst b hv
  rw [h tb hst b hv]
  refine sum_congr rfl fun r _ => ?_
  have e : Blocks.eqN ls 0 low r = Blocks.eqN ls 0 low' r :=
    eqN_congr' ls 0 (fun j hj => by rw [Nat.zero_add]; exact h1 j hj) r
  rw [ext_point _ h2, e]

/-- The same for a short table. -/
theorem ShortAt.congr {W : World K} {R : Model.Head.Run} {K3 : ℕ} {nm : String} {lt : ℕ}
    {u u' : ℕ → K} {c : ℕ → ℕ → K} (h2 : ∀ j, j < lt → u j = u' j)
    (h : ShortAt W R K3 nm lt u c) : ShortAt W R K3 nm lt u' c := by
  intro tb hst φ hv
  rw [h tb hst φ hv, ext_point _ h2]

/-- The same for a long table with the weight 1 on each feature of a block. -/
theorem FlatAt.congr {W : World K} {R : Model.Head.Run} {K3 : ℕ} {nm : String} {ls lt : ℕ}
    {u u' : ℕ → K} {c : ℕ → ℕ → K} (h2 : ∀ j, j < lt → u j = u' j)
    (h : FlatAt W R K3 nm ls lt u c) : FlatAt W R K3 nm ls lt u' c := by
  intro tb hst b hv
  rw [h tb hst b hv]
  exact sum_congr rfl fun s _ => by rw [ext_point _ h2]

variable (ρ) in
/-- The twelve tables on cells, each true in the sense in which the theorems on the head's forms ask
for it (Johnson/Road/HeadLines.lean, Johnson/Road/HeadPolicy.lean): nine at the point from which
their weights are made, and three, under the weights of the positions with a cost, of the cells
times f. -/
structure AtPoints (W : World K) (R : Model.Head.Run) (K3 : ℕ) (f : ℕ → K)
    (t : Inst.Model.Head.Cells K) : Prop where
  hfZ : LongAt W R K3 "hf@Z" R.h.ls R.h.lt (pt ρ R.x.Zl) (fun j => pt ρ R.x.Zl (R.h.ls + j)) t.hf
  xZV : ∀ ZV, lastOf R.x.wpl.r R.h.la = .ok ZV →
    LongAt W R K3 "xbL@Z_V" R.h.ls R.h.lt (pt ρ ZV) (fun j => pt ρ ZV (R.h.ls + j)) t.x
  xYN : ∀ lowN, cutLast (zjOf R.L R.x.g1 R.x.qN) R.h.ls = .ok lowN →
    LongAt W R K3 "xbL@Y_N" R.h.ls R.h.lt (pt ρ (longPoint lowN.2 R.x.tN.r))
      (fun j => pt ρ (longPoint lowN.2 R.x.tN.r) (R.h.ls + j)) t.x
  hdFC : ∀ q, callNo R.L "CNF" = some q →
    ShortAt W R K3 "hd@zt_FC" R.h.lt (pt ρ (ztOf R.h R.L R.x.g1 q)) t.hd
  hdRH : ShortAt W R K3 "hd@r_H" R.h.lt (pt ρ R.x.tH.r) t.hd
  hrROW : ∀ q, callNo R.L "ROW" = some q →
    ShortAt W R K3 "hr@zt_ROW" R.h.lt (pt ρ (ztOf R.h R.L R.x.g1 q)) t.hr
  hrPV : ShortAt W R K3 "hr@P_V" R.h.lt (pt ρ R.x.PV) t.hr
  hrTV : ShortAt W R K3 "hr@r_tV" R.h.lt (pt ρ R.x.tV.r) t.hr
  hrTN : ShortAt W R K3 "hr@rt_N" R.h.lt (pt ρ R.x.tN.r) t.hr
  hrPhiC : ShortAt W R K3 "hr@phiC" R.h.lt (pt ρ (ztOf R.h R.L R.x.g1 R.x.qH))
    (fun φ i => f i * t.hr φ i)
  hrRhoC : SumAt W R K3 "hr@rhoC" (2 ^ R.h.lt) (fun φ i => f i * t.hr φ i)
  hfPhiZ : FlatAt W R K3 "hf@phiZ" R.h.ls R.h.lt (pt ρ (ztOf R.h R.L R.x.g1 R.x.qH))
    (fun φ i => f i * t.hf φ i)

/-- True reads are true in these senses. f: any function that is 1 at the positions with a cost and
0 at the other positions. -/
theorem atPoints_of_true {W : World K} {R : Model.Head.Run} {K3 : ℕ}
    {t : Inst.Model.Head.Cells K} (T : TrueH ρ W R K3 t) {F G : Fork} {C D : Ctx}
    (ht : Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) (P : PointsH R) (f : ℕ → K)
    (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOnC.getD i false then 1 else 0) :
    AtPoints ρ W R K3 f t := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hla, -, -⟩ := tables_of_ok ht
  exact {
    hfZ := longAt_of_sum P.Zl T.hfZ
    xZV := fun _ hZ => xZV_point T ht hZ
    xYN := fun _ hl => xYN_point T ht hl
    hdFC := fun q hq => shortAt_of_sum (P.zFC q hq) (T.hdFC q hq)
    hdRH := shortAt_of_sum P.tH T.hdRH
    hrROW := fun q hq => shortAt_of_sum (P.zROW q hq) (T.hrROW q hq)
    hrPV := shortAt_of_sum P.PV T.hrPV
    hrTV := shortAt_of_sum P.tV T.hrTV
    hrTN := shortAt_of_sum P.tN T.hrTN
    hrPhiC := shortAt_masked P.zH f hf T.hrPhiC
    hrRhoC := sumAt_masked P.zH f hf T.hrRhoC
    hfPhiZ := flatAt_masked P.zH hla f hf T.hfPhiZ }

variable (ρ) in
/-- **All tables and all slots in one world.** Under the hypotheses of trueH_met and the lengths of
the points: for any matrices M and any values σ of the slots there is one world with these slots in
which every record holds, the reads are true of the cells of M, and the twelve tables on cells are
true in the senses of AtPoints. -/
theorem atPoints_met {R : Model.Head.Run} {g : Settings} {O : Owner} {NGr lkW : ℕ} {H0 : HPlanH2}
    (hpl : planH2 g R.h R.L R.b O NGr lkW = .ok H0) (hm0 : R.hp.tl.mats = H0.tl.mats)
    (hN0 : R.hp.tl.NM = H0.tl.NM) (hF : FullH R.h) (N : NumH R.h R.L) (Bd : BorderH R.b)
    {F G : Fork} {C D : Ctx} (ht : Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D)
    {tl : HTailF2} (hm : tl.mats = R.hp.tl.mats) (hNM : tl.NM = R.hp.tl.NM) (P : PointsH R)
    (f : ℕ → K) (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOnC.getD i false then 1 else 0)
    (K3 : ℕ) (M : Mats K) (σ : ℕ → K) :
    ∃ W : World K, W.slot = σ ∧ (∀ Fn ∈ R.t.funs, Holds ρ W tl R.iU3 K3 M Fn) ∧
      TrueH ρ W R K3 (cellsH R.h R.L R.b M) ∧ AtPoints ρ W R K3 f (cellsH R.h R.L R.b M) := by
  obtain ⟨W, hs, hW, T⟩ := trueH_met ρ hpl hm0 hN0 hF N Bd ht hm hNM K3 M σ
  exact ⟨W, hs, hW, T, atPoints_of_true T ht P f hf⟩

end Met

/-! ## A run: all fifteen tables -/

/-- In every table of the list, those on bH too, the places that tabAt gives, taken part by part,
column by column and run by run, are the table's entries in rising order, all of them; and the
tables follow each other without a gap from entry 0 to the length of the reads. With the number of
tables. -/
def orderAllHP (X : Model.Verify.Public) (t : Tables) : Bool × Bool × ℕ :=
  (t.tab.all fun (_, tb, len) =>
      (entriesHP X.H.tl (partsHP t tb len)).map (·.2.2.2) ==
        (List.range len).map fun e => some (tb + e),
    t.tab.foldl (fun (s : Bool × ℕ) e => (s.1 && e.2.1 == s.2, s.2 + e.2.2)) (true, 0) ==
      (true, t.p), t.tab.length)

#guard (match Model.Verify.publicOf (textK linesKF) (wordsK scalesKF) none with
  | .error _ => false
  | .ok X => ((tablesHP X).map (orderAllHP X)) == some (true, true, 15))

#print axioms apartH
#print axioms holdsH_met
#print axioms trueH_met
#print axioms shortAt_masked
#print axioms sumAt_masked
#print axioms flatAt_masked
#print axioms atPoints_of_true
#print axioms atPoints_met

end OnBytes.Road.Hd
