-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlanesHost.lean: kind K5: the kind's instance of the planes' law
(Johnson/Meaning/PlanesLaw.lean, PlanesKit.lean): what the forms that the kind hands its lookup for
"planes" are worth: K3HostPlanes.

Main names:
  `readers_are`: ReadersAre: where the kind's reader of one entry (u3at) returns at every column of
    the planes, what it returns is the entry of the vector of reads (u3at_is,
    Johnson/Desc/First/Att/Claims/PlanesWorth.lean).
  `k5_host_planes`: host_planes_of_laid at the record's own list of tables; the law of the reads
    ReadsAll is a premise.
  `funRead_of_attAt`: the law of the reads at one table of the list, from AttAt
    (Johnson/Road/Rows/AttRead.lean). `k5_host_planes_attAt`: the instance under AttAt: the law of
    the reads is asked at the three tables alone.
  `kb_of_hid`, `planeCols_ok`, `look_y`: the planner's number of columns; the three weight vectors
    of lookOf (Johnson/Desc/First/Att/SeatC.lean) are Forest.phiB at 0 and 1 and Forest.phiP.
  `k5_host_planes_top`: K3HostPlanes gL.shape lmb (rdL ρ gL.zb0) (rdL ρ gL.zb1) ν (the worth in W)
    bit pin, at lk := lookOf lmb gL.
  `bA_rows`: in the list of matrices of a plan that Attention.plan returns, the planes' matrix has
    2^lmb rows (plan_mats, Johnson/Road/Lane5AttLabel.lean).
  `k5_host_planes_seat`: the instance over every seat: the forms are what the kind's two readers for
    "planes" (readersOfK, Johnson/Desc/First/Att/Guest.lean) return.
  `k5_host_planes_planned`: the same at a plan that Attention.plan returns, at the plan's own
    numbers (parCOf A) and list of matrices: the rows are bA_rows.
Premises of k5_host_planes_top, not shown in this file or in what it imports: AttAt (every table of
the list is true of the matrices M in W); gL.shape = fs; the return of tablesP; PosG; the planes'
matrix, number NAs + 2 of the list, has 2^lmb rows (MatsFit says nothing of it; bA_rows gives it at
a plan's own list); its cells are the lookup's places (M (NAs + 2) r c = ν (.cell r c) on the
planes' range); the three readers return at every column of the planes.
Beside it: planes_worth (Johnson/Desc/First/Att/Claims/PlanesWorth.lean) says, over every seat, that
a reader's form is worth the block's sum under the weights handed in; this file goes on from that
sum to colsK and pinColK at ν. Neither is spent in the other.
Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem on such a
routine's return; the runs spoken of are the kind's own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Meaning.PlanesKit
import Johnson.Desc.First.Att.Claims.LookLaid
import Johnson.Desc.First.Att.Claims.PlanesWorth
import Johnson.Desc.First.Att.SeatC
import Johnson.Road.Lane5AttCallsH
import Johnson.Road.Lane5AttLabel

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf LookIn)
open Meaning.Planes (LaidAt ReadersAre K3HostPlanes host_planes_of_laid)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {tl : HTailF2} {K : ℕ}
  {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}

/-- **The kind's readers of the planes' columns are the entries of the vector of reads**: where the reader of one entry returns at every column of the planes. bit e col, pin col: what it returns. -/
theorem readers_are {sh : FoNums.Sh} {lm : ℕ} {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff}
    (hb0 : ∀ col, col < sh.NC * 2 ^ (sh.kT + 5 - lm) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit0 col)).map (·.1) = some (bit 0 col))
    (hb1 : ∀ col, col < sh.NC * 2 ^ (sh.kT + 5 - lm) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit1 col)).map (·.1) = some (bit 1 col))
    (hpn : ∀ col, col < sh.NC * 2 ^ (sh.kT + 5 - lm) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tPin col)).map (·.1) = some (pin col)) :
    ReadersAre sh lm i.iU3 K i.t.tBit0 i.t.tBit1 i.t.tPin bit pin :=
  ⟨fun col hc => (u3at_is (hb0 col hc)).2, fun col hc => (u3at_is (hb1 col hc)).2,
    fun col hc => (u3at_is (hpn col hc)).2⟩

/-- **The kind's instance of the planes' law.** gL: what the kind's lookup has heard; lk: what it hands the kind for the tables; cellM: the matrices' cells; ν: the reading of the lookup's places. -/
theorem k5_host_planes {nW : ℕ} {lk : LookIn} (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g)
    (y0 : Forest.phiB gL S.cf.lmb 0 = some lk.phiB0) (y1 : Forest.phiB gL S.cf.lmb 1 = some lk.phiB1)
    (yP : lk.phiP = Forest.phiP S.cf.lmb)
    (h1 : (tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb = 1)
    (h2 : Fo.planeCols gL.shape S.cf.lmb ≤ (tl.mats.getD (S.cf.NAs + 2) {}).k)
    {cellM : ℕ → ℕ → ℕ → Kf} (ν : _root_.Fo.Pl → Kf)
    (h4 : ∀ r < 2 ^ S.cf.lmb, ∀ c < Fo.planeCols gL.shape S.cf.lmb, cellM (S.cf.NAs + 2) r c = ν (.cell r c))
    {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff}
    (hb0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit0 col)).map (·.1) = some (bit 0 col))
    (hb1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit1 col)).map (·.1) = some (bit 1 col))
    (hpn : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tPin col)).map (·.1) = some (pin col))
    (W : World Kf) (hA : Fo.ReadsAll ρ tl.mats (oldOf S gL i).t.funs W.entry i.iU3 K cellM) :
    K3HostPlanes gL.shape S.cf.lmb (Fo.rdL ρ gL.zb0) (Fo.rdL ρ gL.zb1) ν (fun f => f.value ρ W) bit pin := by
  obtain ⟨T0, T1, TP⟩ := look_laid (gL := gL) hg ht hp
  rw [yP] at TP
  exact host_planes_of_laid ρ gL y0 y1 T0 T1 TP h1 h2 ν h4 (readers_are hb0 hb1 hpn) W hA

/-- **The law of the reads at one table of the list**, where every table of the list is true of the matrices M in W (AttAt). -/
theorem funRead_of_attAt {W : World Kf} {M : Mats Kf} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} (A : AttAt ρ W tl K M h lid cf fs) {f : HFun} (hf : f ∈ h.t.funs.toList)
    (hm : f.mat < tl.NM) : Fo.FunRead ρ tl.mats W.entry h.iU3 K M f := by
  intro col hcol
  have hn : 0 < (tl.mats.getD f.mat {}).m / f.len := by
    rcases Nat.eq_zero_or_pos ((tl.mats.getD f.mat {}).m / f.len) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcol
      exact absurd hcol (Nat.not_lt_zero _)
    · exact h0
  have hl : f.len ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at hn
    exact absurd hn (Nat.lt_irrefl _)
  have hc : col / ((tl.mats.getD f.mat {}).m / f.len) < (tl.mats.getD f.mat {}).k :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
  have hv := A.tabs f hf _ _ _ (tailAt_some tl f hm hl hc (Nat.mod_lt col hn))
  rw [Nat.add_assoc, Nat.div_add_mod'] at hv
  exact hv

/-- **The same instance under AttAt**: the law of the reads is asked at the three tables alone, and AttAt gives it there. M: the matrices. -/
theorem k5_host_planes_attAt {nW : ℕ} {lk : LookIn} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    {W : World Kf} {M : Mats Kf} (A : AttAt ρ W tl K M (oldOf S gL i) lid cf fs) (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g)
    (y0 : Forest.phiB gL S.cf.lmb 0 = some lk.phiB0) (y1 : Forest.phiB gL S.cf.lmb 1 = some lk.phiB1)
    (yP : lk.phiP = Forest.phiP S.cf.lmb)
    (h1 : (tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb = 1)
    (h2 : Fo.planeCols gL.shape S.cf.lmb ≤ (tl.mats.getD (S.cf.NAs + 2) {}).k)
    (ν : _root_.Fo.Pl → Kf)
    (h4 : ∀ r < 2 ^ S.cf.lmb, ∀ c < Fo.planeCols gL.shape S.cf.lmb, M (S.cf.NAs + 2) r c = ν (.cell r c))
    {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff}
    (hb0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit0 col)).map (·.1) = some (bit 0 col))
    (hb1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit1 col)).map (·.1) = some (bit 1 col))
    (hpn : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tPin col)).map (·.1) = some (pin col)) :
    K3HostPlanes gL.shape S.cf.lmb (Fo.rdL ρ gL.zb0) (Fo.rdL ρ gL.zb1) ν (fun f => f.value ρ W) bit pin := by
  obtain ⟨⟨f0, m0, r0⟩, ⟨f1, m1, r1⟩, ⟨fP, mP, rP⟩⟩ := look_laid (gL := gL) hg ht hp
  rw [yP] at rP
  have hNM : S.cf.NAs + 2 < tl.NM := by
    have e : tl.NM = S.cf.NAs + 4 := A.mats.nm
    omega
  have hA : Fo.ReadsAll ρ tl.mats #[f0, f1, fP] W.entry i.iU3 K M := by
    intro f hf _
    have hf' : f = f0 ∨ f = f1 ∨ f = fP := by simpa using hf
    rcases hf' with rfl | rfl | rfl
    · exact funRead_of_attAt A m0 (by rw [r0.2.2.1]; exact hNM)
    · exact funRead_of_attAt A m1 (by rw [r1.2.2.1]; exact hNM)
    · exact funRead_of_attAt A mP (by rw [rP.2.2.1]; exact hNM)
  exact host_planes_of_laid ρ gL y0 y1 (funs := #[f0, f1, fP]) ⟨f0, by simp, r0⟩ ⟨f1, by simp, r1⟩
    ⟨fP, by simp, rP⟩ h1 h2 ν h4 (readers_are hb0 hb1 hpn) W hA

/-- The planner's number of columns of the planes' matrix. -/
theorem kb_of_hid {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (h : Attention.shapeHid lid cf = Except.ok (S, fs)) : Forest.planeCols fs cf.lmb = Except.ok S.kbA := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := L5.bind_ok h
  obtain ⟨f, -, h⟩ := L5.bind_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨kbA, hk, h⟩ := L5.bind_ok h
  obtain ⟨counted, -, h⟩ := L5.bind_ok h
  obtain ⟨-, -, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  subst e1
  subst e2
  exact hk

/-- What planeCols returns. -/
theorem planeCols_ok {sh : Model.Forest.Shape} {lm n : ℕ} (h : Forest.planeCols sh lm = Except.ok n) :
    (Forest.planeCols sh lm).toBool = true ∧ n = Fo.planeCols sh lm := by
  refine ⟨by rw [h]; rfl, ?_⟩
  unfold Forest.planeCols at h
  split at h
  · cases h
  · exact (Except.ok.inj h).symm

/-- The three weight vectors that the lookup hands the kind (lookOf, Johnson/Desc/First/Att/SeatC.lean) are the lookup's own. -/
theorem look_y {lm : ℕ} (hok : (Forest.planeCols gL.shape lm).toBool = true) :
    Forest.phiB gL lm 0 = some (P.lookOf lm gL).phiB0 ∧ Forest.phiB gL lm 1 = some (P.lookOf lm gL).phiB1 ∧
      (P.lookOf lm gL).phiP = Forest.phiP lm := by
  refine ⟨?_, ?_, rfl⟩ <;> unfold P.lookOf Forest.phiB <;> simp only [hok, if_true] <;> rfl

/-- **The instance at the seat's own letters**: lk := lookOf lmb gL; the lookup's shape is the planner's. Left as premises: AttAt; the planes' matrix has 2^lmb rows; its cells are the lookup's places; the readers return at every column of the planes. -/
theorem k5_host_planes_top {nW : ℕ} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    {W : World Kf} {M : Mats Kf} (A : AttAt ρ W tl K M (oldOf S gL i) lid cf fs) (hsh : gL.shape = fs)
    (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW (P.lookOf S.cf.lmb gL) i.p = some i.t) (hp : PosG i.g)
    (hm : (tl.mats.getD (S.cf.NAs + 2) {}).m = 2 ^ S.cf.lmb) (ν : _root_.Fo.Pl → Kf)
    (h4 : ∀ r < 2 ^ S.cf.lmb, ∀ c < Fo.planeCols gL.shape S.cf.lmb, M (S.cf.NAs + 2) r c = ν (.cell r c))
    {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff}
    (hb0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit0 col)).map (·.1) = some (bit 0 col))
    (hb1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tBit1 col)).map (·.1) = some (bit 1 col))
    (hpn : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) →
      (P.Runs.gather K (P.Runs.u3at i i.t.tPin col)).map (·.1) = some (pin col)) :
    K3HostPlanes gL.shape S.cf.lmb (Fo.rdL ρ gL.zb0) (Fo.rdL ρ gL.zb1) ν (fun f => f.value ρ W) bit pin := by
  have hid : Attention.shapeHid lid cf = Except.ok (S, fs) := A.shape
  have ecf : S.cf = cf := (L5.shaped_of_hid hid).cfg
  have hk := kb_of_hid hid
  rw [← ecf, ← hsh] at hk
  obtain ⟨hok, ekb⟩ := planeCols_ok hk
  obtain ⟨y0, y1, yP⟩ := look_y (gL := gL) hok
  have h1 : (tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb = 1 := by
    rw [hm]; exact Nat.div_self (Nat.two_pow_pos _)
  obtain ⟨n, R⟩ := tables_are ht hp
  have hf := fits_size R.tBit0.2
  rw [hg] at hf
  have hf' : S.kbA = (tl.mats.getD (S.cf.NAs + 2) {}).k * ((tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb) := hf
  rw [h1, Nat.mul_one] at hf'
  exact k5_host_planes_attAt A hg ht hp y0 y1 yP h1 (by rw [← ekb, hf']) ν h4 hb0 hb1 hpn

/-- **The planes' matrix has 2^lmb rows**, in the list of matrices of a plan that Attention.plan returns. -/
theorem bA_rows {settings : Model.Settings} {j : Attention.In} {cf : Attention.Cfg} {X : Attention.Plan}
    (h : Attention.plan settings j cf = Except.ok X) :
    (X.seam.tl.mats.getD (X.S.cf.NAs + 2) {}).m = 2 ^ X.S.cf.lmb := by
  have e : (Attention.matrices X.S X.inp)[X.S.cf.NAs + 2]? =
      some (Attention.ownMatrix X.inp "bA" (2 ^ X.S.cf.lmb) X.S.kbA (X.S.cf.NAs + 2) X.inp.wpbA) := by
    unfold Attention.matrices
    exact (L5.append_at _ _ 2 (by simp)).trans (by simp)
  rw [L5.plan_mats h, Array.getD_eq_getD_getElem?, Array.getElem?_map, e]
  rfl

open VerifiableInference.Desc.First.Att.P (SeatC ParC) in
/-- **The instance over every seat**: the forms are what the kind's two readers for "planes" (readersOfK, Johnson/Desc/First/Att/Guest.lean) return. Premises beyond those of k5_host_planes_top: the seat hands in lookOf lmb gL; the readers return at every column of the planes. -/
theorem k5_host_planes_seat {St : Type} (seat : SeatC St) (c : ParC) (s : St)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hgeo : c.geo = geoOf S) (hmats : c.mats = matsOf tl.mats) (hp : PosG c.geo)
    (hr : P.readersOfK seat c s = some r) (hlook : seat.look s = some (P.lookOf S.cf.lmb gL))
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.2 col).isSome) :
    ∃ i K, P.inOf seat c s = some (i, K) ∧
      ∀ (ρ : Reading Kf) (W : World Kf) (M : Mats Kf) (ν : _root_.Fo.Pl → Kf),
        AttAt ρ W tl K M (oldOf S gL i) lid cf fs → gL.shape = fs →
        (tl.mats.getD (S.cf.NAs + 2) {}).m = 2 ^ S.cf.lmb →
        (∀ r < 2 ^ S.cf.lmb, ∀ c < Fo.planeCols gL.shape S.cf.lmb, M (S.cf.NAs + 2) r c = ν (.cell r c)) →
        K3HostPlanes gL.shape S.cf.lmb (Fo.rdL ρ gL.zb0) (Fo.rdL ρ gL.zb1) ν (fun f => f.value ρ W)
          (fun e col => (r.1 e col).getD (Aff.ofConst zeroE)) (fun col => (r.2 col).getD (Aff.ofConst zeroE)) := by
  unfold P.readersOfK at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨⟨i, K⟩, hi, rfl⟩ := hr
  obtain ⟨eg, _, _, _, _, lk, hlk, ht⟩ := inOf_some seat c s i K hi
  rw [hlook] at hlk
  obtain rfl := Option.some.inj hlk
  refine ⟨i, K, hi, fun ρ W M ν A hsh hm h4 => ?_⟩
  have hg : i.g = geoOf S := eg.trans hgeo
  have ht' : P.tablesP i.g (matsOf tl.mats) c.nW (P.lookOf S.cf.lmb gL) i.p = some i.t := by
    rw [eg, ← hmats]; exact ht
  have some_getD : ∀ {o : Option Aff}, o.isSome → o = some (o.getD (Aff.ofConst zeroE)) := by
    intro o ho
    cases o with
    | none => cases ho
    | some a => rfl
  exact k5_host_planes_top A hsh hg ht' (by rw [eg]; exact hp) hm ν h4
    (fun col hc => some_getD (hr0 col hc)) (fun col hc => some_getD (hr1 col hc))
    (fun col hc => some_getD (hrP col hc))

open VerifiableInference.Desc.First.Att.P (SeatC) in
/-- **The instance at a plan that Attention.plan returns**, over every seat, at the plan's own numbers (parCOf A) and list of matrices: the rows of the planes' matrix are bA_rows. -/
theorem k5_host_planes_planned {St : Type} {settings : Model.Settings} {j : Attention.In} {cf0 : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings j cf0 = Except.ok A) (seat : SeatC St) (s : St)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hp : PosG (geoOf A.S)) (hr : P.readersOfK seat (P.parCOf A) s = some r)
    (hlook : seat.look s = some (P.lookOf A.S.cf.lmb gL))
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.2 col).isSome) :
    ∃ i K, P.inOf seat (P.parCOf A) s = some (i, K) ∧
      ∀ (ρ : Reading Kf) (W : World Kf) (M : Mats Kf) (ν : _root_.Fo.Pl → Kf),
        AttAt ρ W A.seam.tl K M (oldOf A.S gL i) lid cf fs → gL.shape = fs →
        (∀ r < 2 ^ A.S.cf.lmb, ∀ c < Fo.planeCols gL.shape A.S.cf.lmb,
          M (A.S.cf.NAs + 2) r c = ν (.cell r c)) →
        K3HostPlanes gL.shape A.S.cf.lmb (Fo.rdL ρ gL.zb0) (Fo.rdL ρ gL.zb1) ν (fun f => f.value ρ W)
          (fun e col => (r.1 e col).getD (Aff.ofConst zeroE)) (fun col => (r.2 col).getD (Aff.ofConst zeroE)) := by
  obtain ⟨i, K, hi, H⟩ := k5_host_planes_seat (Kf := Kf) (tl := A.seam.tl) (S := A.S) (gL := gL) (lid := lid)
    (cf := cf) (fs := fs) seat (P.parCOf A) s rfl rfl hp hr hlook hr0 hr1 hrP
  exact ⟨i, K, hi, fun ρ W M ν At hsh h4 => H ρ W M ν At hsh (bA_rows hA) h4⟩

end K5Law
