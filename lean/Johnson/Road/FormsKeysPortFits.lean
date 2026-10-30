-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPortFits.lean: the hypotheses under the comparisons of the panels are
concluded from the verifier's own lines and from true tables, and can be met.

Johnson/Road/FormsKeysPort.lean states one record, PortFits, and three ties of one call or one
family, ElTie, EwTie and WtsTie. The comparisons of the verifier's panels with the library's
(Johnson/Road/FormsKeysEarly.lean, Johnson/Road/FormsKeysLate.lean) take them as hypotheses. A
record that nobody concludes may be empty. This file concludes each of the four, and gives a world
in which the record holds.

What is compared with what. portFits_of_layout: the verifier's own layout, scales and list of tables
with the library's sizes, names of cells and table of scales, as in fits_of_layout_true
(Johnson/Road/FormsKeysAdmit.lean), of which it is the twin for the tables at the end point of the
second token sumcheck. The ties: the verifier's weights of the layers and of a segment's entries,
made from the point of a call, with the library's own el and ew.

Main definition: CallTieV, which is CallTie of Johnson/Road/FormsKeysAim.lean written on the record
Env (callTieV_iff).
Main theorems.
 - short2_of_laid, stream2_of_laid, portFits_of_layout: the record, in every world in which the six
   families of tables at the lookup's point (TrueAt) and the four at the end point of the second
   token sumcheck (TrueAt2) are true. No tie of a call is asked.
 - elTie_of_point, elTie_of_tie: ElTie at the call that holds the family's segment.
 - ewTie_of_tie: EwTie of the family.
 - wtsTie_of_call: WtsTie of a family that is read by blocks. It reads neither the library's point
   nor its number of columns.
 - TrueAt.congr, zpos_met, portFits_met: for any matrices M one world in which every table of the
   verifier's list holds what it says of M and the record holds of the cells that are read in the
   entries of M, at the verifier's own points.

The hypotheses, and where they are met.
 - The verifier's lines (layout, scalesHeld, readsOf, layTables, pointsOf, funsOf return; g is a
   group; the token point; the second token sumcheck has been heard): run together on made-up
   numbers in Johnson/Road/FormsKeysRun8.lean, and at the two shipped examples' files in
   Johnson/Road/FormsKeysRunK.lean. htm, hNM: plan_sizes, Johnson/Road/FormsKeysPlan.lean.
 - Switches, Sized: at the shipped examples switchesK, sizedKS, sizedKF in
   Johnson/Road/FormsKeysRunK.lean. Numerals: gl_numerals, Johnson/Road/FormsKeysKit.lean.
 - TrueAt, TrueAt2: portFits_met has a world. hzp, that the library's token point reads as the
   verifier's: zpos_met has such a z.
 - CallTieV of a family: four clauses on the call that holds the family's segment. Where the eight
   lines of calls are the library's and the verifier's least number of columns passes the library's
   for no call, callTieV_of_look (Johnson/Road/FormsKeysLookT.lean) concludes it for every family at
   one point z, from the letters in which the lookup makes the calls' points. By the run of
   Johnson/Road/FormsKeysRunK.lean the second clause fails at the small shipped example for four of
   the eight calls, among them the call of G and U: there ElTie and EwTie of these calls' families
   are not concluded.
 - The hypothesis of wtsTie_of_call on low: calls_share, Johnson/Road/FormsKeysPoint.lean, concludes
   it from the verifier's test on the calls' points.

What is not claimed. The verifier never tests that a table holds what it says; M is any function,
tied to no commitment. portFits_met says nothing on the ties. One z that serves the ties of all
calls and hzp together is not given here: look_fits (Johnson/Road/FormsKeysLookT.lean) gives it. The
program does not import this file.
-/
import Johnson.Road.FormsKeysPort
import Johnson.Road.FormsKeysAim

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff HFun HTailF2 Level Tsc CallD Seg lastOf eqTab tenCell)
open OnBytes.Model.Layer (Env Lay Reads Heard TableAsk TableAt Ten ClaimEnv layout readsOf
  scalesHeld layTables tableAsks pointsOf funsOf)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr call len zpos zc aC fams used)

variable {K : Type} [Field K]

/-! ## The record, from the layout and true tables -/

section Laid

variable {ρ : Reading K} {W : World K}

/-- The arrays that are read entry by entry, at the end point of the second token sumcheck: from the
verifier's own layout of the tensors, the switches, and the two families of short tables at that
point, found and true. -/
theorem short2_of_laid (v : Env) (L : Laid v.y) (S : Switches v.y.h) {D : Dim}
    (Z : Sized v.y.h D) (c : Cells K) {low zh : ℕ → K} (Fd : Found2 v)
    (T : TrueAt2 ρ W v v.y.h.lt c low zh) :
    ∀ X : Arr, readShort X = true → HasShort2 ρ W v D c (cellsOf D c) zh X := by
  intro X hX
  have hl : listed X = true := by unfold listed; rw [hX, Bool.or_true]; rfl
  obtain ⟨ten, hT, hm, hn, _, _, _⟩ := ten_of L S X (Or.inl hl)
  have hm' : matNo X = 1 ∨ matNo X = 2 := by
    cases X <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hX (by decide)
  rcases hm' with h1 | h2
  · obtain ⟨b, hb⟩ := Fd.ad
    refine ⟨ten, b, tensorAt_of hT (by rw [hm, h1]; exact hb),
      tied_cellsOf L S Z c (Or.inl hl) hT hn, ?_⟩
    rw [hm, h1, Z.lT]
    exact T.ad b hb
  · obtain ⟨b, hb⟩ := Fd.ar
    refine ⟨ten, b, tensorAt_of hT (by rw [hm, h2]; exact hb),
      tied_cellsOf L S Z c (Or.inl hl) hT hn, ?_⟩
    rw [hm, h2, Z.lT]
    exact T.ar b hb

/-- The residual stream at that end point: from the same, and the two families of long tables. -/
theorem stream2_of_laid (v : Env) (L : Laid v.y) (S : Switches v.y.h) {D : Dim}
    (Z : Sized v.y.h D) (c : Cells K) {low zh : ℕ → K} (Fd : Found2 v)
    (T : TrueAt2 ρ W v v.y.h.lt c low zh) :
    ∃ (bI bF : ℕ) (txs : Ten),
      v.tabAt ("xbI" ++ "@" ++ "Y") = some bI ∧ v.tabAt ("af" ++ "@" ++ "Y") = some bF ∧
      v.y.T_ "xs" = some txs ∧ txs.mat = 0 ∧
      Tied c (cellsOf D c) .x0 4 v.y.xb ∧ Tied c (cellsOf D c) .xs txs.mat txs.place ∧
      LongTrue ρ W v bI 4 v.y.ls D.lT c low zh ∧
      LongTrue ρ W v bF txs.mat v.y.ls D.lT c low zh ∧
      (∀ l, v.y.S2 ∣ tenCell v.y.xb l 0 0) ∧ ∀ i l, v.y.S2 ∣ tenCell txs.place l i 0 := by
  obtain ⟨ten, hT, hm, hn, _, hJ, hO⟩ := ten_of L S .xs (Or.inl rfl)
  obtain ⟨bI, hI⟩ := Fd.xi
  obtain ⟨bF, hF⟩ := Fd.af
  have hxl : v.y.xb.nl = 5 := by rw [L.xb]; exact S.xl
  have t0 : Tied c (cellsOf D c) .x0 4 v.y.xb := ⟨hxl, fun k inst j i => by
    show c 4 (Inst.Model.FFSeg.feat D .x0 k inst j) i = _
    rw [(xb_eq_feat L Z k inst j).1]⟩
  refine ⟨bI, bF, ten, hI, hF, hT, hm, t0, tied_cellsOf L S Z c (Or.inl rfl) hT hn,
    by rw [Z.lT]; exact T.xi bI hI, by rw [hm, Z.lT]; exact T.af bF hF, ?_,
    aligned_of (hO (Or.inl rfl)) (hJ ▸ L.bd)⟩
  intro l
  rw [L.xb]
  exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_zero _) (Dvd.dvd.mul_left L.bd _)) (Nat.dvd_zero _)

/-- The record PortFits holds of the verifier's own layout, scales and tables, in every world in
which the six families of tables at the lookup's point are true at the library's token point, and
the four families at the end point of the second token sumcheck are true at zh; for any reading that
takes numerals to numbers and any sizes that agree with the shape. The library's table of scales is
the one that sclOf defines from the verifier's scale file; its names of cells are read in the cells
c by the library's own rule (cellsOf). -/
theorem portFits_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {v : Env}
    {rd : Reads} {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hy : layout h pc = .ok v.y) (S : Switches h) (hs : scalesHeld h v.sc = .ok ())
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hρ : Numerals ρ) {D : Dim} (Z : Sized h D) (c : Cells K) (low z zh : ℕ → K)
    (T : TrueAt ρ W v h.lt c low (zpos D z)) (T2 : TrueAt2 ρ W v h.lt c low zh) :
    PortFits (scl := sclOf h v.sc v.g v.y.Lam) ρ W v D c (cellsOf D c) low z zh := by
  have A := admitted_of_layout hy S.p3
  have Fd := found2_of_layout hy S hrd hl ht
  have F := fits_of_layout_true hy S hs hg hrd hl ht hρ Z c low (zpos D z) T
  have e := A.shape
  subst e
  letI : Scl := sclOf v.y.h v.sc v.g v.y.Lam
  exact ⟨F, short2_of_laid v A.laid S Z c Fd T2, stream2_of_laid v A.laid S Z c Fd T2⟩

end Laid

/-! ## The ties of one call and of one family -/

section Ties

variable (ρ : Reading K)

/-- CallTie of Johnson/Road/FormsKeysAim.lean, written on what the forms of a layer sub-proof depend
on: the call of the verifier's layout that holds the segment of family s0 is the library's call of
the family, and its point is the library's. -/
def CallTieV (v : Env) (h : Model.Layer.Shape) (D : Dim) (z : ℕ → K) (s0 : Fam) :
    Prop :=
  ∀ (q : ℕ) (cd : CallD) (s : Seg), v.callOf (segName s0) = some (q, cd, s) →
    cd.segs.map (·.name) = (fams (call s0)).map segName ∧
    h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D (call s0)) ∧
    v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size ∧
    ∀ j, j < aC D (call s0) → pt ρ (v.zk.getD q #[]) j = zc D z (call s0) j

variable {ρ}

/-- It is CallTie. -/
theorem callTieV_iff (c : ClaimEnv) (h : Model.Layer.Shape) (D : Dim) (z : ℕ → K)
    (s0 : Fam) :
    CallTie ρ c h D z s0 ↔ CallTieV ρ c.v h D z s0 := Iff.rfl

/-- The layers' weights. If the point of the verifier's call number q has the coordinates of the
layer and reads as the library's point of its call cc, the layers' weights are the library's. -/
theorem elTie_of_point {v : Env} {D : Dim} {z : ℕ → K} {q : ℕ} {cc : Fin 8}
    (hll : v.y.h.ll = D.lL) (hsz : v.y.h.ll ≤ (v.zk.getD q #[]).size)
    (hz : ∀ j, j < aC D cc → pt ρ (v.zk.getD q #[]) j = zc D z cc j) : ElTie ρ v D z q cc := by
  intro lam hlam
  have h1 := elJ_value ρ v D q hll hsz (lam := lam) hlam
  unfold elJ at h1
  rw [h1]
  exact elP_eq_el D hz lam

variable {h : Model.Layer.Shape} {pc : List (List String)} {v : Env} {D : Dim} {z : ℕ → K}

/-- The layers' weights at the call that holds the family's segment, from the family's tie. -/
theorem elTie_of_tie (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D) {s0 : Fam}
    (T : CallTieV ρ v h D z s0) {q : ℕ} {cd : CallD} {s : Seg}
    (hc : v.callOf (segName s0) = some (q, cd, s)) : ElTie ρ v D z q (call s0) := by
  obtain ⟨-, -, hsz, hz⟩ := T q cd s hc
  have hll : v.y.h.ll = D.lL := by
    rw [(admitted_of_layout hy S.p3).shape]
    exact Z.lL.symm
  exact elTie_of_point hll (Nat.le_trans (Nat.le_add_right _ _) hsz) hz

/-- The weights of the entries of the family's segment, from the family's tie. -/
theorem ewTie_of_tie (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D) {s0 : Fam}
    (T : CallTieV ρ v h D z s0) : EwTie ρ v D z s0 := by
  intro a ha
  unfold Env.ewOf at ha
  obtain ⟨⟨q, cd, s⟩, hcall, e⟩ := map_some ha
  subst e
  obtain ⟨hn, hfl, hsz, hz⟩ := T q cd s hcall
  have A := admitted_of_layout hy S.p3
  obtain ⟨hq, hs, hname⟩ := callOf_spec hcall
  have hcd : cd ∈ v.y.calls := Array.mem_of_getElem? hq
  obtain ⟨k1, k2⟩ := cols_of_layout hy S Z hcd hn hfl
  obtain ⟨fam, a1, a2, -, a4, -⟩ := segs_of_layout hy S cd hcd s hs
  have hf : fam = s0 := segName_inj (a1.symm.trans hname)
  subst hf
  have hfam : famS s = fam := by
    unfold famS
    rw [a1, famOf_segName]
    rfl
  have hsn : s.n = len D fam := a2.trans (Z.len_eq fam).symm
  have hll : v.y.h.ll = D.lL := by
    rw [A.shape]
    exact Z.lL.symm
  have hpos : ∀ x, x < len D fam → s.pos.getD x 0 = Inst.Model.FFSeg.pos D fam x := by
    intro x hx
    have r := k2 s hs x
    rw [hfam] at r
    exact r hx
  refine ⟨?_, fun x hx => ?_⟩
  · show (Env.ewFrom (eqTab (v.zj q cd.lJ)) s).size = _
    unfold Env.ewFrom
    rw [Array.size_map, a4, hsn]
  · show ρ.val ((Env.ewFrom (eqTab (v.zj q cd.lJ)) s).getD x zeroE) = _
    rw [ewFrom_ewP ρ v D q cd s fam hll k1 (a4.trans hsn) hpos hsz hx]
    exact ewP_eq_ew D rfl hz x

/-- The weights of the blocks of the segment of a family that is read by blocks. Asked of the call
that holds the segment: its point has the coordinates of the layer and the column, and low is the
last ls coordinates of the column. Neither the library's point nor its number of columns is
read. -/
theorem wtsTie_of_call (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D) {s0 : Fam}
    (hb : byBlocks s0 = true) {low : ℕ → K}
    (H : ∀ (q : ℕ) (cd : CallD) (s : Seg), v.callOf (segName s0) = some (q, cd, s) →
      v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size ∧
      ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j)) :
    WtsTie ρ v D low s0 := by
  intro a wh ha hwh
  unfold Env.ewOf at ha
  unfold Env.ewh at hwh
  obtain ⟨⟨q, cd, s⟩, hcall, e⟩ := map_some ha
  subst e
  rw [hcall] at hwh
  have e2 := (Option.some.inj hwh).symm
  subst e2
  obtain ⟨hsz, hlow⟩ := H q cd s hcall
  have A := admitted_of_layout hy S.p3
  obtain ⟨hq, hs, hname⟩ := callOf_spec hcall
  have hcd : cd ∈ v.y.calls := Array.mem_of_getElem? hq
  obtain ⟨fam, a1, a2, -, a4, a5⟩ := segs_of_layout hy S cd hcd s hs
  have hf : fam = s0 := segName_inj (a1.symm.trans hname)
  subst hf
  have hsn : s.n = len D fam := a2.trans (Z.len_eq fam).symm
  have Al := a5 hb
  obtain ⟨k, hk⟩ := Al.whole
  have hpos : 0 < 2 ^ v.y.ls := by positivity
  have hS2 : v.y.S2 = 2 ^ v.y.ls := A.laid.S2
  refine ⟨?_, ?_, ?_⟩
  · show (Env.ewFrom (eqTab (v.zj q cd.lJ)) s).size = _
    unfold Env.ewFrom
    rw [Array.size_map, a4, hsn]
  · show (Env.ewhFrom v.y.S2 (eqTab (v.zj q (cd.lJ - v.y.ls))) s).size * 2 ^ v.y.ls = _
    unfold Env.ewhFrom
    rw [Array.size_map, Array.size_range, hS2, ← hsn, hk, Nat.mul_div_cancel _ hpos]
  · show Blocked ρ (Env.ewFrom (eqTab (v.zj q cd.lJ)) s)
      (Env.ewhFrom v.y.S2 (eqTab (v.zj q (cd.lJ - v.y.ls))) s) v.y.ls low
    rw [hS2]
    exact (blocked_join ρ v q cd.lJ hsz (lJ_of_layout hy cd hcd) s Al).congr hlow

end Ties

/-! ## The record can be met -/

section Met

/-- The extension of a vector over lt bits reads its point on the first lt coordinates alone. -/
theorem ext_congr_pt (lt : ℕ) (f : ℕ → K) {u u' : ℕ → K} (h : ∀ j, j < lt → u j = u' j) :
    Blocks.ext lt f u = Blocks.ext lt f u' := by
  unfold Blocks.ext
  refine sum_congr rfl fun i _ => ?_
  congr 1
  refine eqN_congr' lt 0 (fun j hj => ?_) i
  show u (0 + j) = u' (0 + j)
  rw [Nat.zero_add]
  exact h j hj

/-- TrueAt reads the token point on its first lT coordinates alone. -/
theorem TrueAt.congr {ρ : Reading K} {W : World K} {v : Env} {lT : ℕ} {c : Cells K}
    {low u u' : ℕ → K} (T : TrueAt ρ W v lT c low u) (h : ∀ j, j < lT → u j = u' j) :
    TrueAt ρ W v lT c low u' := by
  have L : ∀ b mat, LongTrue ρ W v b mat v.y.ls lT c low u →
      LongTrue ρ W v b mat v.y.ls lT c low u' := by
    intro b mat H b' a ha
    rw [H b' a ha]
    exact sum_congr rfl fun r _ => by rw [ext_congr_pt lT _ h]
  have Sh : ∀ b mat, ShortTrue ρ W v b mat lT c u → ShortTrue ρ W v b mat lT c u' := by
    intro b mat H φ a ha
    rw [H φ a ha, ext_congr_pt lT _ h]
  exact
    { af := fun b hb => L b 0 (T.af b hb), qa := fun b hb => L b 3 (T.qa b hb)
      xi := fun b hb => L b 4 (T.xi b hb), xo := fun b hb => L b 5 (T.xo b hb)
      ad := fun b hb => Sh b 1 (T.ad b hb), ar := fun b hb => Sh b 2 (T.ar b hb) }

omit [Field K] in
/-- Any point is the library's token point of some z. -/
theorem zpos_met (D : Dim) (u : ℕ → K) : ∃ z : ℕ → K, ∀ j, zpos D z j = u j :=
  ⟨fun t => u (t - (Inst.Model.FFSeg.Dk D - D.lT)), fun j => by
    show u (Inst.Model.FFSeg.Dk D - D.lT + j - (Inst.Model.FFSeg.Dk D - D.lT)) = u j
    rw [Nat.add_sub_cancel_left]⟩

/-- The record PortFits can be met at any matrices. Under the public hypotheses of trueAt2_met
(Johnson/Road/FormsKeysTrue2.lean), with scales that scalesHeld accepts, sizes that agree with the
shape, and a point z of the library whose token point reads as the verifier's token point: for any
matrices M there is a world in which every table of the verifier's list holds what it says of M, and
in which PortFits holds of the cells that are read in the entries of M, at the verifier's own
points: low is Z, the last la coordinates of the lookup's point, and zh the end point of the second
token sumcheck. -/
theorem portFits_met (ρ : Reading K) (hρ : Numerals ρ) {h : Model.Layer.Shape}
    {pc : List (List String)} {v : Env} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hy : layout h pc = .ok v.y) (S : Switches h) (hs : scalesHeld h v.sc = .ok ())
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd hd2 = some pts) (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF)
    (hfun : funsOf v.y H.fo pts r.2.1 = some funs) {tT : Tsc} (htT : H.tT = some tT)
    {D : Dim} (Z : Sized h D) (M : Mats K) {z : ℕ → K}
    (hzp : ∀ j, j < D.lT → zpos D z j = pt ρ H.ztF j) :
    ∃ W : World K, (∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) ∧
      ∃ Zp, lastOf H.fo.zx v.y.h.la = .ok Zp ∧
        PortFits (scl := sclOf h v.sc v.g v.y.Lam) ρ W v D (cellsAt v.y M)
          (cellsOf D (cellsAt v.y M)) (pt ρ Zp) z (pt ρ tT.r) := by
  obtain ⟨W, hW, Zp, hZ, T, T2⟩ :=
    trueAt2_met ρ hy S hg hrd hl ht htm hNM hp hzt hfun htT M
  have e := (admitted_of_layout hy S.p3).shape
  rw [e] at T T2
  refine ⟨W, hW, Zp, hZ, portFits_of_layout hy S hs hg hrd hl ht hρ Z _ _ z _
    (T.congr fun j hj => ?_) T2⟩
  rw [hzp j (by rw [Z.lT]; exact hj)]

end Met

#print axioms portFits_of_layout
#print axioms elTie_of_tie
#print axioms ewTie_of_tie
#print axioms wtsTie_of_call
#print axioms portFits_met

end OnBytes.Road
