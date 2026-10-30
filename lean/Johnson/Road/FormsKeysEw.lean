-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysEw.lean: the factor of a weight claim that is made from a lookup segment's
columns weighs an index with the library's weight of the segment's entry.

A weight claim has one factor for each index group of its unit (OnBytes/Model/Weights.lean). For the
group whose index runs over the entries of a lookup segment, the verifier makes the factor from the
segment's columns and the point of the segment's call (facEw in OnBytes/Model/LayerPanels.lean). The
library writes the weight of entry x of a family s as ew D z s x: the equality weight of the
column's coordinates of the call's point at the column pos D s x (Inst/Model/FF/Objects.lean).

What is compared with what. Left: what the verifier's factor weighs an index with, in the sense of
facAt (Johnson/Road/FormsKeysPan.lean; a meaning that these files give a factor). Right: ewP
(Johnson/Road/FormsKeysFree.lean), which is the library's ew with a free point in the place of the
library's own point of the call, at the verifier's point of the call; and, if that point agrees with
the library's on the call's coordinates, the library's ew itself.

The file goes in four steps.
 1. The weight that the lookup's join gives an entry of a segment is ewP, if the segment's columns
    are the library's and the call has as many columns (ewFrom_ewP).
 2. With the alignment of the segment's columns on blocks of 2^z entries, z the group's number of
    low bits, the factor weighs index x with ewP at entry x0 + x (facEw_ewP; from the records
    CallFits and SegFits: facEw_ewP_fits).
 3. On a layout that the verifier has returned, every segment is aligned on blocks of every power of
    two that divides its length (aligned_of_layout), and the columns are the library's if the call's
    line names the library's families in the library's order (cols_of_layout in
    Johnson/Road/FormsKeysQK.lean). So step 2 holds there (facEw_ewP_of_layout).
 4. At a point that agrees with the library's: the library's ew (facEw_ew). The same with the three
    hypotheses on numbers replaced by "x0 and the segment's length are multiples of the number of
    the group's indices" (facEw_ew_mul).

What is asked, and who shows that it can be met. The layout, the switches, the sizes, the call's
line (hn) and the least number of columns (hfl) are hypotheses of joinPart_keyVec in
Johnson/Road/FormsKeysKV.lean too. Johnson/Road/FormsKeysRun8.lean evaluates hn and hfl at a made-up
shape, where they hold for all eight calls. Johnson/Road/FormsKeysRunK.lean evaluates them at two
public example files. At the full-size example they hold for all eight calls. At the small one hfl
fails for the calls 0, 5, 6 and 7: there the verifier's call has more columns than the library's,
and the theorems from step 3 on do not apply to the families of these calls. That callOf and facEw
return, for the groups of the verifier's own claims, is evaluated in
Johnson/Road/FormsKeysRunW.lean, also at the made-up shape of FormsKeysRun8.lean (w7 there compares
every such factor, in that file's own reading of a factor, with the segment's weights). These are
runs, not theorems. That the call's point has its coordinates (hsz) follows from a run-time test
(size_of_test in Johnson/Road/FormsKeysPoint.lean). That the group has class 'E' and o 2^z indices,
and the divisibilities, are facts on the layout of the weights, which this file does not look at.
That the verifier's point of a call agrees with the library's (hz) is a hypothesis that no theorem
or run of these files concludes.

Main theorems: ewFrom_ewP, facEw_ewP, aligned_of_layout, facEw_ewP_of_layout, facEw_ew,
facEw_ew_mul.

What is not claimed: that facAt is what the verifier's settling of a claim on the matrix of weights
comes to (Johnson/Road/FormsKeysFac.lean); which groups of which units get such a factor; that two
calls do not hold segments of one name (the statements speak of the call that callOf finds). See
also Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysQK
import Johnson.Road.FormsKeysFacRs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Reading eqTab Seg CallD WsGrp WsFac place topBit)
open OnBytes.Model.Layer (ClaimEnv Env Lay layout)
open Inst.Model.FFSeg (Dim Fam len call pos lJ aC zc ew fams used)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The join's weight of an entry -/

/-- The weight that the lookup's join gives entry x of segment s of call number q reads as ewP of
the family s0 at the point of that call. Asked: a layer has as many coordinates as in the library;
the call has as many columns as the library's call of s0; the segment has one column for each entry
of the family, and it is the column that the library's rule gives the entry; the call's point has
the coordinates of the layer and the column; x is an entry of the family. -/
theorem ewFrom_ewP (v : Env) (D : Dim) (q : ℕ) (cd : CallD) (s : Seg) (s0 : Fam)
    (hll : v.y.h.ll = D.lL) (hlJ : cd.lJ = lJ D (call s0)) (hsize : s.pos.size = len D s0)
    (hpos : ∀ x, x < len D s0 → s.pos.getD x 0 = pos D s0 x)
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) {x : ℕ} (hx : x < len D s0) :
    ρ.val ((Env.ewFrom (eqTab (v.zj q cd.lJ)) s).getD x zeroE) =
      ewP D (pt ρ (v.zk.getD q #[])) s0 x := by
  unfold Env.ewFrom ewP ewcP
  rw [getD_map_lt _ _ (by rw [hsize]; exact hx) zeroE 0, hpos x hx,
    colJ_value ρ v D q cd.lJ hll hzk
      (by rw [hlJ]; exact Inst.Model.FFSeg.IndexFacts.pos_lt D hx), hlJ]

/-! ## The factor -/

/-- If facEw returns a factor, callOf has found a call that holds the segment. -/
theorem facEw_call {c : ClaimEnv} {G : WsGrp} {sn : String} {x0 : ℕ} {X : WsFac}
    (h : c.facEw G sn x0 = some X) : ∃ q cd s, c.v.callOf sn = some (q, cd, s) := by
  unfold ClaimEnv.facEw at h
  obtain ⟨⟨q, cd, s⟩, hc, -⟩ := bind_some h
  exact ⟨q, cd, s, hc⟩

/-- The factor that is made from the columns of segment sn, from its entry x0 on, weighs index x of
its group with ewP of the family s0 at entry x0 + x, at the point of the call that callOf finds.
Asked: what ewFrom_ewP asks of that call and segment; the segment's columns are aligned on blocks of
2^z entries, z the group's number of low bits; the group has class 'E' and o 2^z indices; 2^z
divides x0; the stretch of the group's indices from x0 on lies within the family. -/
theorem facEw_ewP (c : ClaimEnv) (D : Dim) (s0 : Fam) {sn : String} {q : ℕ} {cd : CallD} {s : Seg}
    (hcall : c.v.callOf sn = some (q, cd, s)) (hll : c.v.y.h.ll = D.lL)
    (hlJ : cd.lJ = lJ D (call s0)) (hn : s.n = len D s0)
    (hpos : ∀ x, x < len D s0 → s.pos.getD x 0 = pos D s0 x)
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) (G : WsGrp) (x0 : ℕ)
    (hE : (G.cls == 'E') = true) (hR : G.R = G.o * 2 ^ G.z) (A : Aligned s G.z cd.lJ)
    (hx0 : 2 ^ G.z ∣ x0) (hin : x0 + G.R ≤ len D s0) {X : WsFac}
    (hX : c.facEw G sn x0 = some X) :
    ∀ x, x < G.R → facAt ρ X G x = ewP D (pt ρ (c.v.zk.getD q #[])) s0 (x0 + x) := by
  intro x hx
  rw [facEw_aligned ρ c G sn x0 q cd s hcall hE hsz A hx0 (by rw [hn, ← hR]; exact hin) hX x
    (by rw [← hR]; exact hx)]
  exact ewFrom_ewP ρ c.v D q cd s s0 hll hlJ (by rw [A.size, hn]) hpos hsz (by omega)

/-- The same from the records CallFits and SegFits: for a segment s of a call that is the library's
call cc, with the family fam s. -/
theorem facEw_ewP_fits (c : ClaimEnv) (D : Dim) {sn : String} {q : ℕ} {cd : CallD} {s : Seg}
    {weighed : Array Bool} {cc : Fin 8} {fam : Seg → Fam} (C : CallFits c.v D cd weighed cc fam)
    (hs : s ∈ cd.segs) (HS : SegFits c.v D cd.lJ s (fam s))
    (hcall : c.v.callOf sn = some (q, cd, s))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) (G : WsGrp) (x0 : ℕ)
    (hE : (G.cls == 'E') = true) (hR : G.R = G.o * 2 ^ G.z) (A : Aligned s G.z cd.lJ)
    (hx0 : 2 ^ G.z ∣ x0) (hin : x0 + G.R ≤ len D (fam s)) {X : WsFac}
    (hX : c.facEw G sn x0 = some X) :
    ∀ x, x < G.R → facAt ρ X G x = ewP D (pt ρ (c.v.zk.getD q #[])) (fam s) (x0 + x) := by
  have hmem : fam s ∈ fams cc := by
    rw [← C.fams]
    exact List.mem_map_of_mem hs
  have hc : call (fam s) = cc := Inst.Model.FFSeg.IndexFacts.call_of_mem cc _ hmem
  exact facEw_ewP ρ c D (fam s) hcall C.ll (by rw [C.lJ, hc]) HS.n (C.pos s hs) hsz G x0 hE hR A hx0
    hin hX

/-! ## On a layout that the verifier has returned -/

/-- In a layout that the verifier has returned, under the switches, the columns of every segment are
aligned on blocks of 2^ls entries, for every ls such that 2^ls divides the segment's length. -/
theorem aligned_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {cd : CallD} (hcd : cd ∈ y.calls) {s : Seg}
    (hs : s ∈ cd.segs) (ls : ℕ) (hd : 2 ^ ls ∣ s.n) : Aligned s ls cd.lJ := by
  have A := admitted_of_layout hy S.p3
  obtain ⟨fam, -, a2, -, -, -⟩ := segs_of_admitted A S cd hcd s hs
  have hlt : s.n < 2 ^ (topBit + 1) := by
    rw [a2]
    exact len_lt A fam
  obtain ⟨cl, taken, -, -, hc⟩ := A.calls
  rw [hc] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  exact place_aligned _ _ _ _ ls s hs hd hlt

/-- The factor against ewP, on a layout that the verifier has returned. Under the switches, for
library sizes that agree with the shape: if the call that callOf finds for the name of the family s0
names the families of the library's call of s0 in the library's order (hn), the least number of
columns does not bite (hfl), and the call's point has its coordinates of the layer and the column
(hsz), then the factor that facEw makes for a group G from entry x0 of the segment on weighs index x
with ewP of s0 at entry x0 + x, at the point of that call. Asked of the group and of x0: class 'E';
o 2^z indices; 2^z divides x0 and the family's length; the stretch lies within the family. -/
theorem facEw_ewP_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {c : ClaimEnv}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) {D : Dim} (Z : Sized h D) (s0 : Fam) {q : ℕ}
    {cd : CallD} {s : Seg} (hcall : c.v.callOf (segName s0) = some (q, cd, s))
    (hn : cd.segs.map (·.name) = (fams (call s0)).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D (call s0)))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) (G : WsGrp) (x0 : ℕ)
    (hE : (G.cls == 'E') = true) (hR : G.R = G.o * 2 ^ G.z) (hx0 : 2 ^ G.z ∣ x0)
    (hlen : 2 ^ G.z ∣ len D s0) (hin : x0 + G.R ≤ len D s0) {X : WsFac}
    (hX : c.facEw G (segName s0) x0 = some X) :
    ∀ x, x < G.R → facAt ρ X G x = ewP D (pt ρ (c.v.zk.getD q #[])) s0 (x0 + x) := by
  have A := admitted_of_layout hy S.p3
  obtain ⟨hq, hs, hname⟩ := callOf_spec hcall
  have hcd : cd ∈ c.v.y.calls := Array.mem_of_getElem? hq
  obtain ⟨k1, k2⟩ := cols_of_layout hy S Z hcd hn hfl
  obtain ⟨fam, a1, a2, -, -, -⟩ := segs_of_layout hy S cd hcd s hs
  have hf : fam = s0 := segName_inj (a1.symm.trans hname)
  subst hf
  have hfam : famS s = fam := by
    unfold famS
    rw [a1, famOf_segName]
    rfl
  have hsn : s.n = len D fam := a2.trans (Z.len_eq fam).symm
  have hll : c.v.y.h.ll = D.lL := by
    rw [A.shape]
    exact Z.lL.symm
  have hpos : ∀ x, x < len D fam → s.pos.getD x 0 = pos D fam x := by
    intro x hx
    have r := k2 s hs x
    rw [hfam] at r
    exact r hx
  exact facEw_ewP ρ c D fam hcall hll k1 hsn hpos hsz G x0 hE hR
    (aligned_of_layout hy S hcd hs G.z (by rw [hsn]; exact hlen)) hx0 hin hX

/-- The factor against the library's ew. As facEw_ewP_of_layout; asked beside (hz): the verifier's
point of the call that callOf finds agrees with the library's point zc D z of the call of s0 on that
call's aC coordinates. Then the factor weighs index x with the library's weight ew D z s0 (x0 + x)
of entry x0 + x of the family. -/
theorem facEw_ew {h : Model.Layer.Shape} {pc : List (List String)} {c : ClaimEnv}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) {D : Dim} (Z : Sized h D) (s0 : Fam) {q : ℕ}
    {cd : CallD} {s : Seg} (hcall : c.v.callOf (segName s0) = some (q, cd, s))
    (hn : cd.segs.map (·.name) = (fams (call s0)).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D (call s0)))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) {z : ℕ → K}
    (hz : ∀ j, j < aC D (call s0) → pt ρ (c.v.zk.getD q #[]) j = zc D z (call s0) j) (G : WsGrp)
    (x0 : ℕ) (hE : (G.cls == 'E') = true) (hR : G.R = G.o * 2 ^ G.z) (hx0 : 2 ^ G.z ∣ x0)
    (hlen : 2 ^ G.z ∣ len D s0) (hin : x0 + G.R ≤ len D s0) {X : WsFac}
    (hX : c.facEw G (segName s0) x0 = some X) :
    ∀ x, x < G.R → facAt ρ X G x = ew D z s0 (x0 + x) := by
  intro x hx
  rw [facEw_ewP_of_layout ρ hy S Z s0 hcall hn hfl hsz G x0 hE hR hx0 hlen hin hX x hx]
  exact ewP_eq_ew D rfl hz (x0 + x)

/-- The same where x0 is a times, and the family's length b times, the number of the group's
indices, with a below b. The three hypotheses of facEw_ew on numbers follow. -/
theorem facEw_ew_mul {h : Model.Layer.Shape} {pc : List (List String)} {c : ClaimEnv}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) {D : Dim} (Z : Sized h D) (s0 : Fam) {q : ℕ}
    {cd : CallD} {s : Seg} (hcall : c.v.callOf (segName s0) = some (q, cd, s))
    (hn : cd.segs.map (·.name) = (fams (call s0)).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D (call s0)))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) {z : ℕ → K}
    (hz : ∀ j, j < aC D (call s0) → pt ρ (c.v.zk.getD q #[]) j = zc D z (call s0) j) (G : WsGrp)
    (x0 : ℕ) (hE : (G.cls == 'E') = true) (hR : G.R = G.o * 2 ^ G.z) {a b : ℕ}
    (hx0 : x0 = a * G.R) (hlen : len D s0 = b * G.R) (hab : a < b) {X : WsFac}
    (hX : c.facEw G (segName s0) x0 = some X) :
    ∀ x, x < G.R → facAt ρ X G x = ew D z s0 (x0 + x) := by
  refine facEw_ew ρ hy S Z s0 hcall hn hfl hsz hz G x0 hE hR ⟨a * G.o, ?_⟩ ⟨b * G.o, ?_⟩ ?_ hX
  · rw [hx0, hR]
    ring
  · rw [hlen, hR]
    ring
  · rw [hx0, hlen, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hab

#print axioms ewFrom_ewP
#print axioms facEw_ewP
#print axioms facEw_ewP_fits
#print axioms aligned_of_layout
#print axioms facEw_ewP_of_layout
#print axioms facEw_ew
#print axioms facEw_ew_mul

end OnBytes.Road
