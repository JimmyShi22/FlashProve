-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveValAt.lean: CONDITIONAL: THE LAWS OF
Johnson/Desc/K5/Honest/Law/ReadsLiveAt.lean ONCE MORE, AT VALUES: under the test on what the own
rounds of an attention segment heard, behind a yes of the quiet step that makes and closes the list
of tables, the two tables' weights do not READ 0 (`Reading.gl.val … ≠ 0`), where ReadsLiveAt.lean
says "is not the word 0"; and two facts on public numbers beside: the table's length is not 0, and
it divides the number of rows of the plan's matrix.

Why. A word that is not below the prime can be other than the word 0 and read 0: so "is not the word
0" does not give "does not read 0". The proofs of `eqTab_nz` and `blockRows_eq_nz`
(Johnson/Desc/K5/Honest/Law/EqTabNz.lean) have the value in hand (`eqTab_val_ne`) and hand on the
weaker fact. Whoever counts on the tables' weights wants the value.

Main names:
  `blockRows_val_ne`, `blockRows_eq_val_ne`: an entry of a product of two tables does not read 0.
  `tables_liveV`: the two written weights, at values.
  `LiveV`, `Live2V`: one table of the end; **the end**: on each of the matrices NAs and NAs + 3
    the state's list holds a table in vector number 2, of a length that is not 0 and divides the
    number of rows of the plan's matrix, no entry of whose weights below that length reads 0.
  `fits_at`: what the library's test on a laid table says, in the plan's own list of matrices.
  `funs_liveV`: **behind a yes of the quiet step.**

How. `tables_liveV` and `funs_liveV` repeat `tables_live` and `funs_live` (ReadsLiveAt.lean), and
`blockRows_val_ne`, `blockRows_eq_val_ne` repeat `blockRows_nz`, `blockRows_eq_nz` (EqTabNz.lean),
the end exchanged. The two facts on numbers: the library's `tablesP_fits`
(Johnson/Desc/First/Att/Claims/ReadsApart.lean): every table that the function of the tables lays
passes `fits` (Johnson/Desc/First/Att/TablesP.lean).

Limits. As ReadsLiveAt.lean's. THE MATRIX IS THE PLAN's (A.mats, which is A.seam.tl.mats by its
definition), NOT THE STATE's (tl.mats): that the two lists are one at that state is not shown here.
Two of the segment's matrices.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadsLiveAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE mulE)
open OnBytes.Model (Reading HTailF2 HFun TMat)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts)
open K5Law (Table layFrom laidBy)

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- An entry of a product of two tables does not read 0 where neither factor does. -/
theorem blockRows_val_ne (low tk : Array E) {r i : ℕ} (hr : r < low.size) (hi : i < tk.size)
    (h1 : ρ.val (low.getD r zeroE) ≠ 0) (h2 : ρ.val (tk.getD i zeroE) ≠ 0) :
    ρ.val ((P.blockRows low tk).getD (r * tk.size + i) zeroE) ≠ 0 := by
  have e : (P.blockRows low tk).getD (r * tk.size + i) zeroE =
      mulE (low.getD r zeroE) (tk.getD i zeroE) := OnBytes.Road.blockRows_getD low tk hr hi
  rw [e, ρ.mul]
  exact mul_ne_zero h1 h2

/-- **No entry of a product of two tables of equality weights reads 0**, at two points none of whose
coordinates reads 0 or 1. Conditional: ha, hb; hx: the entry's number is below the product's
length. -/
theorem blockRows_eq_val_ne {a b : Array E} (ha : ∀ j < a.size, pt ρ a j ≠ 0 ∧ pt ρ a j ≠ 1)
    (hb : ∀ j < b.size, pt ρ b j ≠ 0 ∧ pt ρ b j ≠ 1) {x : ℕ}
    (hx : x < 2 ^ a.size * 2 ^ b.size) :
    ρ.val ((P.blockRows (P.eqTab a) (P.eqTab b)).getD x zeroE) ≠ 0 := by
  have hB : 0 < 2 ^ b.size := Nat.two_pow_pos _
  have h1 : x / 2 ^ b.size < 2 ^ a.size := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have h2 : x % 2 ^ b.size < 2 ^ b.size := Nat.mod_lt _ hB
  have e := blockRows_val_ne ρ (P.eqTab a) (P.eqTab b) (r := x / 2 ^ b.size) (i := x % 2 ^ b.size)
    (by rw [size_eqTab]; exact h1) (by rw [size_eqTab]; exact h2) (eqTab_val_ne ρ ha h1)
    (eqTab_val_ne ρ hb h2)
  rw [size_eqTab, Nat.div_add_mod' x (2 ^ b.size)] at e
  exact e

end

/-- **Under the test no entry of the two written weights reads 0.** Conditional: hp: the function of
the points returns; hR: the test. -/
theorem tables_liveV {g : Geo} {zk : Array (Array E)} {hh : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk hh L = some p) (hR : heardReads g hh = true) :
    (∀ c < 2 ^ g.lt,
      Reading.gl.val ((P.eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))).getD c zeroE) ≠ 0) ∧
    ∀ x < 2 ^ g.ls * 2 ^ g.lt,
      Reading.gl.val
        ((P.blockRows (P.eqTab (P.lastCoords (p.x.rc g) g.ls)) (P.eqTab (p.x.ri g))).getD x
          zeroE) ≠ 0 := by
  have PA := K5Law.points_are hp
  unfold heardReads at hR
  simp only [Bool.and_eq_true, beq_iff_eq] at hR
  obtain ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, a1⟩, a2⟩, a3⟩ := hR
  have e1 : p.d.scE.r.extract g.lgk (g.lgk + g.lt) = ptE g hh := by
    rw [PA.scE]
    rfl
  have e2 : p.x.ri g = ptFi g hh := by
    unfold P.MaxP.ri
    rw [PA.scF]
    rfl
  have e3 : P.lastCoords (p.x.rc g) g.ls = ptFc g hh := by
    unfold P.MaxP.rc
    rw [PA.scF]
    rfl
  rw [e1, e2, e3]
  exact ⟨fun c hc => eqTab_val_ne Reading.gl (pt_of_all a1) (by rw [s1]; exact hc), fun x hx =>
    blockRows_eq_val_ne Reading.gl (pt_of_all a3) (pt_of_all a2) (by rw [s3, s2]; exact hx)⟩

/-- One table of the end: in vector number 2, on matrix mu, of length n; its length is not 0 and
divides the number of rows of matrix mu of the list mats (taken as 0 if mats has no matrix mu, so
that this then holds for any length; `LiveV` does not ask that the matrix is there); no entry of its
weights below its length reads 0. -/
def LiveV (mats : Array TMat) (mu n : ℕ) (Fn : HFun) : Prop :=
  Fn.mat = mu ∧ Fn.len = n ∧ Fn.tree = 2 ∧ 0 < Fn.len ∧ (mats.getD mu {}).m % Fn.len = 0 ∧
    ∀ c < Fn.len, Reading.gl.val (Fn.phi.getD c zeroE) ≠ 0

/-- **The end, at values.** mats: the plan's list of matrices. -/
def Live2V (g : Geo) (mats : Array TMat) (s : S) : Prop :=
  ∃ tl, s.tl? = some tl ∧ (∃ Fn ∈ tl.funs.toList, LiveV mats g.NAs g.T Fn) ∧
    ∃ Fn ∈ tl.funs.toList, LiveV mats (g.NAs + 3) (2 ^ g.la) Fn

/-- **What the library's test on a laid table says, in the plan's own list of matrices**: the length
is not 0 and divides the matrix's number of rows. Conditional: h: the test's yes at the list of
pairs (rows, columns) made of mats. -/
theorem fits_at {mats : Array TMat} {mu len n : ℕ}
    (h : P.fits (mats.map fun M => (M.m, M.k)) mu len n = true) :
    0 < len ∧ (mats.getD mu {}).m % len = 0 := by
  unfold P.fits at h
  rw [Array.getElem?_map] at h
  cases hm : mats[mu]? with
  | none =>
    rw [hm] at h
    cases h
  | some M =>
    rw [hm] at h
    have h' : (len != 0 && M.m % len == 0 && n == M.k * (M.m / len)) = true := h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h'
    refine ⟨Nat.pos_of_ne_zero h'.1.1, ?_⟩
    rw [Array.getD_eq_getD_getElem?, hm]
    exact h'.1.2

/-- **BEHIND A YES OF THE QUIET STEP, AT VALUES.** Conditional: h: the yes; h5: what the segment's
own rounds heard, in the state in front; hR: the test on it. -/
theorem funs_liveV (A : OnBytes.Attention.Plan) {m s : S} (h : readsAtSO A m = .ok s) {hh : Heard}
    (h5 : m.heard5? = some hh) (hR : heardReads (P.parCOf A).geo hh = true) :
    Live2V (P.parCOf A).geo A.mats s := by
  obtain ⟨a, hh', g, p, t, _, e5, _, _, hp, ht, _, _, rfl⟩ := (readsAtSO_iff A m s).1 h
  obtain rfl : hh' = hh := Option.some.inj (e5.symm.trans h5)
  unfold P.ptsFrom at hp
  obtain ⟨Lf, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨_, _, z1, z2⟩ := tables_live hp' hR
  obtain ⟨l1, l2⟩ := tables_liveV hp' hR
  have hl := K5Law.tablesP_laid ht
  have hfit := List.all_eq_true.1 (K5Law.tablesP_fits ht)
  have hok : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = true := by
    rw [← K5Law.tablesP_isSome, ht]
    rfl
  have f1 : (P.eqTab (p.d.scE.r.extract (P.parCOf A).geo.lgk
      ((P.parCOf A).geo.lgk + (P.parCOf A).geo.lt))).size = (P.parCOf A).geo.T :=
    K5Law.forced hok .rowsAtProduct (by simp [P.reads]) (by simp [K5Law.theTen])
  have f2 : (P.blockRows (P.eqTab (P.lastCoords (p.x.rc (P.parCOf A).geo) (P.parCOf A).geo.ls))
      (P.eqTab (p.x.ri (P.parCOf A).geo))).size = 2 ^ (P.parCOf A).geo.la :=
    K5Law.forced hok .queriesAtIndex (by simp [P.reads]) (by simp [K5Law.theTen])
  have back : ∀ f : P.Fun1, f ∈ t.funs.toList → funBack f ∈ ((tabsBack t).funs).toList := by
    intro f hf
    show funBack f ∈ (t.funs.map funBack).toList
    rw [Array.toList_map]
    exact List.mem_map_of_mem hf
  have mr : ∀ {x : Table} {X Y : List Table}, x ∈ Y → x ∈ X ++ Y := fun h =>
    List.mem_append_right _ h
  have ml : ∀ {x : Table} {Y : List Table}, x ∈ [x] ++ Y := List.mem_append_left _
    (List.mem_singleton.2 rfl)
  have m1 : (⟨(P.parCOf A).geo.NAs, (P.parCOf A).geo.T,
      P.eqTab (p.d.scE.r.extract (P.parCOf A).geo.lgk ((P.parCOf A).geo.lgk + (P.parCOf A).geo.lt)),
      (P.parCOf A).geo.fillH⟩ : Table) ∈
      laidBy (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb g) p := by
    unfold laidBy
    exact mr (mr (mr (mr (mr (mr ml)))))
  have m2 : (⟨(P.parCOf A).geo.NAs + 3, 2 ^ (P.parCOf A).geo.la,
      P.blockRows (P.eqTab (P.lastCoords (p.x.rc (P.parCOf A).geo) (P.parCOf A).geo.ls))
        (P.eqTab (p.x.ri (P.parCOf A).geo)),
      (P.parCOf A).geo.fillQ * (P.parCOf A).geo.T / 2 ^ (P.parCOf A).geo.la⟩ : Table) ∈
      laidBy (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb g) p := by
    unfold laidBy
    exact mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr ml))))))))))))))
  obtain ⟨p1, q1⟩ := fits_at (mats := A.mats) (hfit _ m1)
  obtain ⟨p2, q2⟩ := fits_at (mats := A.mats) (hfit _ m2)
  refine ⟨_, rfl, ?_, ?_⟩
  · obtain ⟨st, hs⟩ := mem_layFrom _ 0 m1
    rw [← hl] at hs
    exact ⟨_, back _ hs, rfl, rfl, rfl, p1, q1, fun c hc => l1 c (by rw [← z1, f1]; exact hc)⟩
  · obtain ⟨st, hs⟩ := mem_layFrom _ 0 m2
    rw [← hl] at hs
    exact ⟨_, back _ hs, rfl, rfl, rfl, p2, q2, fun x hx => l2 x (by rw [← z2, f2]; exact hx)⟩

end H2K5.Honest

#print axioms H2K5.Honest.blockRows_val_ne
#print axioms H2K5.Honest.blockRows_eq_val_ne
#print axioms H2K5.Honest.tables_liveV
#print axioms H2K5.Honest.fits_at
#print axioms H2K5.Honest.funs_liveV
