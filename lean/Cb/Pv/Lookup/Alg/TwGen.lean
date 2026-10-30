-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Alg/TwGen.lean.
Lemmas by which a sumcheck's end row is compared with the same row on plain data.

A sumcheck of the library (PscPar) leaves a row on the coefficients of its hiding polynomial
(PscPar.slU, PscPar.tU). Cb/Pv/Lookup/Out/TwV.lean has such a row on plain data: a sparse form, that
is a list of places with coefficients, and a target. This file holds definitions and proofs, for
every PscPar, PscOur and list of formats. No assembled lookup is named here.

Main names:
  `dense_nil`, `dense_cons`, `dense_one`, `dense_append`, `dense_scale`, `dense_map_range`,
    `dense_flatMap_range`: the coefficient of a sparse form (TwV.dense) under nil, cons, append,
    scale, and map and flatMap over a range.
  `pEnd`, `pAt`, `ledOf`: the names of the hiding polynomial's constant and of its coefficient of
    power t + 1 in the variable of round r; the places of a sumcheck's own masks as a record
    TwV.Led.
  `POne`, `hPsi_one`: every ψ is the constant 1; then hPsi is 1. `pOne_snoc`, `pOne_eqs`,
    `pOne_mix`, `dummy_one`, `pOne_our`: where that holds.
  `hide_sum`, `slU_dense`: PscPar.slU in closed form over lists, where every ψ is the constant 1.
  `hLast_list`, `lst_be`: the last coordinate (PscOur.lst) is the list's last. `numLE_succ`,
    `eqN_ofFn`: TwV.eqN over a list is Alg.eqk. `idxOf_perm`, `byVar_perm`: an order written as a
    list.
  `toRow`: a sparse row, spread: the library's Row. `scOf`, `scMid`: what a sumcheck's out-statement
    holds, as the flat record TwV.Sc.
  `rowU_eq`: one lemma for every sumcheck none of whose maps stays unrevealed: the library's row is
    TwV.rowU, spread. `pushJ_id`, `line_dense`, `cube_dense`, `drop_ofFn`.
Limits: `slU_dense` and `rowU_eq` stand under POne at every state; `rowU_eq` also under IsEmpty Y.B
and under three equations that the caller proves (the degrees, the incoming form as a sparse form,
the summand's value). In both, sh is idle, and so is shl in `rowU_eq`: TwV.rowU reads neither the
places nor the list of the shown values, so nothing is said on them. Two kinds of lemma stand here:
over the library's own types and ppList (Cb/Pv/Lookup/Order/TwList.lean) alone; and in the types of
Cb/Pv/Lookup/Out/TwV.lean (dense, scale, Led, hideGo, hide, SRow, rowU, eqN, byVar) and
Cb/G9/FlatStep.lean (Sc). `pOne_mix` names pfMix and pdMix of Cb/Pv/Lookup/Blocks/EndM.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwV
import Cb.Pv.Lookup.Order.TwList
import Cb.Ld.LdHideProofs
import Cb.Ld.LdPscVarsProofs
import Cb.Ld.LdLkpNumProofs
import Cb.Ld.LdLkpTreeRows

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw

/-! ## 1. Sparse forms -/
section Dense
variable {P K : Type} [DecidableEq P] [CommRing K]

theorem dense_nil (j : P) : dense ([] : List (P × K)) j = 0 := rfl

theorem dense_cons (pc : P × K) (f : List (P × K)) (j : P) :
    dense (pc :: f) j = (if pc.1 = j then pc.2 else 0) + dense f j := by
  simp [dense]

theorem dense_one (p : P) (c : K) (j : P) : dense [(p, c)] j = if p = j then c else 0 := by
  simp [dense]

theorem dense_append (f g : List (P × K)) (j : P) : dense (f ++ g) j = dense f j + dense g j := by
  simp [dense]

theorem dense_scale (c : K) (f : List (P × K)) (j : P) : dense (scale c f) j = c * dense f j := by
  induction f with
  | nil => simp [dense, scale]
  | cons a f ih =>
    have e : scale c (a :: f) = (a.1, c * a.2) :: scale c f := rfl
    rw [e, dense_cons, dense_cons, ih, mul_add]
    congr 1
    split_ifs <;> simp

theorem sum_map_range (F : ℕ → K) (n : ℕ) :
    ((List.range n).map F).sum = ∑ t ∈ Finset.range n, F t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem dense_map_range (F : ℕ → P × K) (n : ℕ) (j : P) :
    dense ((List.range n).map F) j = ∑ t ∈ Finset.range n, if (F t).1 = j then (F t).2 else 0 := by
  unfold dense
  rw [List.map_map]
  exact sum_map_range _ n

theorem dense_flatMap_range (F : ℕ → List (P × K)) (n : ℕ) (j : P) :
    dense ((List.range n).flatMap F) j = ∑ t ∈ Finset.range n, dense (F t) j := by
  induction n with
  | zero => simp [dense]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, dense_append, ih, Finset.sum_range_succ]
    simp

end Dense

/-! ## 2. The row on the hiding coefficients -/
section Hide
variable {E : Type}

/-- `pEnd l`: the name of the hiding polynomial's constant. `pAt l r t` (below): the name of its
coefficient of power t + 1 in the variable of round r (the constant's, where there is none). -/
def pEnd : (l : List (PFmt E)) → PIdx l
  | [] => ()
  | _ :: l => .inr (pEnd l)
def pAt : (l : List (PFmt E)) → ℕ → ℕ → PIdx l
  | [], _, _ => ()
  | f :: l, 0, t => if h : t < f.n then .inl ⟨t, h⟩ else .inr (pEnd l)
  | _ :: l, r + 1, t => .inr (pAt l r t)

/-- the places of a sumcheck's own masks, as a record TwV.Led -/
def ledOf {J : Type} (l : List (PFmt E)) (w : PIdx l → J) (sh : ℕ → J) : Led J :=
  ⟨fun r t => w (pAt l r t), w (pEnd l), sh⟩

variable [Field E]

/-- every ψ is the constant 1 -/
def POne : (l : List (PFmt E)) → PDats l → Prop
  | [], _ => True
  | _ :: l, d => (∀ x : E, hev d.1.psi x = 1) ∧ POne l d.2

theorem hPsi_one : ∀ (l : List (PFmt E)) (d : PDats l), POne l d → ∀ X : HPt (pVars l d),
    hPsi (pVars l d) X = 1
  | [], _, _, _ => rfl
  | _ :: l, d, h, X => by
    show hev d.1.psi X.1 * hPsi (pVars l d.2) X.2 = 1
    rw [h.1, hPsi_one l d.2 h.2, one_mul]

theorem hide_sum {J : Type} [DecidableEq J] (j : J) : ∀ (l : List (PFmt E)) (d : PDats l),
    POne l d →
    ∀ (w : PIdx l → J) (γ : PPt l) (pw : ℕ → ℕ → J) (r0 : ℕ),
        (∀ r t, pw (r0 + r) t = w (pAt l r t)) →
    (∑ i, if w (pIx l d i) = j then hSl (pVars l d) (pH l d γ) i else 0) =
      dense (hideGo pw r0 (l.map PFmt.n) (ppList l γ)) j + if w (pEnd l) = j then 1 else 0
  | [], _, _, w, _, _, _, _ => by
    show (∑ i : Unit, if w i = j then (1 : E) else 0) = dense [] j + _
    rw [Finset.univ_unique, Finset.sum_singleton, dense_nil, zero_add]
    rfl
  | f :: l, d, h, w, γ, pw, r0, hp => by
    have ih := hide_sum j l d.2 h.2 (fun i => w (.inr i)) γ.2 pw (r0 + 1)
      (fun r t => by rw [add_assoc, add_comm 1 r]; exact hp (r + 1) t)
    refine (HIdx.sum_cons (v := f.var d.1) (l := pVars l d.2) _).trans ?_
    have e2 : (∑ i : HIdx (pVars l d.2),
        if w (pIx (f :: l) d (.inr i)) = j then hSl (pVars (f :: l) d) (pH (f :: l) d γ) (.inr i)
            else 0) =
        ∑ i : HIdx (pVars l d.2), if w (.inr (pIx l d.2 i)) = j then hSl (pVars l d.2)
            (pH l d.2 γ.2) i else 0 := rfl
    have e1 : (∑ t : Fin f.n,
        if w (pIx (f :: l) d (.inl t)) = j then hSl (pVars (f :: l) d) (pH (f :: l) d γ) (.inl t)
            else 0) =
        ∑ t : Fin f.n, if w (.inl t) = j then γ.1 ^ ((t : ℕ) + 1) else 0 := by
      refine Finset.sum_congr rfl fun t _ => ?_
      show (if w (.inl t) = j then hPsi (pVars l d.2) (pH l d.2 γ.2) * γ.1 ^ ((t : ℕ) + 1) else 0) =
          _
      rw [hPsi_one l d.2 h.2, one_mul]
    have e3 : hideGo pw r0 ((f :: l).map PFmt.n) (ppList (f :: l) γ) =
        ((List.range f.n).map fun t => (pw r0 t, γ.1 ^ (t + 1))) ++ hideGo pw (r0 + 1)
            (l.map PFmt.n) (ppList l γ.2) := rfl
    rw [e3, dense_append, dense_map_range, Finset.sum_range]
    refine Eq.trans (congrArg₂ (· + ·) e1 (e2.trans ih)) ?_
    refine (add_assoc _ _ _).symm.trans ?_
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun t _ => ?_) rfl) rfl
    show _ = if pw r0 t = j then γ.1 ^ ((t : ℕ) + 1) else 0
    have : pw r0 t = w (.inl t) := by
      have := hp 0 t
      rw [add_zero] at this
      rw [this]
      show w (if h : (t : ℕ) < f.n then .inl ⟨t, h⟩ else .inr (pEnd l)) = _
      rw [dif_pos t.2]
    rw [this]

/-- THE ROW ON THE HIDING COEFFICIENTS, IN CLOSED FORM OVER LISTS: where every ψ is the constant
1. -/
theorem slU_dense (Y : PscPar E) [DecidableEq Y.J] (h1 : ∀ st, POne Y.fmt (Y.dat st)) (sh : ℕ → Y.J)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) (j : Y.J) :
    Y.slU rowB o j =
      dense (hide (ledOf Y.fmt Y.wAt sh) (Y.fmt.map PFmt.n) (ppList Y.fmt o.pt)) j + o.eps * Y.slS
          o.st j +
        o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * rowB o.st b (Y.hp o.st o.pt) j := by
  unfold PscPar.slU hide
  rw [dense_append, dense_one, hPsi_one _ _ (h1 o.st), mul_one]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ rfl) rfl
  refine Eq.trans ?_ (hide_sum j Y.fmt (Y.dat o.st) (h1 _) Y.wAt o.pt (ledOf Y.fmt Y.wAt sh).pw 0
    (fun r t => by rw [zero_add]; rfl))
  refine Finset.sum_congr rfl fun i _ => ?_
  congr

/-! ### where ψ is the constant 1 -/

theorem pOne_snoc (f : PFmt E) (e : PDat E f) (he : ∀ x : E, hev e.psi x = 1) :
    ∀ (l : List (PFmt E)) (d : PDats l), POne l d → POne (l ++ [f]) (PDats.snoc l d f e)
  | [], _, _ => ⟨he, trivial⟩
  | _ :: l, d, h => ⟨h.1, pOne_snoc f e he l d.2 h.2⟩

theorem pOne_eqs [Fintype E] (n : ℕ) : ∀ (k : ℕ) (z : Fin k → E),
    POne (List.replicate k (pfCube E n)) (pdEqs E n k z)
  | 0, _ => trivial
  | k + 1, z => ⟨fun x => hev_pvConst E n 1 x, pOne_eqs n k fun i => z i.succ⟩

theorem pOne_mix [Fintype E] : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    POne (pfMix E k dg) (pdMix E k dg z)
  | 0, _, _ => trivial
  | k + 1, dg, z => ⟨fun x => hev_pvConst E (dg 0) 1 x,
      pOne_mix k (fun i => dg i.succ) fun i => z i.succ⟩

theorem dummy_one [Fintype E] (D : ℕ) (x : E) : hev (pDummyD E D).psi x = 1 := hev_const (1 : E) x

/-- a sumcheck of the instance with the further variable: ψ = 1 throughout, if so in its own
variables -/
theorem pOne_our [Fintype E] (T : PscOur E) (h : ∀ st, POne T.fmt (T.dat st)) (st : T.par.St) : POne
    T.par.fmt (T.par.dat st) :=
  pOne_snoc (pDummy E T.DY) (pDummyD E T.DY) (dummy_one T.DY) T.fmt (T.dat st) (h st)

end Hide

/-! ## 3. The last coordinate; eq over a list; the point by variable -/
section Pts
variable {E : Type} [Field E]

omit [Field E] in
theorem hLast_list (f : PFmt E) (e : PDat E f) : ∀ (l : List (PFmt E)) (d : PDats l)
    (γ : PPt (l ++ [f])) (a : E),
    hLast l d f e (pH (l ++ [f]) (PDats.snoc l d f e) γ) = (ppList (l ++ [f]) γ).getLastD a
  | [], _, _, _ => rfl
  | _ :: l, d, γ, _ => by
    show hLast l d.2 f e (pH (l ++ [f]) (PDats.snoc l d.2 f e) γ.2) =
        (γ.1 :: ppList (l ++ [f]) γ.2).getLastD _
    rw [List.getLastD_cons]
    exact hLast_list f e l d.2 γ.2 γ.1

theorem lst_be [Fintype E] (T : PscOur E) (o : T.par.Out) :
    T.lst o.st (T.par.hp o.st o.pt) = (ppList T.par.fmt o.pt).getLastD 0 :=
  hLast_list (pDummy E T.DY) (pDummyD E T.DY) T.fmt (T.dat o.st) o.pt 0

open Cb.LdLkp in
theorem numLE_succ {k : ℕ} (b : Fin (k + 1) → Bool) :
    numLE b = (if b 0 then 1 else 0) + 2 * numLE fun i : Fin k => b i.succ := by
  unfold numLE
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun i _ => ?_)
  split_ifs
  · simp [pow_succ, mul_comm]
  · rfl

open Cb.LdLkp in
theorem eqN_ofFn : ∀ (k : ℕ) (z : Fin k → E) (b : Fin k → Bool),
    eqN (List.ofFn z) (numLE b) = Alg.eqk z b
  | 0, _, _ => by simp [eqN, Alg.eqk]
  | k + 1, z, b => by
    rw [List.ofFn_succ, numLE_succ]
    show (if ((if b 0 then 1 else 0) + 2 * numLE fun i : Fin k => b i.succ) % 2 = 1 then z 0 else 1
        - z 0) *
      eqN (List.ofFn fun i => z i.succ) (((if b 0 then 1 else 0) + 2 * numLE fun i : Fin k => b
          i.succ) / 2) = _
    have h2 : ((if b 0 then 1 else 0) + 2 * numLE fun i : Fin k => b i.succ) / 2 = numLE fun i : Fin
        k => b i.succ := by
      split_ifs <;> omega
    have h1 : (((if b 0 then 1 else 0) + 2 * numLE fun i : Fin k => b i.succ) % 2 = 1) ↔ b 0 = true
        := by
      split_ifs with h
      · simp [h]
      · simp [h]
    rw [h2, eqN_ofFn k, Alg.eqk, Alg.eqk, Fin.prod_univ_succ]
    congr 1
    exact if_congr h1 rfl rfl

/-- an order as a list: the round that binds coordinate v -/
theorem idxOf_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (v : Fin k) :
    (List.ofFn fun j : Fin k => ((σ j : Fin k) : ℕ)).idxOf (v : ℕ) = ((σ.symm v : Fin k) : ℕ) := by
  have hn : (List.ofFn fun j : Fin k => ((σ j : Fin k) : ℕ)).Nodup :=
    List.nodup_ofFn.mpr fun a b h => σ.injective (Fin.ext h)
  have hl : ((σ.symm v : Fin k) : ℕ) < (List.ofFn fun j : Fin k => ((σ j : Fin k) : ℕ)).length := by
    rw [List.length_ofFn]; exact (σ.symm v).2
  have := hn.idxOf_getElem _ hl
  rw [List.getElem_ofFn] at this
  simpa using this

theorem byVar_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (xs : List E) :
    byVar (List.ofFn fun j : Fin k => ((σ j : Fin k) : ℕ)) xs = List.ofFn fun v : Fin k => xs.getD
        ((σ.symm v : Fin k) : ℕ) 0 := by
  unfold byVar
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < k := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [← idxOf_perm σ ⟨i, hi⟩]

end Pts

/-- a sparse row, spread: the library's row -/
def toRow {P K : Type} [DecidableEq P] [CommRing K] (r : SRow P K) : Cb.LdLkp.Row K P :=
  ⟨dense r.cf, r.tg⟩

/-! ## 4. A sumcheck's out-statement as a flat record; its row -/
section Rows
open Cb.LdLkp
variable {E : Type} [Field E]

/-- What a sumcheck's out-statement holds (`scOf`: PscPar.Out; `scMid`, below: PscPar.Mid), as the
flat record TwV.Sc: eps, the challenges by round (ppList), fin, and the shown values in the order of
the list sh (`scMid`: none). The state st is left out. -/
def scOf (Y : PscPar E) (sh : List Y.A) (o : Y.Out) : Sc E :=
  ⟨o.eps, ppList Y.fmt o.pt, o.fin, sh.map o.vals⟩
def scMid (Y : PscPar E) (z : Y.Mid) : Sc E := ⟨z.eps, ppList Y.fmt z.pt, z.fin, []⟩

/-- pushing a form along the identity of names changes nothing -/
theorem pushJ_id {J : Type} [Fintype J] (c : J → E) : pushJ (id : J → J) c = c := by
  funext j
  unfold pushJ
  exact (Finset.sum_eq_single j (fun b _ hb => if_neg hb)
      (fun h => absurd (Finset.mem_univ j) h)).trans (if_pos rfl)

/-- One lemma for every sumcheck none of whose maps stays unrevealed (IsEmpty Y.B), where every ψ is
the constant 1: the library's row (slU, tU) is TwV.rowU, spread by toRow. dg, inc and S0 are the
caller's names for the degrees, the incoming form and the summand's value. -/
theorem rowU_eq (Y : PscPar E) [DecidableEq Y.J] (hB : IsEmpty Y.B)
    (h1 : ∀ st, POne Y.fmt (Y.dat st))
    (sh : ℕ → Y.J) (shl : List Y.A) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E)
        (o : Y.Out)
    (dg : List ℕ) (hdg : Y.fmt.map PFmt.n = dg)
    (inc : List (Y.J × E)) (hinc : ∀ j, Y.slS o.st j = dense inc j)
    (S0 : E) (hS : Y.S0 o.st (Y.hp o.st o.pt) o.vals = S0) :
    (⟨Y.slU rowB o, Y.tU o⟩ : Row E Y.J) = toRow (rowU (ledOf Y.fmt Y.wAt sh) dg (scOf Y shl o) inc
        S0) := by
  subst hdg hS
  unfold toRow rowU
  refine congrArg₂ Row.mk (funext fun j => ?_) rfl
  rw [slU_dense Y h1 sh, dense_append, dense_scale, hinc]
  have : (∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * rowB o.st b (Y.hp o.st o.pt) j) = 0 :=
    Finset.sum_eq_zero fun b _ => (hB.false b).elim
  rw [this, mul_zero, add_zero]
  rfl


theorem line_dense {J : Type} [DecidableEq J] (p q j : J) (β a b : E) [Decidable (j = p)]
    [Decidable (j = q)] :
    β * ((if j = p then a else 0) + if j = q then b else 0) = dense [(p, β * a), (q, β * b)] j := by
  rw [dense_cons, dense_one, mul_add]
  show _ = (if p = j then β * a else 0) + if q = j then β * b else 0
  congr 1
  · by_cases h : j = p
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun e => h e.symm), mul_zero]
  · by_cases h : j = q
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun e => h e.symm), mul_zero]

/-- eq(point, corner) at the place of the corner's bit: a sum over the cube, as a sparse form over a
range -/
theorem cube_dense {J : Type} [DecidableEq J] (pl : ℕ → J) (k : ℕ) (y : Fin k → E) (j : J) :
    (∑ b : Fin k → Bool, if pl (numLE b) = j then Alg.eqk y b else 0) =
      dense ((List.range (2 ^ k)).map fun e => (pl e, eqN (List.ofFn y) e)) j := by
  rw [dense_map_range, ← ldLkpNum_sum E k]
  exact Finset.sum_congr rfl fun b _ => by rw [eqN_ofFn]

omit [Field E] in
theorem drop_ofFn {w d : ℕ} (y : Fin (w + d) → E) :
    (List.ofFn y).drop w = List.ofFn fun r : Fin d => y (Fin.natAdd w r) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem_drop, List.getElem_ofFn, Fin.natAdd]

end Rows

end Tw3
#print axioms Tw3.dense_nil
#print axioms Tw3.dense_cons
#print axioms Tw3.dense_one
#print axioms Tw3.dense_append
#print axioms Tw3.dense_scale
#print axioms Tw3.sum_map_range
#print axioms Tw3.dense_map_range
#print axioms Tw3.dense_flatMap_range
#print axioms Tw3.hPsi_one
#print axioms Tw3.hide_sum
#print axioms Tw3.slU_dense
#print axioms Tw3.pOne_snoc
#print axioms Tw3.pOne_eqs
#print axioms Tw3.pOne_mix
#print axioms Tw3.dummy_one
#print axioms Tw3.pOne_our
#print axioms Tw3.hLast_list
#print axioms Tw3.lst_be
#print axioms Tw3.numLE_succ
#print axioms Tw3.eqN_ofFn
#print axioms Tw3.idxOf_perm
#print axioms Tw3.byVar_perm
#print axioms Tw3.pushJ_id
#print axioms Tw3.rowU_eq
#print axioms Tw3.line_dense
#print axioms Tw3.cube_dense
#print axioms Tw3.drop_ofFn
