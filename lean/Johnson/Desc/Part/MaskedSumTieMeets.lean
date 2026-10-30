--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumTieMeets.lean: PartRowLaw's PREMISES CAN BE MET TOGETHER, AT EVERY SIZE OF A PLAIN SUMCHECK.
PartRowLaw (Johnson/Desc/Part/MaskedSumLaw.lean) is an implication. This file shows that its premises do not shut each other
out: for every number of variables, all degrees from 1 up, every degree in Y, every reading, and ALL lists of the lengths
that the reading of the rounds asks, with a beta that reads other than 0, there are a typed plain sumcheck of that size, a
world, a record as heard, a ledger and entries at which every premise holds and «row» returns.
HOW LITTLE THAT IS. The typed sumcheck is the poorest of its size: no map, the summand 0, the incoming form 0; the world's
slots and the entries are all 0; the start form is the constant target. So (D1) (D2) (D4) hold for trivial reasons. THAT
THEY HOLD AT A REAL KIND's SUMMAND, MASKS AND INCOMING FORM IS NOT SHOWN HERE: it stays the calling kind's to show.
  flat           : the poorest plain sumcheck of a size.
  place_const    : a constant mask stands at every place.
  hideRun_retA   : a run of values (an array) goes under slots that are there and free.
  rowLaw_meets   : the statement above.
  rowLaw_applies : PartRowLaw applied at what rowLaw_meets gives: a test that the premises listed are the law's own.

-/
import Johnson.Desc.Part.MaskedSumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-- The poorest plain sumcheck of a size: no map, the summand 0, the incoming form 0. -/
def flat (K : Type) [Field K] [Fintype K] (nv : ℕ) (deg : Fin nv → ℕ) (DY : ℕ) : PlainSc K where
  nv := nv
  deg := deg
  A := Empty
  DY := DY
  St := Unit
  J := Unit
  map := fun _ _ a _ => a.elim
  S := fun _ _ _ => 0
  inc := fun _ _ => 0
  wAt := fun _ => ()
  cAt := fun a => a.elim

theorem place_const {K : Type} [Field K] (c : K) : ∀ (l : List (Cb.HVar K)) (s : ℕ) (i : Cb.HIdx l),
    OnBytes.Road.Hd.place (fun _ => c) l s i = c
  | [], _, _ => rfl
  | [_], _, Sum.inl _ => rfl
  | [_], _, Sum.inr _ => rfl
  | _ :: _ :: _, _, Sum.inl _ => rfl
  | v :: v' :: l, s, Sum.inr i => place_const c (v' :: l) (s + v.n) i

theorem hideRun_retA (F : Fork) (first : Nat) (v : Array E) (factor : E) (hs : F.gotF.size = F.ns)
    (hn : first + v.size ≤ F.ns) (hf : ∀ j, first ≤ j → j < first + v.size → F.gotF.getD j true = false) :
    ∃ G, F.hideRun first v factor = some G := by
  have hl : v.toList.length = v.size := by simp
  obtain ⟨x, hx⟩ := hideSteps_ret factor v.toList first F hs (by rw [hl]; exact hn)
    (fun j a b => hf j a (by rw [← hl]; exact b))
  rw [Array.foldlM_toList] at hx
  refine ⟨x.2, ?_⟩
  unfold Fork.hideRun
  rw [hx]

/-- The record as the hearing gives it, of these lists, at the constant start form t and the first slot 0. -/
def heardOf (degs : List Nat) (DY : Nat) (t mu eps : E) (rs : List (List E × E)) (sentY : List E) (beta : E) : Heard :=
  { start := Aff.ofConst t, target := t, eps := eps,
    claim := after (varsOf degs DY) (rs ++ [(sentY, beta)]) (addE mu (mulE eps t)), first := 0,
    vars := varsOf degs DY, r := rs.map (·.2) ++ [beta], sEnd := 0 }

theorem row_returns (h : Heard) (h0 : h.first = 0) (S0 : E) :
    ∃ f G, row h S0 {} (({} : Fork).slots (hidingAt (h.vars.zip h.r)).1.length) = some (f, G) := by
  obtain ⟨G, hG⟩ := hideRun_retA (({} : Fork).slots (hidingAt (h.vars.zip h.r)).1.length) h.first
    (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) (by simp [Fork.slots])
    (by simp [Fork.slots, h0])
    (by
      intro j _ b
      have b' : j < (hidingAt (h.vars.zip h.r)).1.length := by simpa [h0] using b
      simp [Fork.slots, Array.getD_eq_getD_getElem?, b'])
  refine ⟨rowAff h S0 {}, G, ?_⟩
  unfold row
  simp only [hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

/-- **PartRowLaw's premises can be met together, at every size.** -/
theorem rowLaw_meets (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nv : ℕ) (deg : Fin nv → ℕ) (DY : ℕ)
    (h1 : ∀ i, 1 ≤ deg i) (t mu eps : E) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) :
    ∃ (W : World K) (h : Heard) (m : (flat K nv deg DY).J → K) (F G : Fork) (f : Aff),
      (∀ i, 1 ≤ (flat K nv deg DY).deg i) ∧ (∀ st, HFixs.OK _ ((flat K nv deg DY).fix st)) ∧
      AsHeard h (List.ofFn (flat K nv deg DY).deg) (flat K nv deg DY).DY mu rs sentY beta ∧
      row h zeroE {} F = some (f, G) ∧
      (flat K nv deg DY).our.par.W () m =
        OnBytes.Road.Hd.place W.slot ((flat K nv deg DY).our.par.vars ()) h.first ∧
      (flat K nv deg DY).our.par.inc () m = ρ.val h.target - h.start.value ρ W ∧
      (flat K nv deg DY).S ()
        (ldPartIni (flat K nv deg DY).nv (flat K nv deg DY).deg (pDummy K (flat K nv deg DY).DY)
          (plainOut ρ (flat K nv deg DY) () h.target mu h.eps rs sentY beta hβ (fun a => a.elim)).pt)
        (plainOut ρ (flat K nv deg DY) () h.target mu h.eps rs sentY beta hβ (fun a => a.elim)).vals =
          ρ.val zeroE := by
  obtain ⟨f, G, hr⟩ := row_returns (heardOf (List.ofFn deg) DY t mu eps rs sentY beta) rfl zeroE
  refine ⟨⟨fun _ => 0, fun _ _ _ => 0⟩, heardOf (List.ofFn deg) DY t mu eps rs sentY beta, fun _ => 0, _, G, f, h1,
    fun st => fits_ok ρ _ _ _ _ (plain_fits ρ (flat K nv deg DY) h1 st), ⟨rfl, rfl, rfl⟩, hr, ?_, ?_, ?_⟩
  · funext i
    exact (place_const (0 : K) _ _ i).symm
  · have e : (flat K nv deg DY).our.par.inc () (fun _ => 0) = 0 := Finset.sum_eq_zero fun j _ => mul_zero _
    refine e.trans ?_
    show (0 : K) = ρ.val t - (Aff.ofConst t).value ρ _
    rw [Aff.value_ofConst, sub_self]
  · show (0 : K) = ρ.val zeroE
    rw [ρ.zero]

/-- The law, applied there: that this is accepted by Lean shows that what rowLaw_meets lists ARE PartRowLaw's premises, to the
letter, beside the two on the lists' lengths. -/
theorem rowLaw_applies (K : Type) [Field K] [Fintype K] (ρ : Reading K) (nv : ℕ) (deg : Fin nv → ℕ) (DY : ℕ)
    (h1 : ∀ i, 1 ≤ deg i) (t mu eps : E) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) (hl : rs.map (·.1.length) = List.ofFn deg) (hY : sentY.length = DY) :
    ∃ (W : World K) (h : Heard) (m : (flat K nv deg DY).J → K) (f : Aff),
      (f.value ρ W = 0 ↔ (flat K nv deg DY).our.par.UHolds
        (plainOut ρ (flat K nv deg DY) () h.target mu h.eps rs sentY beta hβ (fun a => a.elim)) m) := by
  obtain ⟨W, h, m, F, G, f, a1, a2, a3, a4, a5, a6, a7⟩ := rowLaw_meets K ρ nv deg DY h1 t mu eps rs sentY beta hβ
  exact ⟨W, h, m, f, partRowLaw K ρ (flat K nv deg DY) a1 a2 W h rs sentY beta hβ (fun a => a.elim) mu zeroE () m F G f
    a3 hl hY a4 a5 a6 a7⟩

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.rowLaw_meets
#print axioms VerifiableInference.Desc.Part.MaskedSum.rowLaw_applies
