-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlanesWorth.lean: kind K5: what the forms that K5 hands the lookup's
kind for "planes" are worth. readersOfK (Johnson/Desc/First/Att/Guest.lean) hands over, for a bit e
and a column col, the form that reads that bit's plane's table at that column, and the like for the
pin.

Main names:
  `u3at_is`: what the reader of one entry returns: the index lies in the table; the form is that one
    entry. `u3at_worth`: under AttAt and TabAt it is worth the sum over the block of the matrix's
    rows under the table's weights (tab_read, Johnson/Road/Rows/AttReadLaws.lean).
  `planes_worth`: over every seat: readersOfK seat c s = some r → ∃ i K lk, inOf seat c s = some (i,
    K) ∧ seat.look s = some lk ∧ at every ρ, W, M with AttAt ρ W tl K M (oldOf S gL i) …: r.1 e col
    = some f → f.value ρ W = Σ_{j < 2^lmb} (phiB0 or phiB1)[j] · M (NAs + 2) (col % nsg · 2^lmb + j)
    (col / nsg), nsg the matrix's rows / 2^lmb; the like for r.2 col under phiP.
Premises: c.geo = geoOf S; c.mats = matsOf tl.mats; PosG c.geo; AttAt: every table of the kind's own
list is true of the matrices M in W: that is what the smallness test is meant to give; not shown in
this file or in what it imports.
Limit: what the vectors phiB0, phiB1 and phiP are is not said here.
Used of OnBytes and Johnson/Road: AttAt, TabAt, tab_read, rdW (plain propositions and a lemma on
them); Aff.value_ent. No routine in a context and no theorem on a run.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Guest
import Johnson.Desc.First.Att.Claims.AnySeat
import Johnson.Desc.First.Att.Claims.MeanRd
import Johnson.Desc.First.Att.Claims.TablesAt
import Johnson.Desc.First.Att.Claims.InRun

set_option autoImplicit false

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf SeatC ParC LookIn)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K : ℕ} {M : Mats Kf}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}

/-- What the reader of one entry returns: the index lies in the table; the form is that entry. -/
theorem u3at_is {t col : ℕ} {f : Aff} (h : (P.Runs.gather K (P.Runs.u3at i t col)).map (·.1) = some f) :
    col < (i.t.tabLen.lookup t).getD 0 ∧ f = Aff.ent i.iU3 ((t + col) / K) ((t + col) % K) := by
  unfold P.Runs.gather at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := h
  have hy' : P.Runs.u3at i t col K #[] = some y := hy
  unfold P.Runs.u3at at hy'
  obtain ⟨y1, e1, e2⟩ := wbind_some hy'
  have hb : Decidable.decide (col < (i.t.tabLen.lookup t).getD 0) = true := by
    unfold P.Runs.mustAs at e1
    cases hd : Decidable.decide (col < (i.t.tabLen.lookup t).getD 0) with
    | true => rfl
    | false => rw [hd] at e1; cases e1
  refine ⟨of_decide_eq_true hb, ?_⟩
  unfold P.Runs.uEnt at e2
  have e3 : ((P.Runs.mustAs "internal-L-row" (K != 0 && (t + col) / K < 2 ^ 32)) >>= fun _ =>
    (pure (Aff.ent i.iU3 ((t + col) / K) ((t + col) % K)) : P.Runs.W Aff)) K y1.2 = some y := e2
  obtain ⟨y2, _, e4⟩ := wbind_some e3
  have e5 : some (Aff.ent i.iU3 ((t + col) / K) ((t + col) % K), y2.2) = some y := e4
  rw [← Option.some.inj e5]

/-- **What one entry of a table is worth**, where every table of the kind's own list is true of the matrices. -/
theorem u3at_worth (A : AttAt ρ W tl K M (oldOf S gL i) lid cf fs) {t mat len col : ℕ} {phi : Array E}
    (Tb : TabAt tl (oldOf S gL i) t mat len phi) (hm : mat < tl.NM) (hl : len ≠ 0) {f : Aff}
    (h : (P.Runs.gather K (P.Runs.u3at i t col)).map (·.1) = some f) :
    f.value ρ W = ∑ j ∈ range len, ρ.val (phi.getD j zeroE) *
      M mat (col % ((tl.mats.getD mat {}).m / len) * len + j) (col / ((tl.mats.getD mat {}).m / len)) := by
  obtain ⟨hc, rfl⟩ := u3at_is h
  rw [Aff.value_ent]
  exact tab_read A Tb hm hl hc

variable {St : Type}

/-- **What the forms that K5 hands the lookup's kind for "planes" are worth**: for a bit e and a column col: the sum over the block of the lookup's matrix's rows under the bit's weight vector at that column; the like for the pin. -/
theorem planes_worth (seat : SeatC St) (c : ParC) (s : St)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hgeo : c.geo = geoOf S) (hmats : c.mats = matsOf tl.mats)
    (hp : PosG c.geo) (hr : P.readersOfK seat c s = some r) :
    ∃ i K lk, P.inOf seat c s = some (i, K) ∧ seat.look s = some lk ∧
      ∀ (ρ : Reading Kf) (W : World Kf) (M : Mats Kf), AttAt ρ W tl K M (oldOf S gL i) lid cf fs →
        (∀ e col f, r.1 e col = some f → f.value ρ W = ∑ j ∈ range (2 ^ S.cf.lmb),
          ρ.val ((if e == 0 then lk.phiB0 else lk.phiB1).getD j zeroE) *
            M (S.cf.NAs + 2) (col % ((tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb) * 2 ^ S.cf.lmb + j)
              (col / ((tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb))) ∧
        (∀ col f, r.2 col = some f → f.value ρ W = ∑ j ∈ range (2 ^ S.cf.lmb),
          ρ.val (lk.phiP.getD j zeroE) *
            M (S.cf.NAs + 2) (col % ((tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb) * 2 ^ S.cf.lmb + j)
              (col / ((tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb))) := by
  unfold P.readersOfK at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨⟨i, K⟩, hi, rfl⟩ := hr
  obtain ⟨eg, _, _, _, _, lk, hlk, ht⟩ := inOf_some seat c s i K hi
  refine ⟨i, K, lk, hi, hlk, fun ρ W M A => ?_⟩
  have hg : i.g = geoOf S := eg.trans hgeo
  have ht' : P.tablesP i.g (matsOf tl.mats) c.nW lk i.p = some i.t := by rw [eg, ← hmats]; exact ht
  have L := tabs_look (tl := tl) (gL := gL) hg ht' (by rw [eg]; exact hp)
  have hm : S.cf.NAs + 2 < tl.NM := by
    have := A.mats.nm
    have e : (oldOf S gL i).S = S := rfl
    rw [e] at this
    omega
  have hl : 2 ^ S.cf.lmb ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos _)
  refine ⟨fun e col f hf => ?_, fun col f hf => u3at_worth A L.tPin hm hl hf⟩
  by_cases he : (e == 0) = true
  · simp only [he, if_true] at hf ⊢
    exact u3at_worth A L.tBit0 hm hl hf
  · simp only [he, if_false, Bool.false_eq_true] at hf ⊢
    exact u3at_worth A L.tBit1 hm hl hf

end K5Law
