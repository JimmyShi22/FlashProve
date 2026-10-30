-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsIff.lean: the ledger of the claims on the end values of the sumcheck of the
terms, pulled back to the early entries, holds if and only if the output rows on all end values
hold.

Cb/Pv/Lay/End/TermsA.lean has one direction (terms_pull). This file has the other. So the ledger
says no more than the rows, and at an output whose shown values are the true ones it holds.

Main names:
  `terms_back`: on entries with true tables, TermsLast gives that every form of termsCl is worth 0.
  `last_of_ev`: the output rows on all end values give TermsLast.
  `terms_pull_iff`: the pull-back of termsLed holds if and only if the rows on all end values hold.
  `trueOut`: an output with the true masked values in the places of the shown values.
  `trueOut_ev`: at trueOut the rows on all end values hold.
  `LateLay.ofNm`: which late entry has which name, from the names of the late entries alone.
Limits: as Cb/Pv/Lay/End/TermsA.lean.


-/
import Cb.Pv.Lay.End.TermsA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led rdTrue)
open Blocks (Form ext)

section Back

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J] (N : TermsNames J) (e : TermsE E)

/-- On entries with true tables, TermsLast gives that every claim on the end values holds. -/
theorem terms_back [Scl] (D : Dim) (t : Cell → E) (z : ℕ → E) (H1 H2 : ℕ → ℕ → E) (y : J → E)
    (T : TermsTrue N e D t y) (L : TermsLast N e D t z H1 H2 y) :
    ∀ f ∈ termsCl N e D, Form.val y f = 0 := by
  intro f hf
  simp only [termsCl, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with (⟨ν, hν, rfl⟩ | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩
  · have hb : ∀ n, n < 99 → Form.val y (valF (E := E) .D fun _ => N.uRow ν n) =
        ext D.lT (fun i => led t ν i n) e.rt :=
      fun n hn => val_valF D.lT t .D ν n e.rt y _ fun k' hk' => by
        have h1 : k' < 1 := hk'
        have h0 : k' = 0 := by omega
        subst h0
        exact T.row ν n hν hn
    unfold cRec
    rw [map_sub, val_hT, L.recip ν hν, Inst.Model.Ledger.val_RF, R_congr hb, sub_eq_zero]
    exact Inst.Model.Ledger.ext_R D.lT (fun m i => led t ν i m) e.rt
  · unfold cSc
    rw [map_sub, val_hT, L.sc l hl,
      val_valF D.lT t .sc l 0 e.rt y _ fun k hk => T.sc l k hl hk]
    exact sub_self _
  · have hx0 : 0 < D.nx := by
      rcases Nat.eq_zero_or_pos D.nx with h0 | h0
      · rw [h0, Nat.mul_zero] at hi
        exact absurd hi (Nat.not_lt_zero _)
      · exact h0
    have hl : i / D.nx < D.ne := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
    have hx : i % D.nx < D.nx := Nat.mod_lt _ hx0
    unfold cSel
    rw [map_sub, val_hT, L.sel _ _ hl hx,
      val_valF D.lT t .sel (i / D.nx) (i % D.nx) e.rt y _ fun k hk => T.sel _ _ k hl hx hk]
    exact sub_self _

end Back

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : TermPar0 E) {Nm J₂ : Type}

/-- The output rows on all end values give TermsLast. -/
theorem last_of_ev (U : TermsReads J₂) (o : P.tm.toSum.T.par.Out) (m : P.J → E) (u : J₂ → E)
    (h : ∀ a, P.tm.toSum.T.par.EHolds o m a) :
    TermsLast (namesT P U) (termsEAt P o) P.D (P.rd m) o.st (fun _ _ => 0)
      (fun l' j => Inst.Model.FFSeg.hhU P.D (P.rd m) (2 * l' + 1) (P.D.fe + j)
        (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) (Sum.elim m u) := by
  have key : ∀ x : ShA P.D,
      pick P.D o.vals 0 (numA P.D x) -
          P.tm.Kp.outB P.tm.Mk o * m (pick P.D P.cT P.rT (numA P.D x)) =
        sh9 P.D (recAt P.D (P.rd m) o.st (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) x := by
    intro x
    have k := (tm_ev P o m x).1 (h x)
    rw [pick_num, pick_num]
    linear_combination -k
  exact ⟨fun ν hν => key (.inl ⟨ν, hν⟩), fun l hl => key (.inr (.inl ⟨l, hl⟩)),
    fun l x hl hx => key (.inr (.inr (⟨l, hl⟩, ⟨x, hx⟩)))⟩

/-- An output with the true masked values in the places of the shown values. -/
noncomputable def trueOut (o : P.tm.toSum.T.par.Out) (m : P.J → E) : P.tm.toSum.T.par.Out :=
  { o with
    vals := fun a =>
      sh9 P.D (recAt P.D (P.rd m) o.st (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) a +
        m (P.cT a) * P.tm.Kp.outB P.tm.Mk o }

/-- At trueOut the output rows on all end values hold. -/
theorem trueOut_ev (o : P.tm.toSum.T.par.Out) (m : P.J → E) (a : ShA P.D) :
    P.tm.toSum.T.par.EHolds (trueOut P o m) m a :=
  (tm_ev P (trueOut P o m) m a).2 rfl

open Classical in
/-- Which late entry has which name, from the names of the late entries alone: the good names are
those that a late entry has. -/
noncomputable def LateLay.ofNm [Inhabited J₂] (nm : J₂ → Nm) : LateLay Nm J₂ where
  nm := nm
  at' := fun x => if h : ∃ j, nm j = x then h.choose else default
  good := fun x => ∃ j, nm j = x
  ok := fun x hx => by
    rw [dif_pos hx]
    exact hx.choose_spec

variable [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The pull-back of the ledger of the claims on the end values holds if and only if the output rows
on all end values hold. -/
theorem terms_pull_iff
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (o : P.tm.toSum.T.par.Out)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) = toAff (termsFm P.rd P.D (termsEAt P o).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k))) (m : P.J → E) :
    TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (termsLed P (readsT Y ι) o)) m ↔
      ∀ a, P.tm.toSum.T.par.EHolds o m a :=
  ⟨terms_pull P hrd Y ι fm o hfm gR gC gS m, fun h =>
    (Cb.Sub.pullL_holds _ _ _).2 ((ledOf_holds _ _).2
      (terms_back _ _ P.D (P.rd m) o.st _ _ _ (terms_true P hrd Y ι fm o hfm gR gC gS m)
        (last_of_ev P (readsT Y ι) o m _ h)))⟩

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.terms_pull_iff
