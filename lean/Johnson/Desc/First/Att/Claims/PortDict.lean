-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortDict.lean: kind K5: the dictionary LateAt holds by construction of
the late entries read off the world; and where "the tables are true" is spent.

Main names:
  `uAt W h K3 Y tabOf place`: the late entry j holds the entry of the vector of tables at the place
    of j's own name (Y.nm j).
  `late_at`: LateAt W h K3 Y tabOf place (uAt …), for every record Y of the late entries' names,
    every world, all beginnings and places. (lateAt_wit, Johnson/Road/Rows/AttPortWit.lean, says it
    of the one record lateW.) So the thirteen parts of Johnson/Desc/First/Att/Claims/PortParts.lean
    hold at ul := uAt … with no premise on the tables' truth.
  `ownCl_pull_of_agree`: under Cb.Sub.Agree (attA L u) (P.msg m) ul (each late entry is worth its
    meant form on the early entries) the ledger's claims at (P.msg m, ul) are its pull-backs at
    P.msg m.
  `late_of_agree`, `tabOf_six`.
Two forms of the premise that the tables are true: LateAt at the meant values (ownCl_pull) speaks of
the good names alone; Agree … (uAt …) speaks of every late entry, and asks more where a late entry's
own name is not good. The two are one where every late entry's name is good. Neither is shown in
this file or in what it imports.
tabOfAtt h (Johnson/Road/Rows/AttPlaces.lean), with lateTabs_att, firstTabs_att and tabOf_six, says
where the 21 tables begin; the two units' tables are numbers 0 and 1 of h.t.score.
Used: LateAt, rdW (plain definitions); the library's LateLay, Cb.Sub.Agree, pullF, pullF_holds,
ownCl, attA.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPlaces
import Johnson.Desc.First.Att.Claims.PortParts

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (LateLay AttTab EndLay JoinLay ownCl attA)

variable {Kf : Type}

/-- The late entries read off the world: the late entry j holds the entry of the vector of tables at the place of j's own name. -/
def uAt {J₂ : Type} (W : World Kf) (h : Attention.Heard) (K3 : ℕ) (Y : LateLay AttTab J₂)
    (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) (j : J₂) : Kf :=
  rdW W h.iU3 K3 (tabOf (Y.nm j).1 + place (Y.nm j).1 (Y.nm j).2)

/-- **The dictionary holds of the late entries read off the world**, whatever the names' record. -/
theorem late_at {J₂ : Type} (W : World Kf) (h : Attention.Heard) (K3 : ℕ) (Y : LateLay AttTab J₂)
    (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) :
    LateAt W h K3 Y tabOf place (uAt W h K3 Y tabOf place) := by
  intro T r hr
  unfold uAt
  rw [Y.ok _ hr]

variable [Field Kf] [Fintype Kf] {M X : Type} {J₂ : Type} [Fintype J₂] [DecidableEq J₂]
  {P : OwnPar Kf M X} {L : EndLay P J₂} {Q : JoinLay P} {u : P.Run} {ul : J₂ → Kf} {m : M}

/-- **Where "the tables are true" is spent.** -/
theorem ownCl_pull_of_agree (hA : Cb.Sub.Agree (attA L u) (P.msg m) ul)
    (hh : ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) ul)) :
    ∀ f ∈ ownCl L Q u, (Cb.Sub.pullF (attA L u) f).Holds (P.msg m) := by
  have e : ul = fun i => (attA L u i).val (P.msg m) := funext hA
  rw [e] at hh
  exact ownCl_pull hh

omit [Fintype Kf] [Fintype J₂] [DecidableEq J₂] in
/-- The second form of the premise gives the first. -/
theorem late_of_agree {J₁ : Type} [Fintype J₁] {W : World Kf} {h : Attention.Heard} {K3 : ℕ}
    {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {place : AttTab → Raw → ℕ}
    {a : J₂ → TWhole.Aff Kf J₁} {x : J₁ → Kf} (hA : Cb.Sub.Agree a x (uAt W h K3 Y tabOf place)) :
    LateAt W h K3 Y tabOf place fun j => (a j).val x := by
  intro T r hr
  show (a (Y.at' (T, r))).val x = _
  rw [← hA]
  exact late_at W h K3 Y tabOf place T r hr

/-- Where the six tables begin that neither LateTabs nor FirstTabs names. -/
theorem tabOf_six (h : Attention.Heard) :
    tabOfAtt h .tA = h.t.tA ∧ tabOfAtt h .hW = h.t.hW ∧ tabOfAtt h .hX = h.t.hX ∧
      tabOfAtt h .tO = h.t.tO ∧ tabOfAtt h .tMm = (h.t.score.getD 0 default).tM ∧
      tabOfAtt h .tMd = (h.t.score.getD 1 default).tM := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end K5Law
