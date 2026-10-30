-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesTieK8CellsAt.lean: the named cells of the smallness test's tie do not hang on
which of two like records, or which of two like tables of cells, they are read at; so the tie at the
witness's cells reaches the cells behind the messages' symbols.

Johnson/Meaning/PlanesTieK8Cells.lean names the integers of `TieOf tl A`: `cellZ tl A`. The
row of the smallness test's block (`k08_row`, Johnson/Desc/First/K8/LawRow.lean)
has in front of the block the tie AT THE RECORD IN THE STATE tl AND AT THE WITNESS's CELLS (Y.cellAt
(entW w)). The cells of Johnson/Meaning/ReadsCells.lean (`cellN`), at which the planes' row asks its
premise h4, are read AT THE PUBLIC RECORD tl0 AND OFF THE MESSAGES (entE). Here the two are shown
equal.

Main theorems (namespace `Meaning.Reads`).
  `cellZ_congr`: two tables of cells that agree at the record's symbol arrays, inside the sizes,
      have the same `cellZ`. No premise on the tie.
  `cellZ_same`: where the tie holds at tl and A, a record tl0 with the same numbers (`SameSize`) and
      the same symbol arrays has the same `cellZ` at A; at all places.
  `cellA_eq_cellN`: **where the tie holds at tl and the witness's cells, `cellA` there is `cellN` at
      LawLay.lean's letters at tl0 and the witness's messages**; at all places.
  `k4_host_planes_tie_cellN`: the planes' three clauses at the layers' forms FROM THE TIE at the
      witness's cells, with h4 at `cellN`, to the letter as `k4_host_planes_relA_cells` asks it.

ALL PREMISES of `k4_host_planes_tie_cellN`: hh · hq · hT · hG · hgp · e0 (as in
Johnson/Meaning/PlanesTieK8.lean) · hE (the law on entE and entW at the early cells) · htie
(the tie at tl and the witness's cells) · hpub (`SamePub tl tl0`) · hfun · hW (the world agrees with
the witness's cells at row 0 of the array o.v.iU3 below K3) · h4 (at `cellN`). Twelve. hK and hgt
are paid inside by Johnson/Meaning/PlanesTieK8Plan.lean. WHO CAN PAY: htie: `k08_row`, from what
stands behind the block, but for its error · hpub: ALL OF IT, at the record behind a yes of the step
that closes the list of tables: `quiet_front` (Johnson/Meaning/QuietFront.lean); or its layout half
by the condition in front of the block (`lay_onA`) and its numbers' half by `sameSize_of_place` from
a yes of the block and `PlaceRec p tl0` (that e0's tl0 has the place's numbers is shown by nobody) ·
hE: `hE_of_inSig`, as Johnson/Desc/First/K8/LawInSig.lean [not in this library] calls it, under its
own premises
(`hE_of_inSig` stands in Johnson/Desc/First/TailClaims/LayAt.lean, which this file does not import)
· hfun, hW, h4: as before.
OBJECT · LETTERS. Object: `TieOf`, `SamePub`, `thetaRec`; the library's `cellsOf`;
the layers' plain hearing. No seated description is named.
Letters: Johnson/Desc/First/K8/LawLay.lean's J, Y, cs, l, seat', arr, entE, entW; tl, tl0, A, ν, W:
free, under
"for all".
Compiled with the whole library.


Limits. The tie, hE, hpub, hfun, hW and h4 are premises. No member is shown. No draw, no error.
Nothing on soundness.
-/
import Johnson.Meaning.PlanesTieK8Cells
import Johnson.Meaning.PlanesTieK8Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansG)
open OnBytes.K.Kc
open VerifiableInference.Desc.First.K8 (TieOf SamePub SameSize pack_congr)
open Meaning.Planes

/-- Two tables of cells that agree at the record's symbol arrays have the same named integers. -/
theorem cellZ_congr (tl : HTailF2) {A A' : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
      ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
        A (tl.gtTree.getD μ 0) i' c = A' (tl.gtTree.getD μ 0) i' c) :
    cellZ tl A = cellZ tl A' := by
  have e : symsA tl A = symsA tl A' :=
    funext fun μ => funext fun i' => funext fun c => hA μ μ.2 c c.2 i' i'.2
  funext μ r c
  unfold cellZ
  rw [e]

/-- Where the tie holds, a record with the same numbers and the same symbol arrays has the same
named integers. -/
theorem cellZ_same {tl tl0 : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieOf tl A)
    (hz : SameSize tl tl0) (hgt : tl.gtTree = tl0.gtTree) : cellZ tl A = cellZ tl0 A := by
  obtain ⟨a, h1, h2, _⟩ := h
  funext μ r c
  by_cases hin : μ < tl.NM ∧ c < (tl.mats.getD μ {}).k ∧ r < (tl.mats.getD μ {}).m
  · have hin0 : μ < tl0.NM ∧ c < (tl0.mats.getD μ {}).k ∧ r < (tl0.mats.getD μ {}).m := by
      rw [← hz.nm, ← hz.k, ← hz.m]
      exact hin
    rw [← cellZ_of_packs h1 h2 hin.1 hin.2.1 hin.2.2]
    refine cellZ_of_packs (tl := tl0) (fun μ hμ c hc i hi => ?_) (fun μ hμ c hc i' hi' => ?_)
      hin0.1 hin0.2.1 hin0.2.2
    · rw [← hz.nm] at hμ
      rw [← hz.k] at hc
      rw [← hz.m] at hi
      exact h1 μ hμ c hc i hi
    · rw [← hz.nm] at hμ
      rw [← hz.k] at hc
      rw [← hz.m] at hi'
      rw [← hgt, ← pack_congr (hz.m μ) _ (fun i => a μ i c)]
      exact h2 μ hμ c hc i' hi'
  · have hin0 : ¬ (μ < tl0.NM ∧ c < (tl0.mats.getD μ {}).k ∧ r < (tl0.mats.getD μ {}).m) := by
      rw [← hz.nm, ← hz.k, ← hz.m]
      exact hin
    unfold cellZ
    rw [dif_neg hin, dif_neg hin0]

section AtTheLetters
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.Sound OnBytes.Maker Johnson.Pack

variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)

/-- **Where the tie holds at the record in the state and the witness's cells, its named cells are
the cells behind the symbols of the witness's messages at the public record.** -/
theorem cellA_eq_cellN
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (hgt : tl0.NM ≤ tl0.gtTree.size) {tl : HTailF2} (hpub : SamePub tl tl0)
    (w : Wit Cells Tok MsgT) (htie : TieOf tl fun a r c => Y.cellAt (entW w) a r c) (μ r c : ℕ) :
    cellA tl (fun a r c => Y.cellAt (entW w) a r c) μ r c =
      cellN tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (K8.symL Y tl0 entE)
        (u3L Y tl0 entE) (digL Y tl0 entW)) (msgsOf cs l seat' arr w) μ r c := by
  rw [cellN_eq_cellA]
  unfold cellA
  rw [cellZ_same htie hpub.toSameSize hpub.gt]
  rw [cellZ_congr tl0 (A := fun a r c => Y.cellAt (entW w) a r c)
    (A' := fun a r c => Y.cellAt (entE (msgsOf cs l seat' arr w)) a r c)
    fun μ hμ c _ i' _ => (cellAt_congr Y _ _ _ _ _ fun j hj => hE w j (by
      rw [hj]
      exact Port.early_sym (Nat.lt_of_lt_of_le hμ hgt) i' c)).symm]

/-- **The three clauses at the layers' forms, from the smallness test's tie at the witness's cells,
with the lookup's cells asked for at THE cells behind the symbols**, as
`k4_host_planes_relA_cells` asks for them. tl0: the plan's record, closed with the public shapes. -/
theorem k4_host_planes_tie_cellN {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp)
    (e0 : tl0 = Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (w : Wit Cells Tok MsgT) {tl : HTailF2}
    (htie : TieOf tl fun a r c => Y.cellAt (entW w) a r c) (hpub : SamePub tl tl0)
    (hfun : tl.funs = o.funs) (W : World Cb.Gl.E)
    (hW : ∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = Y.cellAt (entW w) o.v.iU3 0 pos)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (K8.symL Y tl0 entE)
        (u3L Y tl0 entE) (digL Y tl0 entW)) (msgsOf cs l seat' arr w) (matIx o.v.y).iB r c =
        ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
        (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  have hgt : tl0.NM ≤ tl0.gtTree.size := by
    rw [e0]
    exact k4_hgt hG hgp _
  have h4' : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellA tl (fun a r c => Y.cellAt (entW w) a r c) (matIx o.v.y).iB r c = ν (.cell r c) :=
    fun r hr c hc => (cellA_eq_cellN Y tl0 cs l seat' arr entE entW hE hgt hpub w htie _ r c).trans
      (h4 r hr c hc)
  rw [e0] at hpub
  exact k4_host_planes_tie_pub_cells hh hq hT hG hgp htie hpub hfun (k4_hK hh hG hgp) ν W hW h4'

end AtTheLetters

#print axioms cellZ_congr
#print axioms cellZ_same
#print axioms cellA_eq_cellN
#print axioms k4_host_planes_tie_cellN

end Meaning.Reads
