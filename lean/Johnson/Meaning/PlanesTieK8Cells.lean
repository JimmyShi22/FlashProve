-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesTieK8Cells.lean: the smallness test's tie at NAMED cells: the integers of the
tie are the unpacking of the committed symbols.

`TieOf tl A` (Johnson/Desc/First/K8/LawItems.lean) says "there are integers": small, with the
packing that the table of cells A shows at the record's symbol arrays, and with the stated sums at
the places of the tables of reads. Whoever spends the tie must say of which cells a later law
speaks; of integers under "there are" nobody can say that. Small integers with a given packing are
unique (the library's `cellsOf_of_packs`, Cb/Pv/Tail/Base.lean; the no-wrap premise is paid at every
record's sizes by `sizeOf_uniq`, OnBytes/Tie/Pv/Tail/SizeUniq.lean). So they are named here, as a
function of tl's numbers, its symbol arrays' numbers and A's cells at these arrays alone.

Main names (namespace `Meaning.Reads`).
  `symsA tl A`: the symbols that A shows: (matrix μ, row of symbols i', column c) ↦
      A (tl.gtTree.getD μ 0) i' c, at the record's sizes.
  `cellZ tl A μ r c`: THE integer at (row r, column c) of matrix μ behind these symbols: the
      library's `cellsOf` inside the record's sizes, 0 outside. `cellA`: its image in the field.
  `cellA_syms`: inside the sizes `cellA` is the library's `cellValS` of `symsA tl A`.
  `cellZ_of_packs`: any integers that are small and have A's packing are `cellZ` inside the sizes.
  `TieWith tl A a`: the three clauses of `TieOf` at given integers a. `tieOf_iff`: TieOf is "there
      is a with TieWith".
  `tie_named`: **`TieOf tl A` gives `TieWith tl A (cellZ tl A)`**: nothing is left under "there is".
  `readsAll_of_tie_cells`: **`TieOf tl A` gives Fo.ReadsAll at `cellA tl A`**, at every table of
      entries that agrees with A at row 0 of the array of the reads, below K3. General in tl and A:
      no host's form is named.
  `k4_host_planes_tie_cells`, `k4_host_planes_tie_pub_cells`: the layers' instance: the planes'
      three clauses from the tie, with the premise on the lookup's cells (h4) AT `cellA tl A`.
  `cellN_eq_cellA`: at LawLay.lean's letters the cells of Johnson/Meaning/ReadsCells.lean (`cellN`)
      are `cellA` at the public record tl0 and at the cells that entE reads off the messages.

ALL PREMISES of `readsAll_of_tie_cells`: h (the tie) · hpos (every place that a table
names lies below K3) · hNM (each table on the third vector of reads names a matrix of the
record). WHO CAN PAY: h: `k08_row`
(Johnson/Desc/First/K8/LawRow.lean) has `TieAt` in front of the block, from what stands
behind it, but for its error · hpos, hNM at the layers: `k4_places_below`, `k4_mats_below`
(as in Johnson/Meaning/PlanesTieK8.lean); at the other hosts: their files' to show.
OBJECT · USER · LETTERS. Object: the formula `TieOf tl A`; the library's `cellsOf`, `cellValS`,
Fo.ReadsAll; in the instance the layers' plain hearing and its `planesParts`. No seated description
is named. User: the hosts' storeys over the tie (K4 here; K5's and K6's files). Letters: tl, A,
K3, entry, ν, W: free, under "for all"; in `cellN_eq_cellA` LawLay.lean's J, Y, cs, l, entE, entW.


Compiled with the whole library.
Limits. `cellsOf` is found by choice: no program is given. AT A COLUMN TO WHOSE SYMBOLS NO SMALL
INTEGERS PACK `cellZ` IS 0 (the library's definition, Cb/Pv/Tail/Unique.lean) and says nothing.
`cellZ tl A` hangs on tl's numbers: that two records with the same numbers and layout (`SamePub`)
have the same `cellZ` is not shown here. h4 stays a premise: that the lookup's cells ARE `cellA` is
the lookups' payers' to show. The tie is a premise. No member is shown. No draw, no error. Nothing
on soundness.
-/
import Johnson.Meaning.PlanesTieK8
import Cb.Pv.Tail.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansG)
open OnBytes.K.Kc
open VerifiableInference.Desc.First.K8 (TieOf SamePub)
open Meaning.Planes

/-- The symbols that a table of cells shows at the record's symbol arrays. -/
def symsA (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) : Syms Cb.Gl.E (Tie.Pv.Tail.sizeOf tl).size :=
  fun μ i' c => A (tl.gtTree.getD μ 0) i' c

/-- THE integer at (row r, column c) of matrix μ behind the symbols that A shows: the library's
`cellsOf` inside the record's sizes, 0 outside. -/
noncomputable def cellZ (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (μ r c : ℕ) : ℤ :=
  if h : μ < tl.NM ∧ c < (tl.mats.getD μ {}).k ∧ r < (tl.mats.getD μ {}).m then
    cellsOf (Cb.Pv.Tail.symL Cb.Gl.E (Tie.Pv.Tail.sizeOf tl).size) (symsA tl A) ⟨μ, h.1⟩ ⟨c, h.2.1⟩
      ⟨r, h.2.2⟩
  else 0

/-- Its image in the field. -/
noncomputable def cellA (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (μ r c : ℕ) : Cb.Gl.E :=
  ((cellZ tl A μ r c : ℤ) : Cb.Gl.E)

/-- Inside the sizes `cellA` is the library's reading of the cells off the symbols. -/
theorem cellA_syms (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (μ r c : ℕ) (hμ : μ < tl.NM)
    (hc : c < (tl.mats.getD μ {}).k) (hr : r < (tl.mats.getD μ {}).m) :
    cellA tl A μ r c = cellValS (symsA tl A) ⟨⟨μ, hμ⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩ := by
  unfold cellA cellZ
  rw [dif_pos ⟨hμ, hc, hr⟩]
  rfl

/-- **Small integers with A's packing are `cellZ`**, inside the sizes. -/
theorem cellZ_of_packs {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} {a : ℕ → ℕ → ℕ → ℤ}
    (h1 : ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
      |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ))
    (h2 : ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
      ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
        A (tl.gtTree.getD μ 0) i' c =
          ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
            Cb.Gl.E))
    {μ r c : ℕ} (hμ : μ < tl.NM) (hc : c < (tl.mats.getD μ {}).k)
    (hr : r < (tl.mats.getD μ {}).m) : a μ r c = cellZ tl A μ r c := by
  have e := cellsOf_of_packs (K := Cb.Gl.E) (s := (Tie.Pv.Tail.sizeOf tl).size) Cb.Gl.p
    (sizeOf_uniq tl) (y := symsA tl A) (Mz := fun μ c i => a μ.val i.val c.val)
    (fun μ c i => h1 μ μ.2 c c.2 i i.2) (fun μ c i' => h2 μ μ.2 c c.2 i' i'.2)
  unfold cellZ
  rw [dif_pos ⟨hμ, hc, hr⟩, ← e]

/-- The three clauses of the tie at given integers. -/
def TieWith (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) : Prop :=
  (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
    |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
  (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
    ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
      A (tl.gtTree.getD μ 0) i' c =
        ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
          Cb.Gl.E)) ∧
  (∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
    A (Port.u3Of tl) 0 pos =
      ∑ j ∈ Finset.range Fn.len,
        Reading.gl.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E))

/-- The tie is "there are integers with the three clauses". -/
theorem tieOf_iff (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) : TieOf tl A ↔ ∃ a, TieWith tl A a :=
  Iff.rfl

/-- **The tie at the named integers**: nothing is left under "there is". -/
theorem tie_named {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieOf tl A) :
    TieWith tl A (cellZ tl A) := by
  obtain ⟨a, h1, h2, h3⟩ := h
  refine ⟨fun μ hμ c hc i hi => ?_, fun μ hμ c hc i' hi' => ?_, fun n Fn hn c sg pos hp => ?_⟩
  · rw [← cellZ_of_packs h1 h2 hμ hc hi]
    exact h1 μ hμ c hc i hi
  · have e : (fun i : Fin (tl.mats.getD μ {}).m => cellZ tl A μ i c) =
        fun i : Fin (tl.mats.getD μ {}).m => a μ i c :=
      funext fun i => (cellZ_of_packs h1 h2 hμ hc i.2).symm
    rw [e]
    exact h2 μ hμ c hc i' hi'
  · obtain ⟨g1, g2, g3, _⟩ := OnBytes.Tie.Pv.Tail.tabAt_some tl hp
    rw [h3 n Fn hn c sg pos hp]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hlt : sg * Fn.len + j < (tl.mats.getD Fn.mat {}).m := by
      have b1 : sg * Fn.len + j < (sg + 1) * Fn.len := by
        rw [Nat.succ_mul]
        exact Nat.add_lt_add_left (Finset.mem_range.mp hj) _
      exact Nat.lt_of_lt_of_le b1
        (Nat.le_trans (Nat.mul_le_mul_right _ g3) (Nat.div_mul_le_self _ _))
    rw [cellZ_of_packs h1 h2 g1 g2 hlt]

/-- **The smallness test's tie, spelled as the law of the reads AT THE NAMED CELLS**, at every table
of entries that agrees with A at row 0 of the array of the reads, below K3. -/
theorem readsAll_of_tie_cells {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieOf tl A) (K3 : ℕ)
    (hpos : ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (he : ∀ pos < K3, entry (Port.u3Of tl) 0 pos = A (Port.u3Of tl) 0 pos) :
    ReadsAll Reading.gl tl.mats tl.funs entry (Port.u3Of tl) K3 (cellA tl A) := by
  obtain ⟨a, h1, h2, h3⟩ := readsAll_of_tie h K3 hpos hNM
  refine readsAll_cells_congr Reading.gl (fun f hf ht c hc r hr => ?_) (h3 entry he)
  show ((a f.mat r c : ℤ) : Cb.Gl.E) = ((cellZ tl A f.mat r c : ℤ) : Cb.Gl.E)
  rw [cellZ_of_packs h1 h2 (hNM f hf ht) hc hr]

/-- **The three clauses at the layers' forms, from the smallness test's tie, at the named cells.**
-/
theorem k4_host_planes_tie_cells {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (htie : TieOf tl A)
    (hfun : tl.funs = o.funs) (hix : tl.ix.U.getD 2 none = hp.tl.ix.U.getD 2 none)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E)
    (hW : ∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = A o.v.iU3 0 pos)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellA tl A (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
        (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  have eU : Port.u3Of tl = o.v.iU3 := by
    unfold Port.u3Of
    rw [hix, (hear_iU3 hh).1]
    rfl
  have h3 := readsAll_of_tie_cells htie o.v.K3 (k4_places_below hh tl hfun hmat hK) hNM W.entry
    (by rw [eU]; exact hW)
  rw [eU, hfun] at h3
  exact k4_host_planes_at Reading.gl hh hq hT hg _ _ rfl rfl (cellA tl A) ν h4 W
    (readsAll_sizes Reading.gl hmat h3)

/-- **The same at a record with the public record's numbers and layout**: the plan's record, closed
with the public shapes; hp is a member of the list of plans of the record that holds no token. -/
theorem k4_host_planes_tie_pub_cells {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {G : Array HPlan2} (hG : plansG P0 = .ok G)
    (hgp : G[g]? = some hp)
    {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (htie : TieOf tl A)
    (hpub : SamePub tl (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)))
    (hfun : tl.funs = o.funs) (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E)
    (hW : ∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = A o.v.iU3 0 pos)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellA tl A (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
        (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨⟨O, hO⟩, hg⟩ := plan_of_plansG hG hgp
  obtain ⟨s1, s2⟩ := Road.planG_sizes hO
  have hn : tl.NM = hp.tl.NM := hpub.nm
  have hi : tl.ix = hp.tl.ix := hpub.ix
  have hsz : hp.tl.mats.size = (P0.tails.getD g {}).mats.size := by
    have := congrArg Array.size s1
    simpa using this
  refine k4_host_planes_tie_cells hh hq hT hg htie hfun (by rw [hi])
    (fun μ => ⟨(hpub.m μ).trans (sizes_of_map s1 μ).1, (hpub.k μ).trans (sizes_of_map s1 μ).2⟩) hK
    (fun f hf _ => ?_) ν W hW h4
  rw [hn, s2, hsz]
  rw [hfun] at hf
  exact k4_mats_below hh hT hg f hf

section AtTheLetters
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.Sound OnBytes.Maker Johnson.Pack

/-- **The two names meet**: at the letters of LawLay.lean the cells behind the symbols (`cellN`) are
`cellA` at the public record and at the cells that entE reads off the messages. -/
theorem cellN_eq_cellA {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) {Cells Tok : Type}
    (entE : (sigOf cs l).Msg → J → Cb.Gl.E) (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)
    (msg : (sigOf cs l).Msg) (μ r c : ℕ) :
    cellN tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (K8.symL Y tl0 entE)
        (u3L Y tl0 entE) (digL Y tl0 entW)) msg μ r c =
      cellA tl0 (fun a r c => Y.cellAt (entE msg) a r c) μ r c := by
  by_cases h : μ < tl0.NM ∧ c < (tl0.mats.getD μ {}).k ∧ r < (tl0.mats.getD μ {}).m
  · exact (cellN_syms tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (K8.symL Y tl0 entE)
      (u3L Y tl0 entE) (digL Y tl0 entW)) msg μ r c h.1 h.2.1 h.2.2).trans
      (cellA_syms tl0 (fun a r c => Y.cellAt (entE msg) a r c) μ r c h.1 h.2.1 h.2.2).symm
  · unfold cellN cellA cellZ
    rw [dif_neg h, dif_neg h]
    simp

end AtTheLetters

#print axioms cellA_syms
#print axioms cellZ_of_packs
#print axioms tieOf_iff
#print axioms tie_named
#print axioms readsAll_of_tie_cells
#print axioms k4_host_planes_tie_cells
#print axioms k4_host_planes_tie_pub_cells
#print axioms cellN_eq_cellA

end Meaning.Reads
