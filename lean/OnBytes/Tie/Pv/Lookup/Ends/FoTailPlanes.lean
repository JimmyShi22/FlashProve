-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean: the smallness test's three claims on the planes of its
lookup's counts, from runs of two byte-level routines on one record, under three tests on public
data (CoefOK, PortOK, FoNums.ok), a hypothesis on the lookup's record (HeardIs) and two hypotheses
on the world (RowsLaw, CellsBZ).

 - CoefOK tl Fc: what coef_bz and coef_piece (OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean) ask of the
   test's record tl and of the arrays of the state Fc in which HTailF2.coefficientsF is run: Fc has
   BZ's virtual rows 0, 1, 2; BZ has 32 rows; BZ is no matrix's array; the pieces' virtual rows
   differ from each other, are rows that Fc has, and are none of ZZ's two rows under powers, of BZ's
   rows, of the matrices' rows. All of it is public data: numbers of arrays, of rows and of virtual
   rows.
 - coefTest: the same as a Bool. coefOK_of_test.
 - port_five: at the record of a smallness test that passes PortOK and FoNums.ok: 5 ≤ kT + cK.
 - tail_planes: let HTailF2.linBits9 return from (F, c), and HTailF2.coefficientsF return from (Fc,
   cc), leaving Gc, both run on the one record tl. Then linBits9's run is pscRow on the leaves'
   sumcheck and three calls of t2Lin, and in every state H later than the one behind pscRow, in
   every world over H that meets RowsLaw at Gc and whose cells are BZ's entries, the three claims
   (form and run) are worth claimLeaves, claimBits and countK at the columns' sums of the lookup's
   own cells.
   Premises beside the two runs: tl.heard = some g; tl.f9 = g.shape; CoefOK tl Fc; PortOK tl
   (OnBytes/Tie/Pv/Lookup/Digits/PortSeam.lean); FoNums.ok g.shape; HeardIs ρ g F0 (endsOf g.shape 5
   jLK rsK): the record g, with the state F0, holds the flat function's end values at the rounds rsK
   (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean); Later F0 F; Sized F; ν reads 0 at the place that is no
   cell. No premise ties Fc to F or H.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed here that coefTest follows from the success of the routines that make the record
and the arrays (HTailF2.shapeF, piecesF, addTreesF), or that RowsLaw holds of committed arrays.
Nor does tail_planes, as it stands, reach a run of the whole smallness test. There HTailF2.objectsF
runs linBits9 and then sets the weights vt, vp and rowX (weightsF), and coefficientsF is run on the
record that objectsF returns (so in OnBytes/Model/Layer.lean): a later record than the one on which
linBits9 was run, and coefAll reads these weights. No statement here carries a run of linBits9, or
RowsLaw at Gc, from one record to the other.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBitsLaw

set_option autoImplicit false

namespace Fo
open TwV Finset FoNums Cb.Fo Cb.Fo.Pin OnBytes OnBytes.Model OnBytes.DgP OnBytes.PscRun

instance (F : Fork) (t e : ℕ) : Decidable (HasRow F t e) := by
  unfold HasRow
  infer_instance

/-- What the declared weights' theorems ask of the record and of the state's arrays. -/
structure CoefOK (tl : HTailF2) (Fc : Fork) : Prop where
  bz : HasRow Fc tl.ix.BZ 0 ∧ HasRow Fc tl.ix.BZ 1 ∧ HasRow Fc tl.ix.BZ 2
  bzR : (Fc.trees.getD tl.ix.BZ {}).R = 32
  mats : ∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ
  apart : ((allPieces tl).map fun a => (a.2.tree, a.2.row)).Nodup
  piece : ∀ a ∈ allPieces tl, HasRow Fc a.2.tree a.2.row ∧
    ¬ (tl.ix.ZZ = a.2.tree ∧ tl.zzRowReads = a.2.row) ∧
    ¬ (tl.ix.ZZ = a.2.tree ∧ tl.zzRowTies = a.2.row) ∧ tl.ix.BZ ≠ a.2.tree ∧
    ∀ mu < tl.NM, ¬ (tl.gtTree.getD mu 0 = a.2.tree ∧ 0 = a.2.row)

/-- The same as a Bool. -/
def coefTest (tl : HTailF2) (Fc : Fork) : Bool :=
  decide (HasRow Fc tl.ix.BZ 0 ∧ HasRow Fc tl.ix.BZ 1 ∧ HasRow Fc tl.ix.BZ 2) &&
  decide ((Fc.trees.getD tl.ix.BZ {}).R = 32) &&
  decide (∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ) &&
  decide ((allPieces tl).map fun a => (a.2.tree, a.2.row)).Nodup &&
  decide (∀ a ∈ allPieces tl, HasRow Fc a.2.tree a.2.row ∧
    ¬ (tl.ix.ZZ = a.2.tree ∧ tl.zzRowReads = a.2.row) ∧
    ¬ (tl.ix.ZZ = a.2.tree ∧ tl.zzRowTies = a.2.row) ∧ tl.ix.BZ ≠ a.2.tree ∧
    ∀ mu < tl.NM, ¬ (tl.gtTree.getD mu 0 = a.2.tree ∧ 0 = a.2.row))

theorem coefOK_of_test {tl : HTailF2} {Fc : Fork} (h : coefTest tl Fc = true) : CoefOK tl Fc := by
  simp only [coefTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The declared weights of a piece's row, under the test. -/
theorem CoefOK.pieceW {tl : HTailF2} {Fc : Fork} (T : CoefOK tl Fc) (g : Forest.Heard)
    (a : ℕ × Piece) (ha : a ∈ allPieces tl) :
    (rowAt (coefAll tl g Fc) a.2.tree a.2.row).coef =
      Fo.pieceW (tl.zOf a.1) (g.zk.getD a.1 #[]) a.2 (Fc.trees.getD a.2.tree {}).R :=
  coef_piece tl g Fc a ha T.apart (T.piece a ha).1 (T.piece a ha).2.1 (T.piece a ha).2.2.1
    (T.piece a ha).2.2.2.1 (T.piece a ha).2.2.2.2

theorem port_five {tl : HTailF2} (hP : PortOK tl) (hok : FoNums.ok tl.f9 = true) :
    5 ≤ tl.f9.kT + tl.f9.cK := by
  obtain ⟨⟨_, a2, _⟩, _, c, _⟩ := ok_parts hok
  have h1 : FoNums.kOf tl.f9 0 ≤ tl.f9.kT := (c 0 a2).2.1
  have h2 : FoNums.kOf tl.f9 0 = t2D0 := hP.wide.1
  have h3 : t2D0 = 10 := rfl
  omega

/-- The three claims on the planes, from the routines' runs. -/
theorem tail_planes {K : Type} [CommRing K] (ρ : Reading K) (tl tl' : HTailF2) (g : Forest.Heard)
    (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (F G : Fork) (c c' : Ctx)
    (hrun : tl.linBits9 F c = .ok ((tl', G), c')) (Fc Gc : Fork) (cc cc' : Ctx)
    (hco : tl.coefficientsF Fc cc = .ok (((), Gc), cc')) (T : CoefOK tl Fc) (hP : PortOK tl)
    (hok : FoNums.ok g.shape = true) (jLK : ℕ) (rsK : Rounds K) (F0 : Fork)
    (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 F) (hF : Sized F) :
    ∃ (row : Aff) (p' : Psc) (F1 F2 F3 F4 : Fork) (c1 c2 c3 c4 : Ctx),
      pscRow g.leaves oneE {} F c = .ok (((row, p'), F1), c1) ∧
      t2Lin row #[bzRun tl 0 (mulE g.leaves.eps g.leavesA)
        (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] F1 c1 = .ok (((), F2), c2) ∧
      t2Lin (Aff.slot g.sBit) #[bzRun tl 1 (subE zeroE oneE)
        (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] F2 c2 = .ok (((), F3), c3) ∧
      t2Lin (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))))
        #[bzRun tl 2 oneE (pinW tl)] F3 c3 = .ok (((), F4), c4) ∧
      ∀ H, Later F1 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K) (cellAt : ℕ → ℕ → ℕ → K),
        ν .zero = 0 → RowsLaw ρ Gc (H.worldOf ρ (fun j => ν (.mask j)) entry) cellAt →
        CellsBZ g.shape ν (cellAt tl.ix.BZ) →
        [row.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
              (bzRun tl 0 (mulE g.leaves.eps g.leavesA)
                (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
          (Aff.slot g.sBit).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
              (bzRun tl 1 (subE zeroE oneE) (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
          (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding)))).value ρ
              (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (bzRun tl 2 oneE (pinW tl))] =
        [claimLeaves g.shape 5 jLK rsK ν (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0 ν),
          claimBits g.shape 5 jLK rsK ν (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1 ν),
          countK g.shape 5 (pinColK 5 ν)] := by
  obtain ⟨g1, row, p', F1, F2, F3, F4, c1, c2, c3, c4, e1, r1, r2, r3, r4, _, _⟩ :=
    linBits9_cut tl tl' F G c c' hrun
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e1)
  obtain ⟨g2, e2, rfl, _⟩ := coefficientsF_ok tl Fc Gc cc cc' hco
  obtain rfl : g = g2 := Option.some.inj (hg.symm.trans e2)
  refine ⟨row, p', F1, F2, F3, F4, c1, c2, c3, c4, r1, r2, r3, r4,
    fun H hH ν entry cellAt hz hL hB => ?_⟩
  have hfull : 2 ^ g.shape.cK = g.shape.NC := hs ▸ hP.full
  have h5 : 5 ≤ g.shape.kT + g.shape.cK := hs ▸ port_five hP (hs ▸ hok)
  exact bits9_law ρ tl g jLK rsK F0 F F1 c c1 row p' hs r1 hI h0 hok hF hfull h5 H hH ν entry hz Fc
    T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR cellAt hL hB

end Fo
