-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsMaskAtWide.lean: THE FIELD mask THAT THE ASSEMBLY OF K4's LAW LEAVES AT A
LATER GROUP (`K4LaterAt`, Johnson/Road/K4/K04LawOf.lean: the pile's reader's mask entry at the name
that the public parameters give is the value's message at its slot c7), AT THE DATA OFF THE WIDER
MEANING's OWN PARAMETERS. A joining: `woMaskTie` (Johnson/Road/K4/WoMaskTie.lean),
with its ties on public letters and its premise on the value's letter idxAt paid from ONE TEST
(`indexTieB`, Johnson/Road/K4/K4PinsAtWide.lean) at K4's letters posI, v7, nx. No draw, no count.

  `maskRowsAt M i`: the number of mask rows of the shape number i of the list M; 0 if there is none.
  **`mask_wide`**: the field, at posI := `posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)` · v7 :=
    `rowsBefore E.dP.fvs m` · nx := v7, at every place xL and all bounds, from: what four public
    items say at Mg (the shapes, the book, the seats, the codes) · TWO TESTS OF THAT TIE's FILES:
    `openMaskB`, `maskFitsB` · THE TEST `indexTieB` at n := v7 + 1.

OBJECT: `k4DataWide 𝔇 E Mg₀`. USER: Johnson/Road/K4/K4PinsLaterClosed.lean; meant: `laterAt_closed`
(Johnson/Road/K4/K4PinsLaterClosed.lean), its binder mask. LETTERS: 𝔇, E, Mg₀, Mg, z, links, ps, k,
m, p, xL, nM, nRr, nC: free.




Limits. K04_law IS NOT PROVED BY THIS. THE FOUR LINES ON Mg's PUBLIC ITEMS SPEAK OF NAMES THAT HAVE
LEFT THE MEANING THAT COUNTS: they can hold at the wider meaning alone: the field counts only when
the bridge is paid. THE THREE TESTS ARE EVALUATED NOWHERE IN THIS FILE; at the written values Lean's
kernel decides `indexTieB` and `maskFitsB` at the twelve groups (`indexTie_written`,
`maskFits_written`, Johnson/Road/K4/K4PinsWrittenNext.lean), and a test whose yes gives `openMaskB`
at each place of K4's in the written list of links (`k4_openMask_wide`, `openMask_of_fit`,
Johnson/Road/K4/Rec/OpenNextWide.lean); by evaluation, which is no proof, `maskFitsB` and
`openMaskB` have also run at the small set. THAT THE PROGRAMS LAY INDEX MASK j AT THE j-TH FREE
ENTRY IS NOT SHOWN: posI is laid so. NO MEMBER IS SHOWN.
-/
import Johnson.Road.K4.K04LawOf
import Johnson.Road.K4.K4PinsAtWide
import Johnson.Road.K4.WoMaskTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.Look (Place Stored.entries)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (EShapes EBook0 ESeats ECodes openMaskB maskFitsB)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

/-- The number of mask rows of shape number i of the list; 0 if there is none. -/
def maskRowsAt (M : List OracleShape) (i : ℕ) : ℕ := ((M[i]?).map (·.maskRows)).getD 0

variable [scl : Scl] {Fr : Frame} {Xi Tok : Type} {nR : ℕ} {X : Public}

/-- **The field mask at the wider meaning's own parameters.** -/
theorem mask_wide (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nR X)
    (E : WideData ProofFile.InstPub)
    (Mg₀ Mg : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)) (z : ProofFile.InstPub)
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k m : ℕ) (p : Par)
    (hg : p.g < 12) (xL : Place) (nM nRr nC : ℕ)
    (eS : EShapes Mg E.d12.M) (eB : EBook0 Mg) (eSe : ESeats Mg E.d12.L) (eC : ECodes Mg 𝔇.cs)
    (hO : openMaskB Mg.more links ps (k + 1) = true)
    (hF : maskFitsB 𝔇.cs E.d12.M E.d12.L (𝔇.N.msgsAt ps[k + 1]?) (𝔇.N.treesAt ps[k + 1]?)
      𝔇.N.indexNo (rowsBefore E.dP.fvs m) = true)
    (hT : indexTieB 𝔇.cs E.d12.M E.d12.L.places 𝔇.ms 𝔇.N (rowsBefore E.dP.fvs m + 1) = true) :
    ∀ (b : S × Fr.E.Str) w,
      onQ (k4DataWide 𝔇 E Mg₀).N Mg links ps (fun s => (z, s)) (k + 1) b → b.1.failed = none →
      ((k4DataWide 𝔇 E Mg₀).rw13 (z, b.1) w).mask
          ⟨(k4DataWide 𝔇 E Mg₀).N.indexNo,
            Rec.nextNoP (k4DataWide 𝔇 E Mg₀).d12.M ((k4DataWide 𝔇 E Mg₀).N.msgsAt ps[k + 1]?)
              (k4DataWide 𝔇 E Mg₀).N.indexNo (k4DataWide 𝔇 E Mg₀).fvs m⟩ =
        (qkAt (k4DataWide 𝔇 E Mg₀) p m xL (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo))
          Stored.entries nM nRr nC (rowsBefore E.dP.fvs m) (rowsBefore E.dP.fvs m)
          hg).toL.plan.full.msg
          (partOf (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).arr
            (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N m w)
          (qkAt (k4DataWide 𝔇 E Mg₀) p m xL (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo))
            Stored.entries nM nRr nC (rowsBefore E.dP.fvs m) (rowsBefore E.dP.fvs m)
            hg).toL.plan.full.c7 := by
  obtain ⟨sh, u, hM, hq, hu, hsh, hst, hI⟩ := indexTie_of_B hT
  have hmr : maskRowsAt E.d12.M 𝔇.N.indexNo = sh.maskRows := by
    unfold maskRowsAt
    rw [hM]
    rfl
  rw [← hmr] at hI
  obtain ⟨u', hu', hidx⟩ := idx_at_v7 (Tok := Tok)
    (pinAt (k4DataWide 𝔇 E Mg₀) xL (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)) Stored.entries)
    xL.ns 𝔇.N p.hp.tl (VerifiableInference.Desc.First.Look.pubAt X
      (m / VerifiableInference.Desc.First.Look.stepOf X)).y nM nRr nC
    (OnBytes.Model.Forest.elems X.layers.y.fo) p.hp.ns (rowsBefore E.dP.fvs m)
    (rowsBefore E.dP.fvs m) X p hg 𝔇.arr 𝔇.ms m (rowsBefore E.dP.fvs m + 1) 𝔇.cs hI
    (Nat.lt_succ_self _)
  obtain rfl : u' = u := Option.some.inj (hu'.symm.trans hu)
  exact woMaskTie 𝔇.N Mg z links ps (k + 1) m E.d12.M E.d12.L 𝔇.cs E.dP.fvs sh 𝔇.N.index _
    (partOf 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m) u' (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)
      (rowsBefore E.dP.fvs m)) nR 𝔇.P13.lin.kCol 𝔇.arr 𝔇.mat13 eS eB eSe eC hO hF hM hq
    ⟨Nat.le_refl _, hsh, hst, by rw [hmr]; rfl⟩ hidx

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mask_wide
