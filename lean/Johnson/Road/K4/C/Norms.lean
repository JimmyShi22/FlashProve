-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Norms.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the norms' stretch
(Johnson/Desc/K4/Honest/Norms.lean): the reading into the field of each value that the makers make
is the library's term at the cells t: the right sides are those of five fields of the structure
`Opened` (Johnson/Road/K4/W/Ground.lean): sums, prods, ends8, sqL, sqR. Definitions of hypotheses;
statements and proofs.

  `RowFields`     the four fields of each norm's row at each token, as the makers' tables hold them.
  `rowMaps_congr`, `rowFields_congr`   of the sampled values they read the lookup's alone.
  **`sums_read`**   the sums of limb products.
  **`sq_read`**     the two end values of the squares' product layer: the first is the library's
                  term, the second is the first.
  **`prods_read`**  the row products.
  **`ends8_read`**  the four end values for each norm of the row products' token sumcheck.

Not shown here. That the hypotheses hold anywhere: no example is known. THE ROWS' FIELDS
(RowFields) ARE A HYPOTHESIS: the makers value the verifier's forms on the honest reads at each
token's corner; the law on the honest reads (ValAff.lean) brings each value to the form's value at
the true entries, and RowFields.lean states under which further hypotheses that value is the
library's term. THAT THE SAMPLED VALUES IN p AND THE CHALLENGES rs ARE THOSE THAT THE VERIFIER HAS
HEARD: the statements speak at p.PV, at p.gp and at the job's own point of rs. That the makers
return (hJ, hm), and that the point and the challenges have their lengths (hPV, hrs): premises.
Fits is asked at some world W and some points low, u: of it the numbers and the ties of the
library's names to the cells are read, no entry of W. Nothing says that the cells are those of an
inference.
No property is claimed.
-/
import Johnson.Road.K4.C.NormsTabs
import Johnson.Desc.K4.Honest.Law.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten matIx)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest

variable {W : World Cb.Gl.E} {v : Env} {t : Cell → Cb.Gl.E} [scl : Scl] {D : Dim}
  {low u : ℕ → Cb.Gl.E} {Q : K4Pub} {w : K4In} {Mm : Mats Cb.Gl.E} {p : Pts}

/-- **The four fields of each norm's row at each token**, as the makers' tables hold them, read into
the field, are the library's. This defines a hypothesis; the definition claims nothing. -/
def RowFields (Q : K4Pub) (w : K4In) (p : Pts) (D : Dim) (t : Cell → Cb.Gl.E) : Prop :=
  ∀ ms, rowMaps Q w p = some ms → ∀ ν, ν < D.nNu → ∀ i, i < 2 ^ D.lT →
    Reading.gl.val ((ms.getD (4 * ν + 0) #[]).getD i zeroE) = Inst.Model.Ledger.sa (led t ν i) ∧
    Reading.gl.val ((ms.getD (4 * ν + 1) #[]).getD i zeroE) = Inst.Model.Ledger.sb (led t ν i) ∧
    Reading.gl.val ((ms.getD (4 * ν + 2) #[]).getD i zeroE) = Inst.Model.Ledger.Rlo (led t ν i) ∧
    Reading.gl.val ((ms.getD (4 * ν + 3) #[]).getD i zeroE) = Inst.Model.Ledger.Rhi (led t ν i)

omit scl in
/-- The rows' tables read, of the sampled values, what the lookup has sampled alone. -/
theorem rowMaps_congr (Q : K4Pub) (w : K4In) {p p' : Pts} (hfo : p.fo = p'.fo) :
    rowMaps Q w p = rowMaps Q w p' := by
  unfold rowMaps OnBytes.Desc.First.K4.Honest.envOf
  rw [hfo]

omit scl in
/-- So RowFields at one list of sampled values serves at every list with the same values of the
lookup's. -/
theorem rowFields_congr {p' : Pts} (hfo : p.fo = p'.fo) (R : RowFields Q w p D t) :
    RowFields Q w p' D t := fun ms hms => R ms (by rw [rowMaps_congr Q w hfo]; exact hms)

/-- **THE SUMS OF LIMB PRODUCTS.** -/
theorem sums_read (F : Fits Reading.gl W v D (cellsAt v.y Mm) t low u) (hy : Q.P.y = v.y)
    (C : CellsAre Q w Mm) (N : NormsPlan Q D) (hPV : p.PV.size = D.lT) :
    ∀ ν, ν < D.nNu → ∀ s, s < 9 →
      Reading.gl.val ((wSums Q w p).getD (9 * ν + s) zeroE) =
        wHat D t ν (pt Reading.gl p.PV) s := by
  intro ν hν s hs
  have hxl : Q.P.y.h.xl = 5 := by rw [hy]; exact F.xl
  have hNS : ledNS Q.P.y.h.xl = 9 := by rw [hxl]; rfl
  have hd : Q.P.y.h.d = D.d := by rw [hy]; exact F.d
  have e := wSums_read Q w p (ν := ν) (s := s) (by rw [N.NI]; exact hν) (by rw [hNS]; exact hs)
  rw [hNS] at e
  rw [e, N.T]
  unfold wHat Blocks.ext
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have hW : Inst.Model.Ledger.Wsum D.d
      (fun l j => Reading.gl.val
        (ofF (streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") ν l j i))) s =
      Inst.Model.Ledger.Wsum D.d (fun l j => bS D t ν l j i) s := by
    unfold Inst.Model.Ledger.Wsum
    refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => sum_congr rfl fun l' hl' => ?_
    beta_reduce
    rw [limb_read F hy C N.mats N.streams N.T N.NI hν (mem_range.mp hl) (mem_range.mp hj) hi',
      limb_read F hy C N.mats N.streams N.T N.NI hν (mem_range.mp hl') (mem_range.mp hj) hi']
  rw [limbSums_read Q w ν i hxl hs, eqTab_value Reading.gl p.PV i (by rw [hPV]; exact hi'),
    hPV, hd, hW]
  exact mul_comm _ _

/-- **THE TWO END VALUES OF THE SQUARES' PRODUCT LAYER.** rs: the challenges of the layer's
variables, in the order sampled. -/
theorem sq_read (F : Fits Reading.gl W v D (cellsAt v.y Mm) t low u) (hy : Q.P.y = v.y)
    (C : CellsAre Q w Mm) (N : NormsPlan Q D) {J : Job}
    (hJ : jobSquares Q w p = some J) (rs : List E) (hrs : rs.length = Q.P.rd.muV) :
    Reading.gl.val ((J.ends rs).getD 0 zeroE) =
        ext (Q.P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + D.lT)
          (Road.K4.sqV v.y.NI (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) v.y.lPd v.y.xb.nl D.lT
            (fun l => Reading.gl.val (p.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
          (pt Reading.gl (J.cube.pointOf rs)) ∧
      (J.ends rs).getD 1 zeroE = (J.ends rs).getD 0 zeroE := by
  have hmu : Q.P.rd.muV = Q.P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + D.lT := by
    rw [← hy]
    exact N.muV
  unfold jobSquares at hJ
  dsimp only at hJ
  split at hJ
  · rename_i hfit
    obtain rfl := Option.some.inj hJ
    refine ⟨?_, rfl⟩
    show Reading.gl.val ((Cube.valuesAt _ rs).getD 0 zeroE) = _
    rw [CubeLaw.valuesAt_mle Reading.gl _ hfit rs hrs 0, CubeLaw.mle_ext, CubeLaw.pointOf_size,
      ← hmu]
    exact Blocks.ext_congr (fun x hx => sqTab_read F hy C N p.gp hx) _
  · cases hJ

omit scl in
/-- **THE ROW PRODUCTS.** -/
theorem prods_read (R : RowFields Q w p D t) (hT : Q.P.y.T = 2 ^ D.lT) (hNI : Q.P.y.NI = D.nNu)
    (hPV : p.PV.size = D.lT) (hm : (rowMaps Q w p).isSome = true) :
    ∀ ν, ν < D.nNu → ∀ j, j < 7 →
      Reading.gl.val ((rowProducts Q w p).getD (7 * ν + j) zeroE) =
        pHat D t ν (pt Reading.gl p.PV) j := by
  intro ν hν j hj
  obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp hm
  rw [rowProducts_sum Q w p hms (by rw [hNI]; exact hν) hj, hT]
  unfold pHat Blocks.ext
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  obtain ⟨r0, r1, r2, r3⟩ := R ms hms ν hν i hi'
  rw [eqTab_value Reading.gl p.PV i (by rw [hPV]; exact hi'), hPV]
  congr 1
  have key := prodsOf_pairs
    (fun k => Reading.gl.val ((ms.getD (4 * ν + k) #[]).getD i zeroE)) hj
  beta_reduce at key
  rw [r0, r1, r2, r3] at key
  exact key.symm

omit scl in
/-- **THE FOUR END VALUES FOR EACH NORM OF THE ROW PRODUCTS' TOKEN SUMCHECK.** rs: the challenges of
the sumcheck's variables, in the order sampled. -/
theorem ends8_read (R : RowFields Q w p D t) (hlt : Q.P.y.h.lt = D.lT) {J : Job}
    (hJ : jobRows Q w p = some J) (rs : List E) (hrs : rs.length = D.lT) :
    ∀ ν, ν < D.nNu →
      Reading.gl.val ((J.ends rs).getD (4 * ν + 0) zeroE) =
        ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i))
          (pt Reading.gl (J.cube.pointOf rs)) ∧
      Reading.gl.val ((J.ends rs).getD (4 * ν + 1) zeroE) =
        ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i))
          (pt Reading.gl (J.cube.pointOf rs)) ∧
      Reading.gl.val ((J.ends rs).getD (4 * ν + 2) zeroE) =
        ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i))
          (pt Reading.gl (J.cube.pointOf rs)) ∧
      Reading.gl.val ((J.ends rs).getD (4 * ν + 3) zeroE) =
        ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i))
          (pt Reading.gl (J.cube.pointOf rs)) := by
  unfold jobRows at hJ
  obtain ⟨ms, hms, hJ⟩ := Option.bind_eq_some_iff.mp hJ
  dsimp only at hJ
  split at hJ
  · rename_i hfit
    obtain rfl := Option.some.inj hJ
    intro ν hν
    have key : ∀ c : Cube, c.fits = true → c.n = Q.P.y.h.lt → c.maps = ms → ∀ k,
        Reading.gl.val ((c.valuesAt rs).toList.getD (4 * ν + k) zeroE) =
          ext D.lT (fun i => Reading.gl.val ((ms.getD (4 * ν + k) #[]).getD i zeroE))
            (pt Reading.gl (c.pointOf rs)) := by
      intro c hc hn hmaps k
      rw [toList_getD, CubeLaw.valuesAt_mle Reading.gl c hc rs (by rw [hn, hlt]; exact hrs),
        CubeLaw.mle_ext, CubeLaw.pointOf_size, hn, hlt, hmaps]
    exact ⟨(key _ hfit rfl rfl 0).trans (Blocks.ext_congr (fun i hi => (R ms hms ν hν i hi).1) _),
      (key _ hfit rfl rfl 1).trans (Blocks.ext_congr (fun i hi => (R ms hms ν hν i hi).2.1) _),
      (key _ hfit rfl rfl 2).trans (Blocks.ext_congr (fun i hi => (R ms hms ν hν i hi).2.2.1) _),
      (key _ hfit rfl rfl 3).trans
        (Blocks.ext_congr (fun i hi => (R ms hms ν hν i hi).2.2.2) _)⟩
  · cases hJ

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rowMaps_congr
#print axioms OnBytes.Road.K4.C.rowFields_congr
#print axioms OnBytes.Road.K4.C.sums_read
#print axioms OnBytes.Road.K4.C.sq_read
#print axioms OnBytes.Road.K4.C.prods_read
#print axioms OnBytes.Road.K4.C.ends8_read
