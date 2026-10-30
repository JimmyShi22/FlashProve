-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5LayerSeamTrue.lean

The split at the layers loses no true request. The seam before the lookup of a group of layers
(linkOK_of_forInG, Johnson/Road/Lane5ForInG.lean) has two premises with content: L5.LayerR0 (the
group's meaning without its lookup clause) and ForInG (every call's keys, at the key vectors kvG of
this library, lie in its table). Here: for every index i (a model's weights) and every request x
that is true under the policy pol at a lawful table of scales (Policy.IsTrueUnder), at every group g
below 12, the matrices that are read off the library's honest trace of (i, x), with the weights'
matrix i.mat, meet both.

The matrices are named: mzA y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i
x))) g, at s := scalesOf h sc nf: the honest trace with the cost ledger (Cm.trace), as one family of
matrices named by labels (Hd.zOf), of which group g's list takes the matrix with the label of each
of its numbers (mzA, Johnson/Road/FormsKeysDictA.lean).

Main theorems:
* "layerOrd_of_true": these matrices meet LayerOrd at every group. The proof is the first of the
  five parts of ordsL_met (Johnson/Road/Lane5TopLMet.lean), which is stated for one request (all
  weights and all tokens 0) and proved in a way that holds for every true one.
* **"layerSeam_of_true"**: so they meet L5.LayerR0 and ForInG, by layerOrd_iff_forIn
  (Johnson/Road/Lane5KeysIffG.lean).
Under the public premises of layerKeys_of_forIn and, for the way from the trace: Sized2; twelve
groups; a head's shape hH with the nine numbers FullH (the labels' rule Hd.D5 reads its number of
parts of hf); the table of scales is lawful; the policy is within its bounds.
That these premises hold together is shown by no theorem. Those that a program can decide are one
test with its theorem (recordOneB, Johnson/Road/Ends/AlgBridgeOne.lean); a run finds it true in all
twelve groups at what publicOf returns on the parameter text linesKF and the scale words scalesKF of
Johnson/Road/FormsKeysRunK.lean (Johnson/Road/Ends/GuardRec.lean). Sized2, FullH and "lawful" follow
there from three hypotheses on the files (Johnson/Road/Lane5TopPub.lean). At that record:
layerSeam_of_true_file (Johnson/Road/Lane5LayerSeamTrueAt.lean). The premise hn, that the eight
lines of calls name the library's families in order, is no test of the verifier: a configuration
that it admits may have other lines, and then nothing is said.

Limits. Which true requests there are is not said here. The library exhibits some: at every lawful
table and all weights 0, every request that has its form, with y = 0 if e = 1,024, whatever its
other tokens, under a policy with 257 ≤ θ and 257 ≤ C (Policy/Rel/TrueGuards.lean: zero_all); at the
reference table alone, requests with 1,023 counted positions at made-up weights whose 48 layers are
all zero (Policy/Rel/PosGuards.lean: real_gap, step_gap). At the first family and at real_gap's
request, at the record that publicOf returns (if the scale file's words are "scalesKF"):
layerSeam_zero_all_file, layerSeam_real_gap_file (Johnson/Road/Lane5LayerSeamTrueAt.lean). The
library's model has no cell for a lookup's counts. So in these matrices the matrix b of a group of
layers is 0, which no honest prover of the protocol would commit to. The statements do not read it.
The numbering is that of these files' dictionary. For the labels of the layers' lists it is the
verifier's by a theorem (labA_tails, Johnson/Road/FormsKeysDictA.lean).

Not claimed: that a prover's committed cells are these matrices; that an honest prover's proof is
accepted (completeness of the protocol); anything on a proof, a verifier's verdict, soundness or
hiding. It is a statement on integers and tables alone.

-/
import Johnson.Road.Lane5KeysIffG
import Johnson.Road.Lane5TopLMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

section

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {sc : Model.Layer.Scales} {nf : NormPar} {pol : AcceptancePolicy}

/-- **The matrices read off the honest trace of a true request are in order at every group.** -/
theorem layerOrd_of_true (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol)
    (i : Cm.Idx) (x : Instance ppref) (ht : Policy.IsTrueUnder (scalesOf hL sc nf) pol i x)
    {g : ℕ} (hg : g < 12) :
    LayerOrd hL sc y g (mzA y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x))) g) i.mat x := by
  have P := (premiseL_of_under hs hpol ht).2
  have hT := honest_smallL hs hpol ht
  have hp := Hd.parts_ref hy S Z2
  have hZ : ∀ l r c, |Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)) l r c| < 2 ^ 18 :=
    fun l r c => lt_trans (Hd.zOf_small hT (by norm_num) l r c) (by norm_num)
  have hD : ∀ k < Cm.Seg.nSeg, k % 2 = 0 → ∀ q ∈ Cm.Seg.reads Cm.Seg.Hd.main k,
      Cm.Seg.at' (Hd.D5 hH y (fun _ _ _ => 0) (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)))) q =
      Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)) q :=
    fun k hk h2 q hq => Hd.D5_zOf Policy.mainOK h12 hF.NHf hp.1 hp.2 _ _ k hk q hq
      ((reads_even_or_own hq).elim id fun e => by rw [e]; exact h2)
  have hk : 2 * g < Cm.Seg.nSeg := by
    show 2 * g < 25
    omega
  exact (layerOrd_iff hy S Zd Z2 hp4 Cm.Seg.Hd.main _ i.mat hg sc nf x).2
    ⟨fun _ _ _ _ => hZ _ _ _,
      linkOK_seg (Policy.segPol_ne _ pol (by omega))
        (linkOK_congr (laws_main _ pol) hk
          (fun q hq => ((dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.main _ _ hg q hq).trans
            (hD (2 * g) hk (by omega) q hq)).symm)
          (P.link (2 * g) hk))⟩

end

section

variable {h : Model.Layer.Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ}
  {rd : Model.Layer.Reads} {mats : Array (ℕ × ℕ)}
  {r : List Model.Layer.TableAt × List (Model.Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
  {hH : Model.Head.Shape} {nf : NormPar} {pol : AcceptancePolicy}

/-- **Every true request's honest matrices meet both premises of the seam before the lookup of a
group of layers.** -/
theorem layerSeam_of_true (hy : Model.Layer.layout h pc = .ok P.y) (S : Switches h)
    (hsc : Model.Layer.scalesHeld h P.sc = .ok ()) (hrd : Model.Layer.readsOf P.y = .ok rd)
    (hl : Model.Layer.layTables mats (Model.Layer.tableAsks P.y rd g) 0 = some r)
    (Zd : Sized h All.DF) (Z2 : Sized2 h All.DF) (hp4 : h.p4 = true) (hev : h.dh % 2 = 0)
    (hmats : ∀ (n : String) (Tn : Model.Layer.Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    (hT : P.y.T = All.DF.T) {s : Model.WsShape} (ZW : SizedW s ppref)
    (hW : Model.wsLayOf s true Layout.kRef = .ok P.wsLay)
    (hgL : ∀ l < All.DF.nl, g * P.y.Lam + l < ppref.layers)
    (hrope : Alg.ropeOK P All.DF tbRef (g * P.y.Lam) = true)
    (h8 : P.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : Model.CallD), P.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (FFSeg.fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (FFSeg.used All.DF cc))
    (hw : ∀ cd ∈ P.y.calls, ∃ wg, (Alg.envG P g r.1).weighedOf cd = some wg)
    (hL : ∀ cc : Fin 8, ∃ c0 : Model.Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (FFSeg.lut tbRef cc) ∧ c0.k = if cc = 3 then 8 else 16)
    (h12 : P.y.NGr = 12) (hF : Hd.FullH hH) (hs : (scalesOf h P.sc nf).Lawful)
    (hpol : Policy.PolCond pol) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf h P.sc nf) pol i x) (hg : g < 12) :
    LayerR0 h P.sc P.y g (mzA P.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf h P.sc nf) pol) i x))) g) i.mat x ∧
      Alg.ForInG P g (mzA P.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf h P.sc nf) pol) i x))) g) i.mat :=
  (Alg.layerOrd_iff_forIn hy S hsc (by rw [h12]; exact hg) hrd hl Zd hp4 hev hmats hT ZW hW hgL
    hrope h8 hn hfl hw hL _ _ x).1
    (layerOrd_of_true hy S Zd Z2 hp4 h12 hF hs hpol i x ht hg)

end

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.layerOrd_of_true
#print axioms OnBytes.Road.L5.layerSeam_of_true
