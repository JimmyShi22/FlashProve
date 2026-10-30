-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadAlone.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the hidden values that are sent by themselves
(Johnson/Desc/K5/Honest/Alone.lean), READ IN A FIELD, AT THE PROVER's OWN POINTS: each is the sum,
over a unit's pieces, of the piece's weight times one of the library's reads of the cells (`rd2`,
`rd3`: Inst/Model/Att/Sums.lean; `ext`: Blocks/Ext.lean). Statements with their proofs.

rho is any reading (OnBytes/Model/HideLaws.lean). The right sides have the form in which the tree
reads the verifier's own readers of tables: a claim "slot less the pieces' weighted sum of a reader"
is worth the slot less the sum over the list of pieces of weight times reader (`lessF_value`,
Johnson/Desc/First/Att/Claims/Worth.lean), and a reader is worth `rd2` or `rd3` at the reader's head
point, the table's token weights and the cells (Claims/MeanRd.lean, Claims/KeysLin.lean).

Main names:
  `overPieces_list`, `sum_toList`   a sum over a unit's pieces, as a sum over the list of pieces
  `rd3_rd2`          a read with channels is a read of the contraction over the channels
  `read_planeOf`     R and PV: a plane at a unit's inner point
  `read_rows`, `read_chans`
                     the common form of the values of (pair, head, token), and with a channel
  `read_maxAt`       MV
  `read_zcAt`, `read_ibAt`, `read_rhAt`, `read_rhpAt`, `read_rh2At`, `read_rhp2At`
                     ZC, IB_k, RH, RHP, RH2, RHP2

Every statement but the first four is CONDITIONAL on the lengths of the points that it names, which
the verifier's function of the points tests; MV and IB_k also on the shape's numbers (`Sized`,
public).
Limits. Nothing ties a point to the lookup's here: that is Law/RuleValues.lean. ACC is not here: it
is no sum of one read. RH2 and RHP2 are read at the points of their own list; the verifier's table
under them has the weights of another list's points, which its function for the tables tests to be
the same.
Nothing is said of the verifier's claims.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Alone
import Johnson.Desc.K5.Honest.Law.TilesKit
import Johnson.Desc.K5.Honest.Law.TermsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 RemP ScoreP DivP eqTab tok)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Sums over pieces -/

/-- **The sum over a unit's pieces.** -/
theorem overPieces_list (pw : Array W1) (f : W1 → E) :
    ρ.val (overPieces pw f) = (pw.toList.map fun p => ρ.val p.wp * ρ.val (f p)).sum := by
  unfold overPieces
  rw [← Array.foldl_toList, read_foldl_add ρ (fun p : W1 => mulE p.wp (f p)), ρ.zero, zero_add]
  exact congrArg List.sum (List.map_congr_left fun p _ => ρ.mul _ _)

/-- A sum over the list of pieces, by the pieces' numbers. -/
theorem sum_toList (pw : Array W1) (G : W1 → K) :
    (pw.toList.map G).sum = ∑ b ∈ range pw.size, G (pw.getD b ⟨0, 0, zeroE⟩) := by
  rw [Lists.sum_map_range ⟨0, 0, zeroE⟩ G pw.toList, Array.length_toList]
  refine sum_congr rfl fun b _ => ?_
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- A read with channels is a read of the contraction over the channels. -/
theorem rd3_rd2 (D : Dim) (vg Ψ vn : ℕ → K) (a : ℕ → ℕ → ℕ → K) :
    rd3 D vg Ψ vn a = rd2 D vg Ψ fun g i => conN D vn (a g i) := by
  unfold rd3 rd2 conN
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-! ## Planes -/

/-- **R and PV: cell x of a pair of positions at a unit's inner point**: the multilinear extension
of the plane's cells over the region's entries, at that point, under the pieces' weights. -/
theorem read_planeOf (g : Geo) (w : K5In) (u : RemP) (x : ℕ) :
    ρ.val (planeOf g w u x) = (u.pw.toList.map fun p => ρ.val p.wp *
      Blocks.ext u.z.size (fun n => tOf ρ w (.c (regOf u.isD) x (pairNo g p) n))
        (pt ρ u.z)).sum := by
  unfold planeOf
  dsimp only
  rw [overPieces_list]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [read_under_eq ρ rfl fun _ _ => rfl]
  rfl

/-! ## Values of (pair, head, token) -/

/-- **The common form of the values of (pair, head, token).** zg: the head point, which agrees with
vg. tk: any weights on the tokens, which read as Psi. a: the summed values, read. -/
theorem read_rows {P : Pub5} {pw : Array W1} {zg tk : Array E} {vg Ψ : ℕ → K}
    {f : ℕ → ℕ → ℕ → E} {a : ℕ → ℕ → ℕ → K} (hg : zg.size = P.D.lg)
    (hvg : ∀ j < P.D.lg, pt ρ zg j = vg j) (ht : tk.size = P.D.T)
    (hΨ : ∀ i < P.D.T, ρ.val (tk.getD i zeroE) = Ψ i)
    (hf : ∀ b g i, ρ.val (f b g i) = a b g i) :
    ρ.val (overPieces pw fun p => under (eqTab zg) fun hk => under tk fun i =>
        f (pairNo P.g p) hk i) =
      (pw.toList.map fun p => ρ.val p.wp * rd2 P.D vg Ψ (a (pairNo P.g p))).sum := by
  rw [overPieces_list]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [read_under_eq ρ hg hvg]
  unfold rd2
  refine congrArg _ (sum_congr rfl fun g _ => ?_)
  rw [read_under, ht, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [hΨ i (mem_range.mp hi), hf]
  ring

/-- **The same with a channel.** zc: the channel point, which agrees with vn. -/
theorem read_chans {P : Pub5} {pw : Array W1} {zg tk zc : Array E}
    {vg Ψ vn : ℕ → K} {f : ℕ → ℕ → ℕ → ℕ → E} {a : ℕ → ℕ → ℕ → ℕ → K} (hg : zg.size = P.D.lg)
    (hvg : ∀ j < P.D.lg, pt ρ zg j = vg j) (ht : tk.size = P.D.T)
    (hΨ : ∀ i < P.D.T, ρ.val (tk.getD i zeroE) = Ψ i) (hc : zc.size = P.D.ln)
    (hvn : ∀ j < P.D.ln, pt ρ zc j = vn j) (hf : ∀ b g i n, ρ.val (f b g i n) = a b g i n) :
    ρ.val (overPieces pw fun p => under (eqTab zg) fun hk => under tk fun i =>
        under (eqTab zc) fun ch => f (pairNo P.g p) hk i ch) =
      (pw.toList.map fun p => ρ.val p.wp * rd3 P.D vg Ψ vn (a (pairNo P.g p))).sum := by
  rw [read_rows ρ (P := P) (pw := pw) (f := fun b g i => under (eqTab zc) fun ch => f b g i ch)
    (a := fun b g i => conN P.D vn (a b g i)) hg hvg ht hΨ fun b g i => by
      rw [read_under_eq ρ hc hvn]
      exact sum_congr rfl fun n _ => by rw [hf]]
  exact congrArg List.sum (List.map_congr_left fun p _ => by rw [rd3_rd2])

/-- A table of equality weights of a token point has a weight for each token. -/
theorem size_eqTab_tok {P : Pub5} {zi : Array E} (hi : zi.size = P.D.lT) :
    (eqTab zi).size = P.D.T := by
  rw [size_eqTab, hi, Dim.T_eq]

variable {P : Pub5} (w : K5In)

/-- **MV: the row's maximum at a softmax-table unit's inner point.** The tokens' weights are the
verifier's: the tile rows' weights times the equality weights of the place in the tile. -/
theorem read_maxAt (H : Sized P) {k : ScoreP} (hg : k.zg.size = P.D.lg) :
    ρ.val (maxAt P.g w k) = (k.pw.toList.map fun p => ρ.val p.wp *
      rd2 P.D (pt ρ k.zg) (fun i => ρ.val ((tok P.g k.wI k.zi).getD i zeroE))
        (mxV (tOf ρ w) (pairNo P.g p))).sum :=
  read_rows ρ (f := w.mx) hg (fun _ _ => rfl)
    ((OnBytes.Road.Rows.tok_size P.S k.wI k.zi).trans H.T) (fun _ _ => rfl) (read_mx ρ w)

/-- **ZC: the denominator.** -/
theorem read_zcAt {d : DivP} (hg : d.zgW.size = P.D.lg) (hi : d.ziW.size = P.D.lT) :
    ρ.val (zcAt P.g w d) = (d.pwW.toList.map fun p => ρ.val p.wp *
      rd2 P.D (pt ρ d.zgW) (fun i => ρ.val ((eqTab d.ziW).getD i zeroE))
        (denV (tOf ρ w) (pairNo P.g p))).sum :=
  read_rows ρ (f := w.zd) hg (fun _ _ => rfl) (size_eqTab_tok hi) (fun _ _ => rfl) (read_zd ρ w)

/-- Bit number k in the list of the index's bits. -/
theorem ibAt_getD (g : Geo) (d : DivP) {k : ℕ} (hk : k < g.lt) :
    (ibAt g w d).getD k zeroE = atRow g d.pwX d.zgX d.ziX (w.ibit k) := by
  unfold ibAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- **IB_k: a bit of the index at which the maximum is attained.** -/
theorem read_ibAt (H : Sized P) {d : DivP} (hg : d.zgX.size = P.D.lg) (hi : d.ziX.size = P.D.lT)
    {k : ℕ} (hk : k < P.D.lT) :
    ρ.val ((ibAt P.g w d).getD k zeroE) = (d.pwX.toList.map fun p => ρ.val p.wp *
      rd2 P.D (pt ρ d.zgX) (fun i => ρ.val ((eqTab d.ziX).getD i zeroE))
        (Inst.Model.AttSeg.ibV (tOf ρ w) k (pairNo P.g p))).sum := by
  rw [ibAt_getD w P.g d (by rw [H.lt]; exact hk)]
  exact read_rows ρ (f := w.ibit k) hg (fun _ _ => rfl) (size_eqTab_tok hi) (fun _ _ => rfl)
    (read_ibit ρ w k)

/-- **RH: the cell of the first remainder's high part.** -/
theorem read_rhAt {d : DivP} (hg : d.zgW.size = P.D.lg) (hi : d.ziW.size = P.D.lT)
    (hc : d.zcW.size = P.D.ln) :
    ρ.val (rhAt P.g w d) = (d.pwW.toList.map fun p => ρ.val p.wp *
      rd3 P.D (pt ρ d.zgW) (fun i => ρ.val ((eqTab d.ziW).getD i zeroE)) (pt ρ d.zcW)
        (fun g i n => tOf ρ w (.qh (pairNo P.g p) g i n))).sum :=
  read_chans ρ (f := w.rh) (a := fun b g i n => tOf ρ w (.qh b g i n)) hg (fun _ _ => rfl)
    (size_eqTab_tok hi) (fun _ _ => rfl) hc (fun _ _ => rfl) fun _ _ _ _ => rfl

/-- **RHP: the cell of the second remainder's high part.** -/
theorem read_rhpAt {d : DivP} (hg : d.zgW.size = P.D.lg) (hi : d.ziW.size = P.D.lT)
    (hc : d.zcW.size = P.D.ln) :
    ρ.val (rhpAt P.g w d) = (d.pwW.toList.map fun p => ρ.val p.wp *
      rd3 P.D (pt ρ d.zgW) (fun i => ρ.val ((eqTab d.ziW).getD i zeroE)) (pt ρ d.zcW)
        (fun g i n => tOf ρ w (.qh' (pairNo P.g p) g i n))).sum :=
  read_chans ρ (f := w.rhp) (a := fun b g i n => tOf ρ w (.qh' b g i n)) hg (fun _ _ => rfl)
    (size_eqTab_tok hi) (fun _ _ => rfl) hc (fun _ _ => rfl) fun _ _ _ _ => rfl

/-- **RH2: the same cells as RH, at the points and pieces of the list of the high parts.** -/
theorem read_rh2At {d : DivP} (hg : d.zgH.size = P.D.lg) (hi : d.ziH.size = P.D.lT)
    (hc : d.zcH.size = P.D.ln) :
    ρ.val (rh2At P.g w d) = (d.pwH.toList.map fun p => ρ.val p.wp *
      rd3 P.D (pt ρ d.zgH) (fun i => ρ.val ((eqTab d.ziH).getD i zeroE)) (pt ρ d.zcH)
        (fun g i n => tOf ρ w (.qh (pairNo P.g p) g i n))).sum :=
  read_chans ρ (f := w.rh) (a := fun b g i n => tOf ρ w (.qh b g i n)) hg (fun _ _ => rfl)
    (size_eqTab_tok hi) (fun _ _ => rfl) hc (fun _ _ => rfl) fun _ _ _ _ => rfl

/-- **RHP2: the same cells as RHP, at these.** -/
theorem read_rhp2At {d : DivP} (hg : d.zgH.size = P.D.lg) (hi : d.ziH.size = P.D.lT)
    (hc : d.zcH.size = P.D.ln) :
    ρ.val (rhp2At P.g w d) = (d.pwH.toList.map fun p => ρ.val p.wp *
      rd3 P.D (pt ρ d.zgH) (fun i => ρ.val ((eqTab d.ziH).getD i zeroE)) (pt ρ d.zcH)
        (fun g i n => tOf ρ w (.qh' (pairNo P.g p) g i n))).sum :=
  read_chans ρ (f := w.rhp) (a := fun b g i n => tOf ρ w (.qh' b g i n)) hg (fun _ _ => rfl)
    (size_eqTab_tok hi) (fun _ _ => rfl) hc (fun _ _ => rfl) fun _ _ _ _ => rfl

end H2K5.Honest

#print axioms H2K5.Honest.overPieces_list
#print axioms H2K5.Honest.sum_toList
#print axioms H2K5.Honest.rd3_rd2
#print axioms H2K5.Honest.read_planeOf
#print axioms H2K5.Honest.read_rows
#print axioms H2K5.Honest.read_chans
#print axioms H2K5.Honest.size_eqTab_tok
#print axioms H2K5.Honest.read_maxAt
#print axioms H2K5.Honest.read_zcAt
#print axioms H2K5.Honest.ibAt_getD
#print axioms H2K5.Honest.read_ibAt
#print axioms H2K5.Honest.read_rhAt
#print axioms H2K5.Honest.read_rhpAt
#print axioms H2K5.Honest.read_rh2At
#print axioms H2K5.Honest.read_rhp2At
