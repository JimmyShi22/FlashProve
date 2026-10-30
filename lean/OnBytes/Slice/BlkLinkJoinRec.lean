-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkJoinRec.lean: the program's link and the written link, joined, over the
format with a sample map.

OnBytes/Slice/BlkLinkRec.lean shows that the rows of the program's link are the rows rowsXR at a
statement x of the library's verifier, under two bundles of hypotheses (XTieR, LinkRowsR). This file
meets both where the program runs on the view of a written transcript and x is the statement after
the five written rounds at a pair of records r (OnBytes/Slice/CorePeelRec.lean: st4R), as
OnBytes/Slice/BlkLinkJoin.lean does at `st4`. That statement, its two records
forgotten, is that file's (forget_st4R), so that file's theorems serve for all that is not the
records'.

The hypotheses that are left speak of values alone. Those of head_rows (OnBytes/Slice/
BlkLinkJoin.lean) are asked as they stand there. New: each of the program's two keys holds its
record of the pair r (KeyHasR, OnBytes/Slice/BlkRecRow.lean); the records' rows were made by the
program's own calls; a row's message has room for the pads.

Main theorems.
 foldSym₀_lkR, foldSym₁_lkR, forget_st4R, st4R_recs, st4R_gamma   the statement after the five
                rounds, part by part.
 linkRowsR_of   the bundle LinkRowsR, from LinkRows and the calls that made the records' rows.
 head_rowsR     the two joined: targets and coefficients of the program's rows are tgXR and cfXR at
                the statement after the five written rounds.

Not claimed. That a run of the program's link yields these hypotheses. That a key holds a record.
Nothing on the round in which the rows are combined, and nothing on soundness.

-/
import OnBytes.Slice.BlkLinkJoin
import OnBytes.Slice.BlkLinkRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-! ## The statement after the five rounds -/

section
variable (S : Sz) (Z : Sample GE S.En) (r : (S.lkR Z).X0) (d1 d2 d3 d4 d5 : PQ.RD)
  (y : (S.lkR Z).E0.Str) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg) (c2 : (wRound d2).Chal)
  (m3 : (wRound d3).Msg) (c4 : (wRound d4).Chal) (c5 : (wRound d5).Chal)

/-- The fold of a symbol read in the first table does not read the sample map. -/
theorem foldSym₀_lkR (γ : Fin S.P.v → GE) (q : Option S.lk.E2.Sym) :
    (S.lkR Z).foldSym₀ γ q = S.lk.foldSym₀ γ q := by
  rcases q with _ | ((q | q) | q) <;> rfl

/-- The same for a symbol read in the copy. -/
theorem foldSym₁_lkR (γ : Fin S.P.v → GE) (q : Option S.lk.E2.Sym) :
    (S.lkR Z).foldSym₁ γ q = S.lk.foldSym₁ γ q := by
  rcases q with _ | ((q | q) | q) <;> rfl

/-- The statement after the five rounds, its two records forgotten, is the statement `st4` of
`Sz.lk`. -/
theorem forget_st4R :
    S.forget Z (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 =
      (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 := by
  refine Prod.ext (Prod.ext (Prod.ext rfl rfl) (Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_))) rfl
  · exact funext fun i => foldSym₀_lkR S Z _ _
  · exact funext fun i => foldSym₁_lkR S Z _ _

/-- It holds the pair of records. -/
theorem st4R_recs : (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1.1.1.1.1 = r := rfl

/-- It holds the point of the fold as the first round's values give it. -/
theorem st4R_gamma :
    (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1.1.1.1.2 = gVec S.P.v _ (valsOf d1 c1) := rfl

end

/-! ## The two sides joined -/

/-- The bundle LinkRowsR, from the calls that made the records' rows. LinkRows is asked; the two
calls for the records' rows are taken with the arrangement of a folded row rewritten. -/
theorem linkRowsR_of (S : Sz) (Λ : Params.LinkShape) (codes : Codes) (hS : LinkSizes S Λ codes)
    (o0 : ℕ) (k0 k1 : TableKey) (gamma phi z : List E) (beta y0 y1 : E) (d0 d1 : List ℕ)
    (f0 f1 : ℕ → E) (rc0 rc1 : List Row) (rE s0 s1 : Row) (rs0 rs1 : List Row)
    (hold : LinkRows S Λ (Λ.side false 1) (Λ.side true 1) o0 (o0 + 1) phi z beta y0 y1 d0 d1 f0 f1
      rE s0 s1 rs0 rs1)
    (recs0 : (k0.seeds.zipIdx.mapM fun x =>
      foldeqRecordRow (Λ.side false 1) x.1 k0.record x.2 (foldeqWeights gamma)
        ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rc0)
    (recs1 : (k1.seeds.zipIdx.mapM fun x =>
      foldeqRecordRow (Λ.side true 1) x.1 k1.record x.2 (foldeqWeights gamma)
        ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rc1) :
    LinkRowsR S Λ (Λ.side false 1) (Λ.side true 1) o0 (o0 + 1) k0 k1 gamma phi z beta y0 y1 d0 d1
      f0 f1 rc0 rc1 rE s0 s1 rs0 rs1 := by
  rw [hS.lay] at recs0 recs1
  exact ⟨hold, recs0, recs1⟩

/-- **The rows of the program's link, run on the view of a written transcript, are the rows of
rowsXR at the statement after the five written rounds**, at the pair of records r. What is asked:
what head_rows asks (OnBytes/Slice/BlkLinkJoin.lean); the key of the first table holds r's first
record and the key of the copy its second; the records' rows were made by the program's calls; three
pads for each answer have room in a row's message. -/
theorem head_rowsR (S : Sz) (lg s : ℕ) (Λ : Params.LinkShape) (codes : Codes)
    (hS : LinkSizes S Λ codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (d1 d2 d3 d4 d5 dA : PQ.RD)
    (hd : BatDraws S d1 d2 d3 d4 d5 dA) (y : (S.lkR (recZ S.P.T.l lg s)).E0.Str)
    (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
    (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
    (o0 : ℕ) (gamma phi z : List E) (beta y0 y1 : E) (D0 D1 : List ℕ) (rE row0 row1 : Row)
    (rows0 rows1 : List Row) (list0 list1 : Array ℕ) (columns0 columns1 : Array (Array F))
    (hgamma : gamma.map E.triple = (rvOf d1 m1 c1).els)
    (hz : z.map E.triple = (rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP))
    (hbeta : beta.triple = (rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE)
    (hy0 : y0.triple = (rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE)
    (hy1 : y1.triple = (rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE)
    (hl0 : D0.length = S.P.nu0) (hl1 : D1.length = S.P.nuj)
    (hD0 : ∀ i, i < S.P.nu0 → D0.getD i 0 = (rvOf d4 m4 c4).poss.getD i 0)
    (hD1 : ∀ i, i < S.P.nuj → D1.getD i 0 = (rvOf d4 m4 c4).poss.getD (S.P.nu0 + i) 0)
    (hphi : phi.map E.triple = (rvOf d5 m5 c5).els)
    (heq : linkEqualityRow Λ phi ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩
      ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩ Λ.cut = some rE)
    (form0 : Send.form codes (Λ.side false 1).u o0 ⟨z, beta⟩ 0 = some row0)
    (form1 : Send.form codes (Λ.side false 1).u (o0 + 1) ⟨z, beta⟩ 0 = some row1)
    (cols0 : (D0.mapM fun x => do
      let i ← list0.idxOf? x
      foldeqColumnRow (Λ.side false 1) x (foldeqSymbol (foldeqWeights gamma) (← columns0[i]?))
        ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rows0)
    (cols1 : (D1.mapM fun x => do
      let i ← list1.idxOf? x
      foldeqColumnRow (Λ.side true 1) x (foldeqSymbol (foldeqWeights gamma) (← columns1[i]?))
        ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rows1)
    (hcol0 : ∀ (i : ℕ) (col : Array F) (x : S.Pos), list0.idxOf? x.val = some i →
      columns0[i]? = some col → col.toList = (y.1 x).2)
    (hcol1 : ∀ (i : ℕ) (col : Array F) (x : S.Pos), list1.idxOf? x.val = some i →
      columns1[i]? = some col → col.toList = (y.2 x).2)
    (r : (S.lkR (recZ S.P.T.l lg s)).X0) (k0 k1 : TableKey) (rc0 rc1 : List Row)
    (h3 : 3 * s ≤ S.P.T.l) (hk0 : KeyHasR S.P.v lg s (Λ.side false 1).index k0 r.1)
    (hk1 : KeyHasR S.P.v lg s (Λ.side true 1).index k1 r.2)
    (recs0 : (k0.seeds.zipIdx.mapM fun x =>
      foldeqRecordRow (Λ.side false 1) x.1 k0.record x.2 (foldeqWeights gamma)
        ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rc0)
    (recs1 : (k1.seeds.zipIdx.mapM fun x =>
      foldeqRecordRow (Λ.side true 1) x.1 k1.record x.2 (foldeqWeights gamma)
        ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rc1)
    (b : ℕ) (hb : b < S.nRowsR s) :
    readE ((rc0 ++ (rc1 ++ rE :: { row0 with target := y0 } :: { row1 with target := y1 } ::
        (rows0 ++ rows1))).getD b default).target =
        tgXR S (recZ S.P.T.l lg s) s (Equiv.refl (Fin s))
          (st4R S (recZ S.P.T.l lg s) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 b ∧
      ∀ (a : Bool) (r' p : ℕ), r' < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
        coefAt ((rc0 ++ (rc1 ++ rE :: { row0 with target := y0 } ::
          { row1 with target := y1 } :: (rows0 ++ rows1))).getD b default)
          (if a then o0 + 1 else o0) .main (r' + 2 ^ S.P.aR * p) =
          cfXR S (recZ S.P.T.l lg s) s (Equiv.refl (Fin s))
            (st4R S (recZ S.P.T.l lg s) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 b a r' p := by
  have hzl : z.length = S.P.aR + S.P.aP := by
    have h1 := congrArg List.length hz
    rw [List.length_map, List.length_take, hd.r2.els_length m2 c2] at h1
    omega
  have hgl : gamma.length = S.P.v := by
    rw [← hd.r1.els_length m1 c1, ← hgamma, List.length_map]
  have hR := linkRows_of S Λ codes hS hF.pow o0 gamma phi z beta y0 y1 D0 D1 rE row0 row1 rows0
    rows1 list0 list1 columns0 columns1 hzl hl0 hl1 heq form0 form1 cols0 cols1
  have hx := xTie_st4 S d1 d2 d3 d4 d5 dA hd y m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 gamma phi z beta y0 y1
    D0 D1 (fun k => (rows0.getD k default).target) (fun k => (rows1.getD k default).target) hgamma
    hz hbeta hy0 hy1 hD0 hD1 hphi
    (fun i x hi hx => folds_of (fun x => (y.1 x).2) _ _ _ _ _ _ _ cols0 hcol0 i x
      (by rw [hl0]; exact hi) hx)
    (fun i x hi hx => folds_of (fun x => (y.2 x).2) _ _ _ _ _ _ _ cols1 hcol1 i x
      (by rw [hl1]; exact hi) hx)
  have hγ : (st4R S (recZ S.P.T.l lg s) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1.1.1.1.2 =
      readP S.P.v gamma := by
    rw [st4R_gamma, readP_eq_ptL, hgamma]
    exact gVec_rvOf d1 m1 c1 _
  rw [← forget_st4R S (recZ S.P.T.l lg s) r] at hx
  exact rows_cfXR S lg s Λ _ _ o0 (o0 + 1) (Nat.succ_ne_self o0).symm _ k0 k1 gamma phi z beta y0
    y1 D0 D1 _ _ rc0 rc1 rE _ _ rows0 rows1 hF h3 ⟨hx, hgl, hγ, hk0, hk1⟩
    (linkRowsR_of S Λ codes hS o0 k0 k1 gamma phi z beta y0 y1 D0 D1 _ _ rc0 rc1 rE _ _ rows0
      rows1 hR recs0 recs1) b hb

end OnBytes.Slice
