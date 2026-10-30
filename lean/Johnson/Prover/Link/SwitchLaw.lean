-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchLaw.lean: a code switch of the proximity test out of a stage that is not
the first, whole: the description's two parts return ok, and the claim behind them is true at an
honest prover's new message. The form's half and the values' half meet.

Main names (namespace `Johnson.Prover.Link`).
  `foldedFit_of_front`   the record in front of a fold (`FoldFront`,
      Johnson/Prover/Link/FormFold.lean) and the codes: what is public of the fold's output, as a
      switch asks it (`FoldedFit`, OnBytes/Slice/BlkProxSeg.lean)
  `switch_V'`   `switch_V` (Johnson/Prover/Link/SwitchV.lean), its public premises as `FoldedFit`
  `switch_law`   `SwitchFront`, `BehindFront` (Johnson/Prover/Link/FormSwitch.lean), `FoldedFit`,
      the premises of `hy_stage` (Johnson/Prover/Link/HyStage.lean), the claim in front true at the
      folded messages, the answer the true one: then both parts return ok, with the records behind
      as terms, and the row behind, read in the field, is true at the new message

By: `foldedFit_pure` (Johnson/Desc/K12/Law/FoldKeeps.lean), `foldShapeFits_agrees`,
`foldRowFits_agrees` (Johnson/Desc/Own/FoldAgree.lean), `foldRowFits_spent`
(Johnson/Prover/Link/FormFoldLaws.lean), `switch5_yes`, `behind5_yes`, `did_of_front`
(Johnson/Prover/Link/FormSwitchLaws.lean), `Did.group0` (Johnson/Desc/K12/Law/SwClaim.lean).

Limits. Every premise is asked; who pays the two fronts is not shown here. Two debts by name: the
drawn factor as a unit of the field (β with hβ) wants that the factor's words are not all 0 and are
below the prime; the codes' premises are the plan's. The first stage's tree has another reading law.
Nothing on how a tail, a mask or the free room's values are chosen. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchV
import Johnson.Prover.Link.FormSwitchLaws
import Johnson.Prover.Link.FormFoldLaws
import Johnson.Desc.K12.Law.FoldKeeps
import Johnson.Desc.Own.FoldAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK

/-- **What is public of the fold's output, as a switch asks it.** -/
theorem foldedFit_of_front (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (t : T12) (row : GroupRow)
    (L : GroupLayout) (c : IoppStage) (n : ℕ × ℕ) (id : ℕ) (rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (s s' : Sg) (F : FoldFront p j cur t row L c n id) (hK : StageCodes s c t.st.codes)
    (hzk : (t.st.codes.mask[c.maskCode]?).map codeOf = some s.Z)
    (hc' : (t.st.codes.base[n.1]?).map codeOf = some s'.C)
    (hz' : (t.st.codes.mask[n.2]?).map codeOf = some s'.Z) (hsmall : s.C.a ≤ 32)
    (h0 : row.kept = #[]) (hkept : ∀ i, i < L.members.size → L.kept.getD i false = false)
    (hlen : rR.length = s.h + s.g) :
    FoldedFit s s' t.st.codes n.1 n.2 (foldOut t row L c id (rE :: rR)) :=
  foldedFit_pure t.st.codes s s' c hK n.1 n.2 hzk hc' hz' hsmall t.st (spent t.st id) row L id
    (drawnOf rE) _ (rR.map drawnOf) rfl rfl h0 hkept (by rw [List.length_map]; exact hlen)
    ((Own.foldShapeFits_agrees _ _).trans F.shape)
    ((Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans F.rowFits))

/-- `switch_V` with its public premises in one record. -/
theorem switch_V' {s s' : Sg} (hf : CsFit s s') (hs : s.Sized)
    (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) (fr : ℕ → GE)
    {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {nc nz gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
        out row lay theta D)
    (ff : FoldedFit s s' S.codes nc nz old) (hG : D.G = { code := nc, maskCode := nz })
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (cu : IoppStage) (L : GroupLayout) (o id n : ℕ)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (h1 : 1 ≤ s.h + s.g)
    (hL : LayAt [o] #[some 0] #[some 0] L)
    (seat : SeatP S Bk [o, id] n s.C.a (stageShapes s cu))
    (hcols : ∀ c ∈ cols, c.2.1 < 2 ^ s.C.a ∧ c.2.2 = stageColW s tabM tabZ tM tZ fM fT c.2.1)
    (μ : s.cIn.J → GE) (ρ : s.cIn.Q → GE) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hM : ∀ b j, μ (.inl (b, j)) = tabM (Sz.rowNo b + 2 ^ (s.h + s.g) * j.val))
    (hZ : ∀ b j, μ (.inr (b, j)) = tabZ (Sz.rowNo b + 2 ^ s.h * j.val))
    (hTM : ∀ b q, ρ (.inl (b, q)) = tM (Sz.rowNo b) q.val)
    (hTZ : ∀ b q, ρ (.inr (b, q)) = tZ (Sz.rowNo b) q.val)
    (hF : ∀ b j, φ (b, j) = fM (Sz.rowNo b) j.val) (hT : ∀ b q, ψ (b, q) = fT (Sz.rowNo b) q.val)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = s.h + s.g)
    (hHolds : (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s old)
      (foldMsg s μ φ (readP (s.h + s.g) gamma)))
    (hans : readE D.alpha = gAns hf (foldMsg s μ φ (readP (s.h + s.g) gamma))
      (foldTl s ρ ψ (readP (s.h + s.g) gamma)) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row)
      (gMsg hf (foldMsg s μ φ (readP (s.h + s.g) gamma))
        (foldTl s ρ ψ (readP (s.h + s.g) gamma)) fr) :=
  switch_V hf hs tabM tabZ tM tZ fM fT fr h ff.prog ff.kept hG ff.d0 ff.d1 ff.vars ht hx β hβ Qs hQ
    cu L o id n hk hh h1 hL seat hcols μ ρ φ ψ hM hZ hTM hTZ hF hT S₀ row₀ eps claim gamma hold
    hkept hγ hHolds hans

/-- **The switch's whole law at a stage that is not the first.** -/
theorem switch_law {s s' : Sg} (hf : CsFit s s') (hs : s.Sized)
    (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) (fr : ℕ → GE)
    {p : P12} {n : IoppStage} {last : Bool} {dS dC : Fmt.DeclaredRound} {t : T12} {rS rC : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {rows : SingleRows} {gp : ℕ} {D : Taken} {j : ℕ}
    {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext} {row : GroupRow} {lay : GroupLayout}
    (cur : Fmt.M1.Stage) (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x)
    (F' : BehindFront p n last dC t gp D (E.ofTriple x) row lay)
    (hnk : n.k = s'.h + s'.g) (hnh : n.h = s'.h)
    (ff : FoldedFit s s' t.st.codes n.code n.maskCode rows)
    (hG : t.st.groups[gp]? = some { code := n.code, maskCode := n.maskCode })
    (ht : dC.entry.poss = s.t) (β : GEˣ) (hβ : β.val = readE D.beta)
    (cu : IoppStage) (L : GroupLayout) (o id nT : ℕ)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (h1 : 1 ≤ s.h + s.g)
    (hL : LayAt [o] #[some 0] #[some 0] L)
    (seat : SeatP t.st t.book [o, id] nT s.C.a (stageShapes s cu))
    (hcols : ∀ c ∈ keyed p [dS, dC] gs,
      c.2.1 < 2 ^ s.C.a ∧ c.2.2 = stageColW s tabM tabZ tM tZ fM fT c.2.1)
    (μ : s.cIn.J → GE) (ρ : s.cIn.Q → GE) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hM : ∀ b j, μ (.inl (b, j)) = tabM (Sz.rowNo b + 2 ^ (s.h + s.g) * j.val))
    (hZ : ∀ b j, μ (.inr (b, j)) = tabZ (Sz.rowNo b + 2 ^ s.h * j.val))
    (hTM : ∀ b q, ρ (.inl (b, q)) = tM (Sz.rowNo b) q.val)
    (hTZ : ∀ b q, ρ (.inr (b, q)) = tZ (Sz.rowNo b) q.val)
    (hF : ∀ b j, φ (b, j) = fM (Sz.rowNo b) j.val) (hT : ∀ b q, ψ (b, q) = fT (Sz.rowNo b) q.val)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : rows = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = s.h + s.g)
    (hHolds : (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s rows)
      (foldMsg s μ φ (readP (s.h + s.g) gamma)))
    (hans : readE D.alpha = gAns hf (foldMsg s μ φ (readP (s.h + s.g) gamma))
      (foldTl s ρ ψ (readP (s.h + s.g) gamma)) fr
      (readP _ ((rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes
        (switchTargetStage n.code n.maskCode (s'.h + s'.g) s'.h 1).shape).bits), β)) :
    (guardedProximityTestParts.switch p j cur next last [dS, dC]).decide t [rS, rC] gs =
        .ok (switchT p n last t rC gp D B (E.ofTriple x)) ∧
      (guardedProximityTestParts.batBehind p (j + 1) next [dS, dC]).decide
        (switchT p n last t rC gp D B (E.ofTriple x)) [] [] =
        .ok (behindT p n last t rC gp D B row lay) ∧
      (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row)
        (gMsg hf (foldMsg s μ φ (readP (s.h + s.g) gamma))
          (foldTl s ρ ψ (readP (s.h + s.g) gamma)) fr) := by
  refine ⟨switch5_yes cur F, behind5_yes dS rC j next B F', ?_⟩
  obtain ⟨out, D', e1, e2, ha, hb, hd⟩ := did_of_front cur F F'
  rw [hnk, hnh] at hd
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -⟩ := switchCut_says F.cut
  obtain ⟨-, ⟨-, g3, -, g5⟩, -⟩ := fit_says F.fit
  have hC : codeOf D.code = s.C := by
    have k := ff.prog.code
    rw [F.code] at k
    exact Option.some.inj k
  have hlog : dC.entry.logN = s.C.a := c10.trans (congrArg (·.a) hC)
  have hx : ∀ y ∈ rC.drawn.poss, y < 2 ^ s.C.a := by
    intro y hy
    have := List.all_eq_true.1 g5 y hy
    rw [hlog] at this
    exact of_decide_eq_true this
  have hlen : rC.drawn.poss.length = s.t := g3.trans ht
  have hin : ∀ i : Fin s.t, rC.drawn.poss.getD i.val 0 < 2 ^ s.C.a := by
    intro i
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
    exact hx _ (List.getElem_mem _)
  exact switch_V' hf hs tabM tabZ tM tZ fM fT fr hd ff
    (Option.some.inj (hd.group0.symm.trans hG)) (by rw [e2]; exact hlen)
    (by rw [e2]; exact hx) β (by rw [hb]; exact hβ) (fun i => ⟨rC.drawn.poss.getD i.val 0, hin i⟩)
    (fun i => by rw [e2]) cu L o id nT hk hh h1 hL seat hcols μ ρ φ ψ hM hZ hTM hTZ hF hT S₀ row₀
    eps claim gamma hold hkept hγ hHolds
    (by
      rw [ha]
      unfold Taken.z
      rw [e1]
      exact hans)

end Johnson.Prover.Link
