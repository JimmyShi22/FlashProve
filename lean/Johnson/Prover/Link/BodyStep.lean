-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyStep.lean: THE VALUES' STEP OF THE PROXIMITY TEST: A FOLD AND THE SWITCH
BEHIND IT, IN ONE STATEMENT, AT THE STATE BY INDEX (Johnson/Prover/Link/BodyState.lean). It composes
fold_V (FoldHolds.lean) with switch_V (SwitchV.lean), and at the link's first stage with
switch_V_first (FrontSwitch.lean). Statements and proofs.

  stage_V        the claim in front is true at μOf s P, READ WITH THE RECORD's OWN LAYOUT
                 (stmGk s L.k L.h row), whose two numbers are the stage's · the further table pairs
                 with W · the fold's rounds show what fold_V asks · FoldFront · what the switch
                 behind has done on the fold's own output (Did) · switch_V's public premises · each
                 dealt column is the written column of P · the answer is gAns
                 ⟹ the claim behind is true at μOf s' (nextPS ...), READ WITH ITS OWN LAYOUT
                 (stmGk s' lay.k lay.h row'): no premise on lay: so it serves into the last stage
  stage_V_first  the same out of the link's first stage, at firstPS

The joints that it closes: the fold ends at the point sPt 2 k γ and the switch starts at
readP k (the drawn elements): claimOf_shows · the switch's "old" is the fold's output: by foldOut's
text · the six premises that tie μ ρ φ ψ to tables by index: by μOf's text · the new message is the
next state's: muOf_next.

Not shown here. Every premise on the form is asked. Nothing on how W, a tail, a further table or
free room is chosen. Nothing on soundness; nothing on what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyState
import Johnson.Prover.Link.FoldHolds
import Johnson.Prover.Link.SwitchV
import Johnson.Prover.Link.FrontSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open H2K.Sw H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **A fold and the switch behind it, at a stage that is not the first.** -/
theorem stage_V {s s' : Sg} (hf : CsFit s s') (hs : s.Sized) (P new : PS) (fr : ℕ → GE)
    {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
    {c : IoppStage} {n : ℕ × ℕ} {id : ℕ} (H : FoldFront p j cur t row L c n id) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : c.k = s.h + s.g) (hh : c.h = s.h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = s.Z.l)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h)
    (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmGk s L.k L.h row) (μOf s P))
    (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (γ : HPt (sVars GE 2 (s.h + s.g)))
    (hP : Pairs s s.Z.l W (φOf s P))
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR (foldQ s (vecG s row) (μOf s P) W (readE (drawnOf rE)) γ) γ)
    (hkept : row.kept = #[])
    {ft : ℕ} {cols : List Tw.L9.Col} {nc nz gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row' : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (h : Did ft cols (foldOut t row L c id (rE :: rR))
        (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk' out row' lay
        theta D)
    (Pg : CsProg s s' S.codes (foldOut t row L c id (rE :: rR)) nc nz)
    (hkeptO : (foldOut t row L c id (rE :: rR)).kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : ((foldOut t row L c id (rE :: rR)).d.getD 0 #[]).size = s.Z.l)
    (hd1 : ((foldOut t row L c id (rE :: rR)).d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ (foldOut t row L c id (rE :: rR)).c.tensors, v.vars = ceilLog2 s.C.l)
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (o m : ℕ) (h1 : 1 ≤ s.h + s.g) (hL : LayAt [o] #[some 0] #[some 0] L)
    (seat : SeatP S Bk [o, id] m s.C.a (stageShapes s c))
    (hcols : ∀ x ∈ cols, x.2.1 < 2 ^ s.C.a ∧
      x.2.2 = stageColW s P.tabM P.tabZ P.tM P.tZ P.fM P.fT x.2.1)
    (hans : readE D.alpha = gAns hf
      (foldMsg s (μOf s P) (φOf s P) (readP (s.h + s.g) (rR.map drawnOf)))
      (foldTl s (ρOf s P) (ψOf s P) (readP (s.h + s.g) (rR.map drawnOf))) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row')
      (μOf s' (nextPS s (readP (s.h + s.g) (rR.map drawnOf)) fr new P)) := by
  obtain ⟨-, i2, i3⟩ := claimOf_shows _ rR _ γ
    (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target) hR
  have hin' : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) (μOf s P) := by
    have e : stmGk s L.k L.h row = stmG s row := by rw [stmG_eq, hLk, hLh]
    rw [← e]
    exact hin
  have hF := fold_V s (μOf s P) (φOf s P) W γ H rE rR hk hh hZ hin' hP hσ hR
  rw [← i2] at hF
  rw [muOf_next hf]
  exact switch_V hf hs P.tabM P.tabZ P.tM P.tZ P.fM P.fT fr h Pg hkeptO hG hd0 hd1 hc ht hx β hβ Qs
    hQ c L o id m hk hh h1 hL seat hcols (μOf s P) (ρOf s P) (φOf s P) (ψOf s P)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (spent t.st id) row (drawnOf rE)
    (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) (rR.map drawnOf) rfl
    hkept (by rw [List.length_map, i3]) hF hans

/-- **A fold and the switch behind it, out of the link's first stage.** -/
theorem stage_V_first (S₁ : Sz) (t₁ : ℕ) {s' : Sg} (hf : CsFit (S₁.sg t₁) s')
    (hs : (S₁.sg t₁).Sized) (m : Bool → S₁.MJ → GE) (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)
    (new : PS) (fr : ℕ → GE)
    {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
    {c : IoppStage} {n : ℕ × ℕ} {id : ℕ} (H : FoldFront p j cur t row L c n id) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : c.k = (S₁.sg t₁).h + (S₁.sg t₁).g) (hh : c.h = (S₁.sg t₁).h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = (S₁.sg t₁).Z.l)
    (hin : (Slf.idf (E := GE) (J := (S₁.sg t₁).cIn.J)).Holds (stmG (S₁.sg t₁) row)
      (μOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN)))
    (W : HIdx (sVars GE 2 ((S₁.sg t₁).h + (S₁.sg t₁).g)) → GE)
    (γ : HPt (sVars GE 2 ((S₁.sg t₁).h + (S₁.sg t₁).g)))
    (hP : Pairs (S₁.sg t₁) (S₁.sg t₁).Z.l W (φOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) =
      hMu (sVars GE 2 ((S₁.sg t₁).h + (S₁.sg t₁).g)) W)
    (hR : Shows ((S₁.sg t₁).h + (S₁.sg t₁).g) rR
      (foldQ (S₁.sg t₁) (vecG (S₁.sg t₁) row) (μOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN)) W
        (readE (drawnOf rE)) γ) γ)
    (hkept : row.kept = #[])
    {ft : ℕ} {cols : List Tw.L9.Col} {nc nz gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row' : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (h : Did ft cols (foldOut t row L c id (rE :: rR))
        (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk' out row' lay
        theta D)
    (Pg : CsProg (S₁.sg t₁) s' S.codes (foldOut t row L c id (rE :: rR)) nc nz)
    (hkeptO : (foldOut t row L c id (rE :: rR)).kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : ((foldOut t row L c id (rE :: rR)).d.getD 0 #[]).size = (S₁.sg t₁).Z.l)
    (hd1 : ((foldOut t row L c id (rE :: rR)).d.getD 1 #[]).size = (S₁.sg t₁).Z.l)
    (hc : ∀ v ∈ (foldOut t row L c id (rE :: rR)).c.tensors, v.vars = ceilLog2 (S₁.sg t₁).C.l)
    (ht : D.rC.drawn.poss.length = (S₁.sg t₁).t)
    (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ (S₁.sg t₁).C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin (S₁.sg t₁).t → (S₁.sg t₁).Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (o0 o1 k : ℕ) (sh frS : OracleShape)
    (hst : (Fmt.M2.starts [S₁.P.mem, S₁.P.mem]).1 = [some 0, some (2 ^ S₁.P.aR)])
    (hk1 : 2 ^ S₁.P.aR + S₁.P.R ≤ 2 ^ Fmt.M2.kOf [S₁.P.mem, S₁.P.mem])
    (hRw : sh.mainRows = S₁.P.R) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : frS.mainRows = 0) (hfz : 0 < frS.maskRows)
    (hwid : 3 * (S₁.P.R + S₁.P.R) + frS.maskRows * 3 = Fmt.M2.widthOf S₁.P.mems 1)
    (hL : LayAt [o0, o1] #[some 0, some (2 ^ S₁.P.aR)] #[none, none] L)
    (seat : SeatP S Bk [o0, o1, id] k (S₁.sg t₁).C.a [sh, sh, frS])
    (hcols : ∀ x ∈ cols, x.2.1 < 2 ^ S₁.P.C.a ∧
      x.2.2 = firstColW S₁ (membN S₁ m) tN φN ψN x.2.1)
    (hans : readE D.alpha = gAns hf
      (foldMsg (S₁.sg t₁) (μOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN))
        (φOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN))
        (readP ((S₁.sg t₁).h + (S₁.sg t₁).g) (rR.map drawnOf)))
      (foldTl (S₁.sg t₁) (ρOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN))
        (ψOf (S₁.sg t₁) (firstPS S₁ m tN φN ψN))
        (readP ((S₁.sg t₁).h + (S₁.sg t₁).g) (rR.map drawnOf))) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row')
      (μOf s' (nextPS (S₁.sg t₁) (readP ((S₁.sg t₁).h + (S₁.sg t₁).g) (rR.map drawnOf)) fr new
        (firstPS S₁ m tN φN ψN))) := by
  obtain ⟨-, i2, i3⟩ := claimOf_shows _ rR _ γ
    (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target) hR
  have hF := fold_V (S₁.sg t₁) _ _ W γ H rE rR hk hh hZ hin hP hσ hR
  rw [← i2] at hF
  rw [muOf_next hf]
  exact switch_V_first S₁ t₁ hf hs (membN S₁ m) tN φN ψN fr h Pg hkeptO hG hd0 hd1 hc ht hx β hβ Qs
    hQ c L o0 o1 id k sh frS hk hh hst hk1 hRw h3 hz hfm hfz hwid hL seat hcols _ _ _ _
    (first_mem S₁ t₁ m tN φN ψN) (first_free S₁ t₁ m tN φN ψN) (first_mask S₁ t₁ m tN φN ψN)
    (first_tail S₁ t₁ m tN φN ψN)
    (fun a i q h1 h2 => first_tail_free S₁ t₁ m tN φN ψN a i q h1 h2)
    (first_tail_mask S₁ t₁ m tN φN ψN) (first_phi S₁ t₁ m tN φN ψN) (first_psi S₁ t₁ m tN φN ψN)
    (spent t.st id) row (drawnOf rE)
    (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) (rR.map drawnOf) rfl
    hkept (by rw [List.length_map, i3]) hF hans

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.stage_V_first
#print axioms Johnson.Prover.Link.stage_V
