-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyStepF.lean: THE VALUES' CLAUSE BEHIND THE FIRST STAGE, whose tree is the
link's own (two members' rows and the row beside them), AT WHAT THE FORM's STEP HANDS (StepDone,
Johnson/Prover/Link/FormStep.lean) AND AT bodyAll's OWN PIECES. Statements and proofs.

  first_at_s    stage_V_first (BodyStep.lean) with the stage's sizes as a letter s and s = S.sg t₀
                as a premise: a tool: bodyAll speaks at sgOf cur, the link's laws at S.sg t₀
  val_first     the plan's step · the form's half · the claim true at the first state · the packing
                · the first tree's column, seat and layout · the positions that "CS" drew ·
                StepDone at sRF | sRS | sGS ⟹ the claim behind the batching is true at sNext's
                message

Not shown here. Nothing on soundness; nothing on what any value that is sent discloses or does not
disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyStepV

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open H2K.Pub (sgOf)

/-- stage_V_first with the stage's sizes as a letter. -/
theorem first_at_s (S₁ : Sz) (t₁ : ℕ) (s : Sg) (es : s = S₁.sg t₁) {s' : Sg} (hf : CsFit s s')
    (hs : s.Sized) (m : Bool → S₁.MJ → GE) (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)
    (new : PS) (fr : ℕ → GE)
    {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
    {c : IoppStage} {n : ℕ × ℕ} {id : ℕ} (H : FoldFront p j cur t row L c n id) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : c.k = s.h + s.g) (hh : c.h = s.h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = s.Z.l)
    (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) (μOf s (firstPS S₁ m tN φN ψN)))
    (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (γ : HPt (sVars GE 2 (s.h + s.g)))
    (hP : Pairs s s.Z.l W (φOf s (firstPS S₁ m tN φN ψN)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR
      (foldQ s (vecG s row) (μOf s (firstPS S₁ m tN φN ψN)) W (readE (drawnOf rE)) γ) γ)
    (hkept : row.kept = #[])
    {ft : ℕ} {cols : List Tw.L9.Col} {nc nz gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row' : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (h : Did ft cols (foldOut t row L c id (rE :: rR))
        (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk' out row' lay
        theta D)
    (ff : FoldedFit s s' S.codes nc nz (foldOut t row L c id (rE :: rR)))
    (hG : D.G = { code := nc, maskCode := nz })
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta)
    (o0 o1 k : ℕ) (sh frS : OracleShape)
    (hst : (Fmt.M2.starts [S₁.P.mem, S₁.P.mem]).1 = [some 0, some (2 ^ S₁.P.aR)])
    (hk1 : 2 ^ S₁.P.aR + S₁.P.R ≤ 2 ^ Fmt.M2.kOf [S₁.P.mem, S₁.P.mem])
    (hRw : sh.mainRows = S₁.P.R) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : frS.mainRows = 0) (hfz : 0 < frS.maskRows)
    (hwid : 3 * (S₁.P.R + S₁.P.R) + frS.maskRows * 3 = Fmt.M2.widthOf S₁.P.mems 1)
    (hL : LayAt [o0, o1] #[some 0, some (2 ^ S₁.P.aR)] #[none, none] L)
    (seat : SeatP S Bk [o0, o1, id] k (S₁.sg t₁).C.a [sh, sh, frS])
    (hcols : ∀ x ∈ cols, x.2.1 < 2 ^ s.C.a ∧ x.2.2 = firstColW S₁ (membN S₁ m) tN φN ψN x.2.1)
    (hans : readE D.alpha = gAns hf
      (foldMsg s (μOf s (firstPS S₁ m tN φN ψN)) (φOf s (firstPS S₁ m tN φN ψN))
        (readP (s.h + s.g) (rR.map drawnOf)))
      (foldTl s (ρOf s (firstPS S₁ m tN φN ψN)) (ψOf s (firstPS S₁ m tN φN ψN))
        (readP (s.h + s.g) (rR.map drawnOf))) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row')
      (μOf s' (nextPS s (readP (s.h + s.g) (rR.map drawnOf)) fr new
        (firstPS S₁ m tN φN ψN))) := by
  subst es
  have hin' : ∀ i : Fin (S₁.sg t₁).t, D.rC.drawn.poss.getD i.val 0 < 2 ^ (S₁.sg t₁).C.a := by
    intro i
    rw [List.getD_eq_getElem _ _ (by rw [ht]; exact i.isLt)]
    exact hx _ (List.getElem_mem _)
  exact stage_V_first S₁ t₁ hf hs m tN φN ψN new fr H rE rR hk hh hZ hin W γ hP hσ hR hkept h
    ff.prog ff.kept hG ff.d0 ff.d1 ff.vars ht hx β hβ
    (fun i => ⟨D.rC.drawn.poss.getD i.val 0, hin' i⟩) (fun _ => rfl) o0 o1 k sh frS hst hk1 hRw h3
    hz hfm hfz hwid hL seat hcols hans

section
variable {p : P12} {K : BCoins} {last : Bool} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ}
  {t : T12} {col : ℕ → List UInt64} {row : GroupRow} {L : GroupLayout} {c n : IoppStage}
  {dS dC : Fmt.DeclaredRound} {id tN : ℕ} {tr : Tree} {Dr : ℕ → Fmt.Drawn}

/-- **Behind the first stage the claim is true at sNext's message.** -/
theorem val_first (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (S₁ : Sz) (t₁ : ℕ) (m : Bool → S₁.MJ → GE) (tN' : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)
    (es : sgOf cur = S₁.sg t₁)
    (hin : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmGk (sgOf cur) L.k L.h row)
      (μOf (sgOf cur) (firstPS S₁ m tN' φN ψN)))
    (hpk : (firstPS S₁ m tN' φN ψN).fM = packedN (sgOf cur) (K.W (sgOf cur) j))
    (hc : col = firstColW S₁ (membN S₁ m) tN' φN ψN)
    (o0 o1 k : ℕ) (sh frS : OracleShape)
    (hst : (Fmt.M2.starts [S₁.P.mem, S₁.P.mem]).1 = [some 0, some (2 ^ S₁.P.aR)])
    (hk1 : 2 ^ S₁.P.aR + S₁.P.R ≤ 2 ^ Fmt.M2.kOf [S₁.P.mem, S₁.P.mem])
    (hRw : sh.mainRows = S₁.P.R) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : frS.mainRows = 0) (hfz : 0 < frS.maskRows)
    (hwid : 3 * (S₁.P.R + S₁.P.R) + frS.maskRows * 3 = Fmt.M2.widthOf S₁.P.mems 1)
    (hL : LayAt [o0, o1] #[some 0, some (2 ^ S₁.P.aR)] #[none, none] L)
    (seat : SeatP t.st t.book [o0, o1, id] k (S₁.sg t₁).C.a [sh, sh, frS])
    (hlt : ∀ x ∈ (Dr (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems, ltE x = true)
    (ht : (Dr (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss.length = (sgOf cur).t)
    (hx : ∀ x ∈ (Dr (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss, x < 2 ^ (sgOf cur).C.a)
    (e1 : sT1 p K j cur l o t (firstPS S₁ m tN' φN ψN) row Dr =
      foldT t row L c (n.code, n.maskCode) id
        ((sRF K j cur o (firstPS S₁ m tN' φN ψN) row Dr).map noDigest))
    {Dk : Taken} {x : Fmt.Ext} {row' : GroupRow}
    (Dn : StepDone (sgOf cur) (sgOf next) p n last dS dC
      (foldT t row L c (n.code, n.maskCode) id
        ((sRF K j cur o (firstPS S₁ m tN' φN ψN) row Dr).map noDigest))
      (noDigest ⟨[], Dr (o + 1 + ((sgOf cur).h + (sgOf cur).g))⟩)
      (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t (firstPS S₁ m tN' φN ψN) row Dr))],
        Dr (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩)
      (sGS cur o col Dr)
      (foldOut t row L c id ((sRF K j cur o (firstPS S₁ m tN' φN ψN) row Dr).map noDigest))
      t.st.groups.size j cur next tN
      (ofE (sAns p K j cur next l o t (firstPS S₁ m tN' φN ψN) row Dr)) Dk x row') :
    (Slf.idf (E := GE) (J := (sgOf next).cIn.J)).Holds
      (stmGk (sgOf next)
        (stepL p n last (foldT t row L c (n.code, n.maskCode) id
          ((sRF K j cur o (firstPS S₁ m tN' φN ψN) row Dr).map noDigest)) t.st.groups.size Dk).k
        (stepL p n last (foldT t row L c (n.code, n.maskCode) id
          ((sRF K j cur o (firstPS S₁ m tN' φN ψN) row Dr).map noDigest)) t.st.groups.size Dk).h
        row')
      (μOf (sgOf next) (sNext K last j cur next o (firstPS S₁ m tN' φN ψN) row Dr)) := by
  have hZ : (t.st.codes.mask.getD c.maskCode default).ell = (sgOf cur).Z.l :=
    congrArg (·.l) Pl.codes.mask
  have hin' : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmG (sgOf cur) row)
      (μOf (sgOf cur) (firstPS S₁ m tN' φN ψN)) := by
    have e : stmGk (sgOf cur) L.k L.h row = stmG (sgOf cur) row := by
      rw [stmG_eq, I.layK, I.layH]
    rw [← e]
    exact hin
  have hR := shows_noDigest _ _ _ _ (foldRV_shows (sgOf cur) (vecG (sgOf cur) row)
    (μOf (sgOf cur) (firstPS S₁ m tN' φN ψN)) (K.W (sgOf cur) j) fun n => Dr (o + n))
  have eT : swTarget p n =
      switchTargetStage n.code n.maskCode ((sgOf next).h + (sgOf next).g) (sgOf next).h 1 := by
    unfold swTarget
    rw [Pl.nk, Pl.nh, Pl.one]
  have hseed := Dn.front.seed
  have hd := Dn.did
  rw [eT] at hseed hd
  have hβ := beta_at (Dr (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems _ Dk.beta hseed
    Dn.front.factor hlt
  have hA := ans_at p K j cur next l o t (firstPS S₁ m tN' φN ψN) row Dr Pl.fits
  rw [e1, Pl.stageN, gam_at] at hA
  have h3 := first_at_s S₁ t₁ (sgOf cur) es Pl.fits Pl.sized m tN' φN ψN
    (if last then K.new j else
      { K.new j with fM := packedN (sgOf next) (K.W (sgOf next) (j + 1)) }) (K.fr j) I.front
    (noDigest ⟨[.e (ofE (hMu (sVars GE 2 ((sgOf cur).h + (sgOf cur).g)) (K.W (sgOf cur) j)))],
      Dr (o + 0)⟩) _ Pl.codes.k Pl.codes.h hZ hin' (K.W (sgOf cur) j) _
    (pairs_packedN (sgOf cur) Pl.room _ _ hpk) (foldRV_sigma (sgOf cur) (K.W (sgOf cur) j) _) hR
    I.kept0 hd Dn.ff Dn.G (by rw [Dn.isC]; exact ht) (by rw [Dn.isC]; exact hx) _ hβ o0 o1 k sh frS
    hst hk1 hRw h3 hz hfm hfz hwid hL (seatP_foldT seat row L c _ id _)
    (fun q hq => by
      have := cols_at p cur o col Dr [dS, dC] q hq
      rw [hc] at this
      exact this)
    (by
      rw [Dn.alpha]
      unfold Taken.z
      rw [Dn.isS]
      exact hA)
  unfold sNext
  rw [gam_at]
  exact h3

end

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.first_at_s
#print axioms Johnson.Prover.Link.val_first
