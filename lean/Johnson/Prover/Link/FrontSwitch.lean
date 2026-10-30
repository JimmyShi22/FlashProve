-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontSwitch.lean: the values' half of THE LINK's FIRST code switch, as one
statement: claim_behind (Johnson/Prover/Link/SwitchHolds.lean) with its premise on what was read
paid by hy_first (Johnson/Prover/Link/FrontHy.lean). The twin, at the first stage, of switch_V
(Johnson/Prover/Link/SwitchV.lean), whose text it follows line for line.

  switch_V_first   the claim in front is true at the three folded messages · what the switch and the
      batching behind it have done (Did) · the public premises of did_sem and of linkReads · each
      dealt column is firstColW at its own position · μ ρ φ ψ hold the members' rows and tails on
      their blocks, 0 elsewhere, and the further row · the answer that the switch has taken reads as
      gAns: then the row behind, read in the field, is true at the new message gMsg

Limits. Every premise is asked. That the switch says yes is inside Did. Nothing on how a tail, the
further row or the free room's values are chosen. Nothing on soundness; nothing on what any entry
discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchHolds
import Johnson.Prover.Link.FrontHy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open H2K.Sw H2K.JointK

/-- **The values' half of the link's first switch.** -/
theorem switch_V_first (S : Sz) (t : ℕ) {s' : Sg} (hf : CsFit (S.sg t) s') (hs : (S.sg t).Sized)
    (mN tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE) (fr : ℕ → GE)
    {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {nc nz gp : ℕ}
    {others : Array OracleNotice} {St St' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others St Bk roots St'
        Bk' out row lay theta D)
    (P : CsProg (S.sg t) s' St.codes old nc nz) (hkeptO : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = (S.sg t).Z.l) (hd1 : (old.d.getD 1 #[]).size = (S.sg t).Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 (S.sg t).C.l)
    (ht : D.rC.drawn.poss.length = (S.sg t).t)
    (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ (S.sg t).C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin (S.sg t).t → (S.sg t).Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (cu : IoppStage) (L : GroupLayout) (o0 o1 id n : ℕ) (sh frS : OracleShape)
    (hk : cu.k = (S.sg t).h + (S.sg t).g) (hh : cu.h = (S.sg t).h)
    (hst : (Fmt.M2.starts [S.P.mem, S.P.mem]).1 = [some 0, some (2 ^ S.P.aR)])
    (hk1 : 2 ^ S.P.aR + S.P.R ≤ 2 ^ Fmt.M2.kOf [S.P.mem, S.P.mem])
    (hR : sh.mainRows = S.P.R) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : frS.mainRows = 0) (hfz : 0 < frS.maskRows)
    (hwid : 3 * (S.P.R + S.P.R) + frS.maskRows * 3 = Fmt.M2.widthOf S.P.mems 1)
    (hL : LayAt [o0, o1] #[some 0, some (2 ^ S.P.aR)] #[none, none] L)
    (seat : SeatP St Bk [o0, o1, id] n (S.sg t).C.a [sh, sh, frS])
    (hcols : ∀ c ∈ cols, c.2.1 < 2 ^ S.P.C.a ∧ c.2.2 = firstColW S mN tN φN ψN c.2.1)
    (μ : (S.sg t).cIn.J → GE) (ρ : (S.sg t).cIn.Q → GE) (φ : (S.sg t).cFr.J → GE)
    (ψ : (S.sg t).cFr.Q → GE)
    (hμ : ∀ a i, i < S.P.R → ∀ j, μ (.inl (memRow S t a i, j)) = mN a i j.val)
    (hμz : FreeZero S t μ) (hμm : ∀ j, μ (.inr j) = 0)
    (hρ : ∀ a i, i < S.P.R → ∀ q, ρ (.inl (memRow S t a i, q)) = tN a i q.val)
    (hρz : ∀ a i q, S.P.R ≤ i → i < 2 ^ S.P.aR → ρ (.inl (memRow S t a i, q)) = 0)
    (hρm : ∀ q, ρ (.inr q) = 0)
    (hφ : ∀ b j, φ (b, j) = φN j.val) (hψ : ∀ b q, ψ (b, q) = ψN q.val)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = (S.sg t).h + (S.sg t).g)
    (hHolds : (Slf.idf (E := GE) (J := (S.sg t).cMid.J)).Holds (stmS (S.sg t) old)
      (foldMsg (S.sg t) μ φ (readP ((S.sg t).h + (S.sg t).g) gamma)))
    (hans : readE D.alpha = gAns hf (foldMsg (S.sg t) μ φ (readP ((S.sg t).h + (S.sg t).g) gamma))
      (foldTl (S.sg t) ρ ψ (readP ((S.sg t).h + (S.sg t).g) gamma)) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) St), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row)
      (gMsg hf (foldMsg (S.sg t) μ φ (readP ((S.sg t).h + (S.sg t).g) gamma))
        (foldTl (S.sg t) ρ ψ (readP ((S.sg t).h + (S.sg t).g) gamma)) fr) := by
  have hC : codeOf D.code = (S.sg t).C := by
    have k := P.code
    rw [h.code] at k
    exact Option.some.inj k
  have hlog : D.code.logN = (S.sg t).C.a := congrArg (·.a) hC
  exact claim_behind hf _ _ fr (laws_of_sized hs) h P hkeptO hG hd0 hd1 hc ht hx β hβ Qs hQ
    (hy_first S t mN tN φN ψN hs cu L o0 o1 id n sh frS h hk hh hst hk1 hR h3 hz hfm hfz hwid hL
      seat hcols μ ρ φ ψ hμ hμz hμm hρ hρz hρm hφ hψ S₀ row₀ eps claim gamma hold hkept hγ hlog Qs
      hQ ht)
    hHolds hans

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.switch_V_first
