-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstJoins.lean: two theorems that restate, with `ClaimTrue`
(Johnson/Desc/K12/Honest/ClaimTrue.lean), two theorems on the values in the stages of a proximity
test. `ClaimTrue s t P` says: whatever claim the verifier's state t (`T12`) passes is true at the
message `μOf s P` of the prover's state P (`PS`), read with the layout that is passed with it.
`first_claimTrue` is `first_V` (Johnson/Desc/K12/Honest/FirstValues.lean), on the first stage, with
`ClaimTrue` as the hypothesis on the claim before the first fold and as the conclusion. `second_V`
is `stage_V` (Johnson/Prover/Link/BodyStep.lean), on a fold and the switch after it at a stage that
is not the first, with `ClaimTrue` as the hypothesis on the claim before the fold. So the conclusion
of `first_claimTrue` has the form of that hypothesis of `second_V`, at the second stage's sizes.
`second_V` is stated at free sizes, states and stage number, not at the second stage, and
`ClaimTrue` is a hypothesis of it: no theorem of this file calls it at the conclusion of
`first_claimTrue`. Statements and proofs. The file does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

  `first_claimTrue`: under the hypotheses of `first_V`, with `ClaimTrue (sgOf a) t P` for its hin:
    `ClaimTrue` at `sgOf next`, the second stage's sizes, at `t3At` and at `qAt`
    (Johnson/Desc/K12/Honest/FirstYes.lean): the verifier's state after the first switch and the
    batching after it, and the prover's state after that switch, as the term `stagesAll`
    (Johnson/Desc/K12/Honest/Stages.lean) builds them
  `second_V`: under `ClaimTrue s t P` and every hypothesis of `stage_V` but its hin: the conclusion
    of `stage_V`: the claim of the row row' with the layout lay, the two that its hypothesis h
    (`Did`, Johnson/Desc/K12/Law/SwDid.lean) names, is true at the message `μOf s'` of the prover's
    next state (`nextPS`, Johnson/Prover/Link/BodyState.lean)

By what. `first_claimTrue` calls `first_V` at `hin row L hp`. That gives one claim which `t3At`
passes and which is true; whatever claim `t3At` passes is that one, since `.claim` is a constructor.
`second_V` is one call of `stage_V` at `hin row L H.pass`; `pass` is the field of `FoldFront`
(Johnson/Prover/Link/FormFold.lean) which says that t passes the claim of row with L.

Hypotheses. But for hin, each theorem has the hypotheses of the theorem that it calls, word for
word and under the same names: see FirstValues.lean and BodyStep.lean.

Limits.
- `second_V` has all of `stage_V`'s other hypotheses; that they hold is not shown here.
- Among them are hLk and hLh: the two numbers of the layout L are the stage's. `first_claimTrue`
  does not give them for the layout that `t3At` passes.
- `first_claimTrue` has `first_V`'s other hypotheses, among them the acceptances (`FirstYes`), and
  `ClaimTrue` before the first fold; that they hold is not shown here. The limits that
  FirstValues.lean states of `first_V` hold of it.
- Where the verifier's state passes no claim, `ClaimTrue` is vacuous. `first_V` also states that
  `t3At` passes a claim; `first_claimTrue` does not.
- In both theorems t and P are free parameters: that t is a state which a run of the verifier
  reaches is not stated.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ClaimTrue
import Johnson.Desc.K12.Honest.FirstValues
import Johnson.Prover.Link.BodyStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- **After the first switch, whatever claim the verifier's state passes is true.** True at the
message of `qAt`, the prover's state after that switch. It is `first_V` with `ClaimTrue` as the
hypothesis hin and as the conclusion. -/
theorem first_claimTrue (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn)
    (he : p.early = true) (h1 : p.answers = 1)
    (hl : l = laidS p)
    (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (Dp : Plain) (hD : gpOf p t a L = some Dp) (hok : ok (gpL p a row Dp) = true)
    (hhk : a.h ≤ a.k) (hhk' : next.h ≤ next.k) (hs : (sg a).Sized)
    (cu nx : IoppStage) (hcu : stageAt p 0 a = some cu) (hnx : stageAt p 1 next = some nx)
    (c : ℕ → ℕ → List UInt64) (R : PlainRows) (hC : ColsAt a Dp c R) (hS : StateAt a Dp P R)
    (Y : FirstYes p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D)
    (hr : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (ht : (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t)
    (hf : CsFit (sgOf a) (sgOf next))
    (hLk : L.k = (sgOf a).h + (sgOf a).g) (hLh : L.h = (sgOf a).h)
    (hin : ClaimTrue (sgOf a) t P)
    (hroom : (sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l)
    (hpk : P.fM = packedN (sgOf a) (K.W (sgOf a) 0))
    (hZl : ((t1At p K 0 a l o t P D).st.codes.mask.getD cu.maskCode default).ell = a.Z.l)
    (hOld : ∀ rows gp, (t1At p K 0 a l o t P D).pass = .single rows gp →
      OldOk (sgOf a) (sgOf next) (t1At p K 0 a l o t P D).st.codes rows nx.code nx.maskCode)
    (hwords : okE (((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
      (bitsAt p 0 next (t1At p K 0 a l o t P D)) zeroE) = true) :
    ClaimTrue (sgOf next)
      (t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D)
      (qAt K rest 0 a next o P D) := by
  intro rowX LX hX
  obtain ⟨row', lay', e1, e2⟩ := first_V p K rest a next l o t P D he h1 hl row L hp Dp hD hok hhk
    hhk' hs cu nx hcu hnx c R hC hS Y hr ht hf hLk hLh (hin row L hp) hroom hpk hZl hOld hwords
  rw [hX] at e1
  injection e1 with a1 a2
  rw [a1, a2]
  exact e2

/-- **`stage_V` with `ClaimTrue s t P` as its hypothesis on the claim before the fold.** At free
sizes s and s'. `ClaimTrue s t P` is a hypothesis; it is not proved here. -/
theorem second_V {s s' : Sg} (hf : CsFit s s') (hs : s.Sized) (P new : PS) (fr : ℕ → GE)
    {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
    {c : IoppStage} {n : ℕ × ℕ} {id : ℕ} (H : FoldFront p j cur t row L c n id) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : c.k = s.h + s.g) (hh : c.h = s.h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = s.Z.l)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h)
    (hin : ClaimTrue s t P)
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
      (μOf s' (nextPS s (readP (s.h + s.g) (rR.map drawnOf)) fr new P)) :=
  stage_V hf hs P new fr H rE rR hk hh hZ hLk hLh (hin row L H.pass) W γ hP hσ hR hkept h Pg hkeptO
    hG hd0 hd1 hc ht hx β hβ Qs hQ o m h1 hL seat hcols hans

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.first_claimTrue
#print axioms ProofFile.Honest.K12.second_V
