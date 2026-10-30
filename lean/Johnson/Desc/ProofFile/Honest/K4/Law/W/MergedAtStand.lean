-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MergedAtStand.lean: CONDITIONAL.

Not shown here. OpensAt (Johnson/Road/K4/C/MergedOf.lean) at the data that the honest side's
function returns and at the verifier's list of weight claims (hO): a hypothesis; no statement here
leads to it; no member of it is evaluated in Lean; it can hold only where the extents in the
weights' layout are at most the panels'. That the weights' layout is one that wsLayOf returns for a
model with routed experts, with the widths d and fe of the layer sub-proof's shape (hl, hd, hfe):
public hypotheses. K4Stand, Thr, K4LookTieAt: hypotheses. That all of these hold together: no
example is known. K4Seated's field fits (the public test k4Fits) is spent. By a walk of import lines
the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms,
Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under
Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness
or on any other property. No property is claimed.

The field merged of `OpenedOwn` (Johnson/Road/K4/W/OpenedOwn.lean) at a state behind the member's
step, at the list of weight claims that the hearing's own call returns: one call of `own_merged`
(Law/W/MergedAt.lean). Its premises at such a state: the library's LedG and what the tape has
sampled by `stand_led` (Law/PtsAtStand.lean); the left half by `opened_left` (Law/SlotsTrue.lean);
StackAt by `stackAt_at`, the honest side's two returns by `stackJob_at` (Law/W/MakersReturn.lean);
the structure that the forms read by `env_is` (Law/ClaimsAre.lean) at `stand_hear`
(Law/W/StandHear.lean). The conclusion is, in its letters, the hypothesis on the slots under the
weight claims' values that a law on the start of the merge's sumcheck asks at such a state.

  `merged_at`   OpenedOwn's field merged at a state behind the member's step.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergedAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersReturn
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StandHear
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own ClaimEnv callsTS)
open OnBytes.PscRun (Later)
open OnBytes.Road.K4.C (OpensAt)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ dataQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **OpenedOwn's FIELD merged AT A STATE BEHIND THE MEMBER's STEP.** CONDITIONAL: on every
hypothesis named. -/
theorem merged_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) (F : Fork)
    (hL : Later A.F F) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {sw : WsShape} {lk : ℕ}
    (hl : wsLayOf sw true lk = .ok Q.P.wsLay) (hd : sw.d = Q.P.y.h.d) (hfe : sw.fe = Q.P.y.h.fe)
    (hO : ∀ SD, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
        (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some SD →
      ∀ (TS : List ℕ) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
        ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
           rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
        OpensAt SD Q.P.wsLay (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) cl) :
    ∀ (TS : List ℕ) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
      ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
         rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
      ∀ a x, cl[a]? = some x →
        (F.worldOf Reading.gl (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
          entry).slot (o.K.sV + a) =
          OnBytes.Road.claimVal Reading.gl Q.P.wsLay
            (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) x := by
  intro TS cl hTS hcl
  obtain ⟨hd2, tT, ⟨F0, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, _,
    _⟩ := stand_led Z
  have l4 : k4StartAt Q 4 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  obtain ⟨SD, e, data, ends, _⟩ :=
    stackJob_at Z hT (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q))
  obtain ⟨Fh, hH⟩ := stand_hear Z
  have hh := k4_heard_front Z.seat hT
  have hzk : (look Q m.st.heard).zk = o.H.fo.zk := by
    obtain ⟨g, _, q2, _, hz, _⟩ := hLk
    have el := stand_look Z
    rw [q2] at el
    obtain rfl := Option.some.inj el
    exact hz
  exact own_merged L hD l4 (opened_left Z ds' F hL entry) (stackAt_at Z hT hLk data ends)
    (env_is hH _ (by
      show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.zk = _
      rw [at_look _ _ ds hh]
      exact hzk))
    hTS hcl hl hd hfe (hO SD data TS cl hTS hcl)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.merged_at
