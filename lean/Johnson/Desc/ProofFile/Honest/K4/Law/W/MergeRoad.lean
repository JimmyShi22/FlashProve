-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MergeRoad.lean: CONDITIONAL.

What is here. The road of the merge's start, in one environment: `ownBack_merged`
(Law/MergeStartAtStand.lean) asks what the slots under the weight claims' values are worth;
`merged_at` (Law/W/MergedAtStand.lean) has that from OpensAt; `opensAt_of_units`
(Law/W/OpensOfUnits.lean) has OpensAt from PanelUnits. The second hands the verifier's list of
claims at the environment that the hearing's own call names, the third asks it at the honest side's
environment with the challenges laid in: `claims_sides` carries the one into the other. So the two
own claims behind "back" (`OwnBack`, Johnson/Road/K4/W/Join.lean) are worth 0 at a state behind the
member's step with no start of the merge's sumcheck left as a hypothesis.

  `claims_sides`   the verifier's list of weight claims, at the honest side's environment with the
      challenges laid in.
  `opensAt_stand`   OpensAt at a state behind the member's step, from PanelUnits: the hypothesis hO
      of merged_at.
  `ownBack_units`   OwnBack at such a state.

Not shown here. PanelUnits (Law/W/OpensOfUnits.lean: at each panel the claims' units and their
extents) at the data that the honest side's function returns and at the verifier's list of weight
claims (hPU): a hypothesis HERE; Law/W/MergeRoadPub.lean has it from the layout (panelUnits_stand,
over panel_units, Johnson/Road/K4/C/UnitsOfClaim.lean); no member of it is evaluated in Lean; it can
hold only where the extents in the weights' layout are at most the panels'. JoinWorth
(Law/StackStart.lean), which holds all the content that is left of the batched sumcheck's own claim
(hJW); that the three words of one challenge lie below the prime (hok); that the lookup's point is
not empty (hz0): hypotheses. That the weights' layout is one that wsLayOf returns for a model with
routed experts, with the widths d and fe of the layer sub-proof's shape (hws, hd, hfe): public
hypotheses. K4Stand, Thr, K4LookTieAt, K4Plan (its field sw bars every shape but those with the
library's eleven switches); that "front" and "back" return: hypotheses. That all of these hold
together: no example is known. K4Seated's field fits is spent. The import closure holds what
Law/MergeStartAtStand.lean's, Law/WoShare.lean's and Law/OpenTabs.lean's hold: through
Law/WoShare.lean, which is imported for one public law (units_of_layout), more modules with
RecCompile in the name than the seven of the other files of Law/W/, and the threads'
Thread/SharesS.lean. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergedAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OpensOfUnits
import Johnson.Desc.ProofFile.Honest.K4.Law.W.HalvesNums
import Johnson.Desc.ProofFile.Honest.K4.Law.MergeStartAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsPubOf
import Johnson.Desc.ProofFile.Honest.K4.Law.WoShare
import Johnson.Road.K4.C.GatedNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own ClaimEnv callsTS)
open OnBytes.K.Kc (Tape)
open OnBytes.PscRun (Later)
open OnBytes.Road.K4 (LedG entryTrue)
open OnBytes.Road.K4.W (K4Plan OwnBack)
open OnBytes.Road.K4.C (OpensAt stack_open sides_fields gatedNums_of_plan)
open OnBytes.Desc.First.K4 (Par formsBack formsFrontWith formsFrontWith_later formsBack_later)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ dataQ)

/-- **The verifier's list of weight claims, at the honest side's environment with the challenges
laid in.** CONDITIONAL: on every hypothesis named. -/
theorem claims_sides {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {w : K4In} {h ds : List Fmt.Drawn}
    {seen : Seen} {SD : StackData} {e : List OnBytes.E}
    (Lg : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3'
      G4 G5 u5)
    (A : StackAt Q w h ds seen o SD e)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q (pts4 Q w h ds) = some o.v) {TS : List ℕ}
    {cl : List WsClaim} (hTS : callsTS Q.P = some TS)
    (hcl : ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
              rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl) :
    ({ SD.S.ce with rs := o.K.rs, rt := (pts4 Q w h ds).rt } : ClaimEnv).weightClaims SD.S.TS =
      some cl := by
  have hS := (stack_open A.data).1
  obtain ⟨_, _, _, hvS, _, hTS', _⟩ := sides_fields hS
  have eV : SD.S.v = o.v := Option.some.inj (hvS.symm.trans hv)
  have eT : SD.S.TS = TS := Option.some.inj (hTS'.symm.trans hTS)
  have ert : (pts4 Q w h ds).rt = (o.H.tT.map (·.r)).getD #[] := by
    rw [A.rt _ Lg.kTT, Lg.kTT]
    rfl
  rw [sides_ce hS, eV, eT, ert]
  exact hcl

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **OpensAt AT A STATE BEHIND THE MEMBER's STEP, FROM PanelUnits.** CONDITIONAL: on every
hypothesis named. -/
theorem opensAt_stand {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) {sw : WsShape} {lk : ℕ}
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay)
    (hPU : ∀ SD, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
        (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some SD →
      ∀ (TS : List ℕ) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
        ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
           rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
        PanelUnits SD Q.P.wsLay cl) :
    ∀ SD, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
        (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some SD →
      ∀ (TS : List ℕ) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
        ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
           rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
        OpensAt SD Q.P.wsLay (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) cl := by
  intro SD data TS cl hTS hcl
  obtain ⟨hd2, tT, ⟨F0, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, _⟩, _, _,
    _⟩ := stand_led Z
  obtain ⟨SD', e, data', ends, _⟩ :=
    stackJob_at Z hT (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q))
  obtain rfl : SD' = SD := Option.some.inj (data'.symm.trans data)
  obtain ⟨Fh, hH⟩ := stand_hear Z
  have hh := k4_heard_front Z.seat hT
  have hzk : (look Q m.st.heard).zk = o.H.fo.zk := by
    obtain ⟨g, _, q2, _, hz, _⟩ := hLk
    have el := stand_look Z
    rw [q2] at el
    obtain rfl := Option.some.inj el
    exact hz
  exact opensAt_of_units data
    (claims_sides L (stackAt_at (seen := m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))
        Z hT hLk data ends)
      (env_is hH _ (by
        show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.zk = _
        rw [at_look _ _ ds hh]
        exact hzk))
      hTS hcl)
    hws (hPU SD' data TS cl hTS hcl)

/-- **OwnBack AT A STATE BEHIND THE MEMBER's STEP, WITH NO START OF THE MERGE's SUMCHECK LEFT.**
CONDITIONAL: on every hypothesis named. -/
theorem ownBack_units {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    {h : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (AQ : K4Plan h pc Q.P Q.g tl D)
    {sw : WsShape} {lk : ℕ} (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hd : sw.d = Q.P.y.h.d)
    (hfe : sw.fe = Q.P.y.h.fe) (ds' : List Fmt.Drawn) {rows : Bool} {P' : Layer.Pub} {g' : ℕ}
    {fs₁ fs₂ : Array Aff} {F₁ F₂ : Fork} (hf : formsFrontWith rows P' g' o A.F = some (fs₁, F₁))
    (hb : formsBack o F₁ = some (fs₂, F₂)) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hok : ∀ tT, o.H.tT = some tT → OnBytes.okE tT.p.eps = true)
    (hz0 : o.H.fo.zx.isEmpty = false)
    (hJW : ∀ D', stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some D' →
      ∀ weighed parts tT', o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' →
        JoinWorth o.H tT' parts
          (F₂.worldOf Reading.gl
            (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask entry) D')
    (hPU : ∀ SD, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
        (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some SD →
      ∀ (TS : List ℕ) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
        ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
           rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
        PanelUnits SD Q.P.wsLay cl) :
    OwnBack Reading.gl
      (F₂.worldOf Reading.gl
        (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask entry) o := by
  obtain ⟨_, _, _, _, eg, ey⟩ := stand_led Z
  have hnE : 1 ≤ Layer.nEndT Q.P.y := by
    have e1 := (halvesNums_of_plan AQ ey eg).ends
    have e2 : 1 ≤ Q.P.y.LamM := by
      rw [(gatedNums_of_plan AQ).LamM]
      exact Nat.one_le_two_pow
    omega
  have L1 := formsFrontWith_later hf
  exact ownBack_merged Z hT hLk ds' L1 hb F₂ (Later.refl _) entry
    (fun _ hS => termsPub_of_plan AQ hws hS) hnE hok hz0 hJW (units_of_layout hws)
    (merged_at Z hT hLk ds' F₂ (L1.trans (formsBack_later hb)) entry hws hd hfe
      (opensAt_stand Z hT hLk hws hPU))

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.claims_sides
#print axioms ProofFile.Honest.K4.W.opensAt_stand
#print axioms ProofFile.Honest.K4.W.ownBack_units
