-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MergeRoadPub.lean: CONDITIONAL.

What is here. The two own claims behind "back" (`OwnBack`, Johnson/Road/K4/W/Join.lean: the batched
sumcheck's and the merge's) are worth 0 at a state behind the member's step, with nothing left on
the merge's sumcheck but public facts on the weights' layout (`ownBack_layout`). It is
`ownBack_units` (Law/W/MergeRoad.lean) with its hypothesis PanelUnits paid: `panelUnits_stand` has
PanelUnits at such a state from `panel_units` (Johnson/Road/K4/C/UnitsOfClaim.lean), at the
verifier's list of weight claims as the hearing's own call names it (`claims_sides`). So the whole
road of the merge's start stands in one statement: the honest tables of the weights are the
library's vectors of the claims (`opens_are`, Law/OpenTabs.lean); the end values read as the claims'
sums (`merged_of_opens`, Johnson/Road/K4/C/MergedOf.lean); the slots are worth these (`merged_at`,
Law/W/MergedAtStand.lean); the start is the cube's total (`merge_start_stand`,
Law/MergeStartAtStand.lean).

  `panelUnits_stand`   PanelUnits at a state behind the member's step.
  `ownBack_layout`   OwnBack at such a state.

Not shown here. JoinWorth (Law/StackStart.lean), WHICH HOLDS ALL THE CONTENT THAT IS LEFT OF THE
BATCHED SUMCHECK's OWN CLAIM (hJW); that the three words of one challenge lie below the prime (hok);
that the lookup's point is not empty (hz0): hypotheses; these two bear on the batched sumcheck's
claim, not on the merge's; Law/OkAtStand.lean has them (stand_ok, stand_z0), and Law/W/FootJoin.lean
calls both. SEVEN PUBLIC HYPOTHESES ON THE WEIGHTS' LAYOUT: it is one that wsLayOf returns for a
model with routed experts (hws); its widths d and fe are the layer sub-proof's (hd, hfe); sw.dq ≤
y.dq, sw.f ≤ h.f, sw.fe ≤ h.f (which follows from hfe and K4Plan, where f = 2 fe, and is kept as a
premise), sw.NE ≤ h.NE; Johnson/Road/K4/C/WsFacts.lean has the six from K4Plan and the library's
SizedW; no statement here ties the weights' layout to the layer sub-proof's. K4Stand, Thr,
K4LookTieAt, K4Plan (its field sw bars every shape but those with the library's eleven switches);
that "front" and "back" return: hypotheses. That all of these hold together: no example is known.
K4Seated's field fits (the public test k4Fits) is spent. The import closure holds what
Law/W/MergeRoad.lean's holds. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergeRoad
import Johnson.Road.K4.C.UnitsOfClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own ClaimEnv callsTS)
open OnBytes.Road.K4.W (K4Plan OwnBack)
open OnBytes.Road.K4.C (stack_open sides_fields panel_units)
open OnBytes.Desc.First.K4 (Par formsBack formsFrontWith)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ dataQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **PanelUnits AT A STATE BEHIND THE MEMBER's STEP.** CONDITIONAL: on every hypothesis named. -/
theorem panelUnits_stand {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m)
    {sw : WsShape} {lk : ℕ} (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hd : sw.d = Q.P.y.h.d)
    (hfe : sw.fe = Q.P.y.h.fe) (hdq : sw.dq ≤ Q.P.y.dq) (hf : sw.f ≤ Q.P.y.h.f)
    (hfef : sw.fe ≤ Q.P.y.h.f) (hNE : sw.NE ≤ Q.P.y.h.NE) :
    ∀ SD, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
        (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some SD →
      ∀ (TS : List ℕ) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
        ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
           rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
        PanelUnits SD Q.P.wsLay cl := by
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
  have SA := stackAt_at (seen := m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))
    Z hT hLk data ends
  have hv : OnBytes.Desc.First.K4.Honest.envOf Q
      (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) = some o.v :=
    env_is hH _ (by
      show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.zk = _
      rw [at_look _ _ ds hh]
      exact hzk)
  obtain ⟨_, _, _, hvS, _, _, _⟩ := sides_fields (stack_open data).1
  have ey : SD'.S.v.y = Q.P.y := by
    rw [Option.some.inj (hvS.symm.trans hv)]
    exact SA.y
  exact panel_units data (claims_sides L SA hv hTS hcl) hws (by rw [ey]; exact hd)
    (by rw [ey]; exact hfe) (by rw [ey]; exact hdq) (by rw [ey]; exact hf)
    (by rw [ey]; exact hfef) (by rw [ey]; exact hNE)

/-- **OwnBack AT A STATE BEHIND THE MEMBER's STEP: OF THE MERGE's SUMCHECK NOTHING IS LEFT BUT
PUBLIC FACTS ON THE WEIGHTS' LAYOUT.** CONDITIONAL: on every hypothesis named. -/
theorem ownBack_layout {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
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
    (hfe : sw.fe = Q.P.y.h.fe) (hdq : sw.dq ≤ Q.P.y.dq) (hf : sw.f ≤ Q.P.y.h.f)
    (hfef : sw.fe ≤ Q.P.y.h.f) (hNE : sw.NE ≤ Q.P.y.h.NE)
    (ds' : List Fmt.Drawn) {rows : Bool} {P' : Layer.Pub} {g' : ℕ}
    {fs₁ fs₂ : Array Aff} {F₁ F₂ : Fork} (hfr : formsFrontWith rows P' g' o A.F = some (fs₁, F₁))
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
            (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask entry) D') :
    OwnBack Reading.gl
      (F₂.worldOf Reading.gl
        (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask entry) o :=
  ownBack_units Z hT hLk AQ hws hd hfe ds' hfr hb entry hok hz0 hJW
    (panelUnits_stand Z hT hLk hws hd hfe hdq hf hfef hNE)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.panelUnits_stand
#print axioms ProofFile.Honest.K4.W.ownBack_layout
