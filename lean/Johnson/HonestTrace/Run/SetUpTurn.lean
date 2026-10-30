-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpTurn.lean

The steps of "publicOfO" (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) at a turned scan and a turned
layout ("scanTurn", "layTurn", "pubTurn": Johnson/HonestTrace/Run/SetUpTurnDefs.lean). Theorems
alone; no definition. All stand at variable records: no stored file is named here. The marks p1,
p8, p13 and so on in the comments are the names of the hypotheses of the library's
"publicOfO_of_parts" (Johnson/AtFull/Public/Ledger.lean).

Main theorems:
* "polLayout_turn": where "polLayout pol" returns (P, y) and "polScan pol'" returns P turned,
  "polLayout pol'" returns P and y turned. Asked besides: hsh, the layers' shape of the turned
  scan is that of P with eps1, eps2, epsF set; and 1 ≤ eps1 < 2^59, 1 ≤ eps2 < 2^59.
* "matIx_turn", "tails_turn", "reads_turn", "mq_turn", "border_turn", "settings_turn", "owner_turn",
  "widths_turn", "vocabulary_turn", "wsLay_turn", "planH2_turn": steps that give the same at the
  turned records; "headShape_turn": the head's shape at the turned records. Each holds by "rfl".
* "headLayout_turn": the head's layout returns the same at the turned records, under bounds on MF,
  KF, epsF, theta, cap and C.
* "pubOf_turn", "planG_turn", "plansFrom_turn", "plansG_turn": the layers' record and its plans.

Limits. Conditional throughout: no file at which a step returns is shown here.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.Run.SetUpTurnDefs
import Johnson.HonestTrace.Run.SetUpLay
import Johnson.HonestTrace.Run.SetUpHead
import Johnson.AtFull.Public.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok refuseIf_no)
open VerifierAndGoals (FreeLines)
open OnBytes.Road.K4.Trial.AttL2 (mqOf seenGOf AOf)

/-! ### p1 -/

theorem polLayout_turn {pol pol' : ByteArray} {P : PolScan} {y : Layer.Lay}
    {vals : List (String × Nat)} {v : FreeLines}
    (h : polLayout pol = .ok (P, y)) (hs : polScan pol' = .ok (scanTurn P vals v))
    (hsh : layerShape (scanTurn P vals v) =
      { layerShape P with eps1 := v.eps1, eps2 := v.eps2, epsF := v.epsF })
    (h1 : 1 ≤ v.eps1 ∧ v.eps1 < 2 ^ 59) (h2 : 1 ≤ v.eps2 ∧ v.eps2 < 2 ^ 59) :
    polLayout pol' = .ok (scanTurn P vals v, layTurn y v) := by
  unfold polLayout at h ⊢
  obtain ⟨P0, _, h⟩ := exc_bind h
  obtain ⟨_, a1, h⟩ := exc_bind h
  obtain ⟨y0, hy, h⟩ := exc_bind h
  obtain ⟨_, a2, h⟩ := exc_bind h
  obtain ⟨_, a3, h⟩ := exc_bind h
  obtain ⟨_, a4, h⟩ := exc_bind h
  cases h
  refine (bind_ok hs).trans ?_
  refine (bind_ok a1).trans ?_
  refine (bind_ok (a := layTurn y v) ?_).trans ?_
  · rw [hsh]
    exact layout_eps hy h1 h2
  refine (bind_ok a2).trans ?_
  refine (bind_ok a3).trans ?_
  refine (bind_ok a4).trans ?_
  rfl

/-! ### the small steps: each reads none of the turned fields -/

section
variable (P : PolScan) (y : Layer.Lay) (vals : List (String × Nat)) (v : FreeLines)

theorem matIx_turn : Layer.matIx (layTurn y v) = Layer.matIx y := rfl

theorem tails_turn : Layer.tailsOf (layTurn y v) = Layer.tailsOf y := rfl

theorem reads_turn : Layer.readsOf (layTurn y v) = Layer.readsOf y := rfl

theorem mq_turn : mqOf (layTurn y v) = mqOf y := rfl

theorem border_turn : borderOf (layTurn y v) = borderOf y := rfl

theorem settings_turn : (scanTurn P vals v).settings = P.settings := rfl

theorem owner_turn (G : Array Layer.HPlan2) : ownerOf (layTurn y v) G = ownerOf y G := rfl

/-- p8 -/
theorem widths_turn : Layer.weightWidthsHeld (layTurn y v).h (layTurn y v).kinds =
    Layer.weightWidthsHeld y.h y.kinds := rfl

/-- p8' -/
theorem vocabulary_turn : Head.vocabulary (headShape (scanTurn P vals v) (layTurn y v)) =
    Head.vocabulary (headShape P y) := rfl

/-- p9 -/
theorem wsLay_turn : wsLayOf (weightShape (scanTurn P vals v) (layTurn y v)) (layTurn y v).h.p3
    (scanTurn P vals v).lkW = wsLayOf (weightShape P y) y.h.p3 P.lkW := rfl

theorem headShape_turn : headShape (scanTurn P vals v) (layTurn y v) =
    ({ headShape P y with MF := v.MF, KF := v.KF, epsF := v.epsF } : Head.Shape).withPol
      v.C v.theta v.cap := rfl

/-- p19 -/
theorem planH2_turn (L : Head.HL) (O : Head.Owner) :
    Head.planH2 (scanTurn P vals v).settings (headShape (scanTurn P vals v) (layTurn y v)) L
      (borderOf (layTurn y v)) O (layTurn y v).NGr (scanTurn P vals v).lkW =
    Head.planH2 P.settings (headShape P y) L (borderOf y) O y.NGr P.lkW := rfl

end

/-- p13 -/
theorem headLayout_turn {P : PolScan} {y : Layer.Lay} (vals : List (String × Nat)) {v : FreeLines}
    {L : Head.HL} (k : Head.layout (headShape P y) y.tauFC = .ok L)
    (hM : 24 ≤ v.MF ∧ v.MF ≤ 47 ∧ v.MF ≤ v.KF + 14) (hK : 17 ≤ v.KF ∧ v.KF ≤ 32)
    (he : 1 ≤ v.epsF ∧ v.epsF < 2 ^ 59) (h1 : v.theta ≤ v.C) (h2 : v.cap ≤ (headShape P y).T)
    (h3 : v.cap < 2 ^ 16) (h4 : v.C < 2 ^ 32) :
    Head.layout (headShape (scanTurn P vals v) (layTurn y v)) (layTurn y v).tauFC = .ok L := by
  rw [headShape_turn]
  exact LPFPol.layout_returns _ _ (headLayout_norm k hM hK he) h1 h2 h3 h4

/-! ### p15 · p16 -/

theorem pubOf_turn {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (k : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) (v : FreeLines) (sc' : Layer.Scales)
    (rope' : Array Nat) :
    Layer.Pub.of (layTurn y v) sc' rope' wsLay V tokv set = .ok (pubTurn L v sc' rope') := by
  unfold Layer.Pub.of at k ⊢
  obtain ⟨_, t, k⟩ := exc_bind k
  obtain ⟨rd, hr, k⟩ := exc_bind k
  obtain rfl := Except.ok.inj k
  refine (bind_ok t).trans ?_
  refine (bind_ok hr).trans ?_
  rfl

section
variable (L : Layer.Pub) (v : FreeLines) (sc : Layer.Scales) (rope : Array Nat)

theorem planG_turn (g : Nat) (O : Option Layer.HPlan2) :
    Layer.planG (pubTurn L v sc rope) g O = Layer.planG L g O := rfl

theorem plansFrom_turn : ∀ (n g : Nat) (O : Option Layer.HPlan2),
    Layer.plansFrom (pubTurn L v sc rope) n g O = Layer.plansFrom L n g O
  | 0, _, _ => rfl
  | n + 1, g, O => by
    simp only [Layer.plansFrom, planG_turn, plansFrom_turn n]

theorem plansG_turn : Layer.plansG (pubTurn L v sc rope) = Layer.plansG L := by
  unfold Layer.plansG
  rw [plansFrom_turn]
  try rfl

end

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.polLayout_turn
#print axioms HonestTraceRun.SetUp.tails_turn
#print axioms HonestTraceRun.SetUp.reads_turn
#print axioms HonestTraceRun.SetUp.widths_turn
#print axioms HonestTraceRun.SetUp.vocabulary_turn
#print axioms HonestTraceRun.SetUp.wsLay_turn
#print axioms HonestTraceRun.SetUp.planH2_turn
#print axioms HonestTraceRun.SetUp.headLayout_turn
#print axioms HonestTraceRun.SetUp.pubOf_turn
#print axioms HonestTraceRun.SetUp.plansG_turn
