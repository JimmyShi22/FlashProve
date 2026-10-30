-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/BackAtStand.lean: CONDITIONAL.

Not shown here. THAT THE FUNCTION WHICH MAKES THE BATCHED SUMCHECK's DATA RETURNS AND THAT ITS END
VALUES ARE THERE (data, ends): hypotheses here; Law/W/MakersReturn.lean has both at such a state,
from the public test k4Fits. CellsAre (Law/CellsAt.lean has it at a state, under K4CellsTieAt);
K4LookTieAt; K4Plan, WHOSE FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES
(at every other shape this statement says nothing); K4Ground (Johnson/Road/K4/W/KeptGround.lean has
it behind an accepting decision): hypotheses. That they can hold together: no example is known. THE
OWN CLAIMS BEHIND "back" (OwnBack) ARE NOT REACHED HERE. By a walk of import lines the closure holds
seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through
Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none
of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The right half behind the run "back", `OpenedRightBack` (Law/W/Halves.lean: the fields sideA,
sideB), at a state behind the member's step: one call of `right_back_led` (Law/W/BackOfLed.lean),
which has it from a return of the hearing. Its premises at such a state: the library's LedG on the
tape of the played rounds by `stand_led_tape` (Law/OwnAtStand.lean); what the tape has sampled by
`stand_drawn`; the reach by `stand_reach` (Law/PtsAtStand.lean); the structure that the forms read
by `env_is` (Law/ClaimsAre.lean) at `stand_hear` (Law/W/StandHear.lean); the three key values of the
look by K4LookTieAt; what the second token sumcheck has shown by `stand_terms_run`
(Law/SeenTerms.lean).

  `back_at`   OpenedRightBack at a state behind the member's step.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StandHear
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BackOfLed
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SeenTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road.K4 (entryTrue)
open OnBytes.Road.K4.W (K4Plan K4Ground)
open OnBytes.Road.K4.C (CellsAre)
open OnBytes.Desc.First.K4 (Par entries)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **OpenedRightBack AT A STATE BEHIND THE MEMBER's STEP.** CONDITIONAL: on every hypothesis
named. -/
theorem back_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    {h : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (AQ : K4Plan h pc Q.P Q.g tl D)
    {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    {pts : List (String × Array OnBytes.E)}
    (Gr : K4Ground h pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D) {Mm : Road.Mats Cb.Gl.E}
    (C : CellsAre Q (k4Wit Q cells weights tokens (look Q) m.st.input) Mm) {SD : StackData}
    {e : List OnBytes.E}
    (data : stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
      (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) = some SD)
    (ends : SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = some e)
    {Wd : World Cb.Gl.E} (hW : Wd.entry = entryTrue tl o Mm) :
    OpenedRightBack Wd Q o (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g)))) := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hD := stand_drawn hy (entries Q.P Q.hp Q.g)
  have hr := stand_reach Z
  have l4 : k4StartAt Q 4 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  obtain ⟨_, _, _, _, eg, ey⟩ := stand_led Z
  have hmats : matsOf Q = Road.matsR o.v.y o.v.g := by rw [ey, eg]; exact AQ.tails
  obtain ⟨Fh, hH⟩ := stand_hear Z
  have hh := k4_heard_front Z.seat hT
  have el := stand_look Z
  obtain ⟨g, _, h2, hzx, hzk, he⟩ := hLk
  rw [h2] at el
  obtain rfl := Option.some.inj el
  exact right_back_led Gr L hD l4 hh hzx he
    (env_is hH _ (by
      show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.zk = _
      rw [at_look _ _ ds hh]
      exact hzk))
    data ends hmats C
    (fun tT' a' h1 h3 => stand_terms_run Z hT tT' h1 G2 a' L.g2 h3) hW

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.back_at
