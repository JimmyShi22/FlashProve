-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackFin.lean: CONDITIONAL.

Not shown here. THE SIX TIES between what the honest side holds and what the verifier holds at the
batched sumcheck: the structure that the forms read (hv), the lookup's weights of the calls (he),
its token point (hzt), the two weights that join the passes (hom), the values that the second token
sumcheck has shown (one letter in hfin_of; hsh in hfin_hear), the list of the calls with terms in
that sumcheck (hTS in hfin_of; hPT in hfin_hear). Beside them, in hfin_hear: that the verifier's
text is called at the plan's layout and number of rounds (hPy, hlam). That the honest side's maker
and the verifier's text return. No example is known. No property is claimed.

THE VERIFIER's CALL OF stackEnd STANDS AT THE HONEST SIDE's PANELS, CHALLENGES' NUMBER AND WEIGHTS.
StackSides.lean and what stands over it ask (hfin) that stackEnd, at the panels SD.bl and the
weights SD.om which the honest side's maker has laid, returns what the verifier holds. The verifier
makes its own panels (panelsT over panelsA, placed) at its own environment. Here: the two lists of
panels are one where the environments' five fields and the list of calls are, and so the verifier's
call is the call that hfin asks.

  hfin_of        hfin, from the verifier's panels and its call of stackEnd written out.
  hfin_hear      hfin at some shown values, from a return of the verifier's text hearStack (by the
                 library's hearStack_public, OnBytes/Desc/First/K4/StackPublic.lean).
-/
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.CornerKit
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Pub Heard HeardStack Panels StackEnd stackEnd panelsA panelsT
  placePanels stubO callsTS nEndT)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.K4 (engFl)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts StackData envOf ztOf stackData)

/-- **hfin, from the verifier's panels and its call of stackEnd written out.** v, e', zt', TS',
pans': the verifier's; shownT: what both sides hold as the values that the second token sumcheck has
shown. -/
theorem hfin_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (hD : stackData Q w p shownT = some SD) {v : Env} (hv : envOf Q p = some v) {e' zt' : Array E}
    (he : p.fo.e = e') (hzt : ztOf Q p = zt') {TS' : List ℕ} (hTS : callsTS Q.P = some TS')
    {pans' : Panels}
    (hp : panelsT { v := v, e := e', shownT := shownT, zt := zt', stubO := stubO Q.P.y } TS'
      (panelsA { v := v, e := e', shownT := shownT, zt := zt', stubO := stubO Q.P.y } {}) =
      some pans')
    {om : Array E} (hom : p.om = om) {rs H1 V : Array E} {a b : E} {fin : StackEnd}
    (hfin : stackEnd Q.P.y (placePanels pans'.bl).1 rs Q.hp.lamS om H1 V a b = some fin) :
    stackEnd SD.S.v.y SD.bl rs SD.S.Q.hp.lamS SD.om H1 V a b = some fin := by
  obtain ⟨hS, -, eom⟩ := stack_open hD
  obtain ⟨eQ, -, efo, hv0, -, hTS0, ezt⟩ := sides_fields hS
  obtain ⟨pans, hpn, hbl, -⟩ := stack_panels_at hD
  have ev : SD.S.v = v := Option.some.inj (hv0.symm.trans hv)
  have ey : v.y = Q.P.y := envOf_y hv
  have eT : SD.S.TS = TS' := Option.some.inj (hTS0.symm.trans hTS)
  have eE : sidesEnv SD.S shownT =
      { v := v, e := e', shownT := shownT, zt := zt', stubO := stubO Q.P.y } := by
    unfold sidesEnv
    rw [ev, efo, he, ezt, hzt, ey]
  rw [eE, eT, hp] at hpn
  obtain rfl := Option.some.inj hpn
  rw [hbl, ev, ey, eQ, eom, hom]
  exact hfin

/-- **hfin at some shown values, from a return of the verifier's text.** P': the public numbers at
which the verifier's text is called. hsh: the run of values that the ledger F shows under the second
token sumcheck's end values is shownT. -/
theorem hfin_hear {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (hD : stackData Q w p shownT = some SD) {P' : Pub} {v : Env} {H : Heard} {lamS NCLp : ℕ}
    {F G : Fork} {t u : Tape} {K : HeardStack}
    (hH : OnBytes.Desc.First.K4.hearStack engFl P' v H lamS NCLp F t = some (K, G, u))
    (hPy : P'.y = Q.P.y) (hPT : callsTS P' = callsTS Q.P) (hv : envOf Q p = some v)
    (he : p.fo.e = H.fo.e) (hzt : ztOf Q p = H.ztF) (hlam : lamS = Q.hp.lamS)
    (hom : p.om = powers (OnBytes.Desc.First.P1.tapeEps t) 2)
    (hsh : ∀ tT a, H.tT = some tT →
      ((Array.range (nEndT P'.y)).mapM fun i => F.shown (tT.sEnd + i)) = some a → a = shownT) :
    ∃ (H1 V : Array E) (a b : E),
      stackEnd SD.S.v.y SD.bl K.rs SD.S.Q.hp.lamS SD.om H1 V a b = some K.fin := by
  obtain ⟨tT, sh, TS, pans, Fe, H1, V, shA, shB, C, Fk, tk, -, hT, hs, hTS, hp, -, -, -, -, -, -, -,
    -, -, -, -, hfin⟩ := OnBytes.Desc.First.K4.hearStack_public hH
  obtain rfl := hsh tT sh hT hs
  rw [hPy] at hp hfin
  rw [hPT] at hTS
  rw [hlam] at hfin
  exact ⟨H1, V, shA, shB, hfin_of hD hv he hzt hTS hp hom hfin⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.hfin_of
#print axioms OnBytes.Road.K4.C.hfin_hear
