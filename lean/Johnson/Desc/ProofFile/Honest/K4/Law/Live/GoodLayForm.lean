-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/GoodLayForm.lean: CONDITIONAL.

What is here. TWO HYPOTHESES THAT THE WRITERS OF THE SUB-PROTOCOL K9 ASK OF K4, EACH TO ITS LETTER.
Their `goodLayers_of_clauses` (Honest/K9/GoodLayPaid.lean; not imported here) says when a state in
front of the batching of a feed-forward segment is "good". Among its hypotheses are two on the
claims of K4 (the sub-protocol of the feed-forward layers' own rounds): live4 (at every slot of a
set W4 some claim of K4's two lists that has no `eqFirst` names the slot with a coefficient whose
words lie below the prime and are not all 0: `liveAt`, Johnson/Desc/K9/Honest/SlotsLive.lean) and
un4 (no claim of these lists names the merge's slot, where that lies below a number n: `unnamedAt`,
there). `k4_live4_form` ENDS IN live4's TEXT, sign for sign, with the set `k4W4 a.F.next fo a₀` in
the place of W4; `k4_un4_form` ENDS IN un4's TEXT, sign for sign. BOTH ARE EXCHANGED, NOT PAID: each
stands under every hypothesis of the laws that it calls, none lighter, and under one more. The
proofs are calls: `k4_live_of_yes_words` (Law/Live/TapeOfWords.lean: K4's own stretch of slots, and
the slots that the end of the key side of the lookup on the calls names), `k4_planes_of_yes`,
`k4_unnamed_of_yes` and `mergeOf_lay_eq` (Law/Live/AtYes.lean), each at `!p4.k3Runs`, `p4.P` and
`a₀.F`, which the field front of the structure `Heard4` (Honest/K9/LayersFree.lean) names.

  `k4W4`   a set of slots: K4's own stretch; the slots that the end of the lookup's key side names;
      those that its leaves' row names whatever is kept that has no coefficient there; the slot of
      its bits' value.
  `k4_live4_form`   **live4 of `goodLayers_of_clauses`, to its letter, at the set `k4W4`: not at the
      calls' two further windows as windows.**
  `k4_un4_form`   **un4 of `goodLayers_of_clauses`, to its letter.**

Not shown here. THE CARRIAGE (hcar): that what the state in front of the batching holds as K4's own
is what K4's step left. The laws called speak at a yes of K4's own block, at the state s₀ in front
of K4's member; the two hypotheses speak at a later state's part a₀. hcar is typed in no file of
K4's writers; the writers of K9 say that their `k4_front_handed` (Honest/K9/LayFrontHanded.lean)
gives it at a walk's returned state: their word; not read here. THE SET: `k4W4` READS TWO VALUES OFF
THE EARLIER STATE (its ledger's next slot; what it holds as heard by the lookup on the calls) and
a₀'s own. THAT THE HYPOTHESIS cover OF `goodLayers_of_clauses` HOLDS WITH THIS SET IS NOT SHOWN
HERE; the writers of K9 say that their `cover_k4W4` (Honest/K9/CoverLay.lean) has it, under premises
of its own: their word; not read here. THE SET DOES NOT HOLD THE CALLS' WINDOWS OF "planes" AND
"join" AS WINDOWS: it holds the slots that the end of the lookup's key side and the row of its
leaves name with a coefficient other than 0, and the slot of its bits' value. That these windows lie
in it would be for the laws of the writers of the sub-protocol K3 (lookups) on these forms' words,
under their clause, with two things more: the earlier state's fo is what a₀ holds as heard (A SECOND
CARRIAGE), and the earlier ledger's next slot is the end of the calls' stretch. ALL OF THAT STANDS
IN cover NOW, NOT IN live4. WHERE `Heard4` FAILS BOTH ENDS HOLD IDLY, and `Heard4` is shown of no
state. THE HYPOTHESES THAT STAY: of `k4_live4_form` sixteen: h (K4's yes), eP, ehp, eg, hrf, hw, hM
and hC (the wider mark and K4's fall are silent), ha, hfo, hF, hfree, N, hll, hLam and hcar; of
`k4_un4_form` nine: h, ha, hfo, hF, hfree, N, hlv, hs (the later state stands at a₀) and hcar. hC
follows from h (`k4_coin_of_yes`, Law/Live/CoinOfYes.lean; not called here): THE EVENT OF hC IS NOT
SAVED BY THAT: IT STANDS INSIDE h. What each is: the heads of Law/Live/TapeOfWords.lean and
Law/Live/AtYes.lean. Three have givers that are not called here: hrf (`k4_hrf_of_step`,
Law/Live/NzOfStep.lean), hll and hLam at the full size (`llLam_of_scan`, Law/Live/AtFull.lean; at
`Bs.G₀.W.layers`, under the library's `P5J.AtMgA` and a return of `baseOf`: `llLam_at_base`,
Law/Live/AtBase.lean). Two hypotheses that the called laws take behind their "for all" are met here:
that the public data's layout is K4's (at `p4.P`: by rfl) and that `frontForms` returns (`Heard4`'s
field front). This file gives no example of the hypotheses together; none is known. THE CALL OF
`goodLayers_of_clauses`
ITSELF IS NOT MADE HERE (Law/Live/GoodLayFormFits.lean holds two laws in its stead; K9
calls them in its `k4_texts_handed`, Honest/K9/K4TextsHanded.lean; no part of the
library). A NAME: `plainOf` is written bare in both ends; the frame's Honest/Strat.lean declares
`ProofFile.Honest.plainOf`, another thing; it does not lie beneath this file; with it beneath, by Lean's
rule for names as we read it (an enclosing namespace goes before an opened name; at `plainOf` not
tried), Lean would take that one and refuse the text: loudly, never silently.

A LAW, NOT A PART: its imports reach modules under Johnson/Bridge/ (through
Johnson/Desc/Ok/FormRules.lean): no file that defines a part of the description may import it.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.TapeOfWords
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.AtYes
import Johnson.Desc.ProofFile.Honest.K9.LayersFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4 (Par blockAtS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (roundsFit noDigest fieldPrimeWord)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Honest (layersBack plainOf)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt unnamedAt)
open ProofFile.Honest.K9 (Heard4)

/-- **K4's set of slots**, said of a number k, of what a lookup has heard and of a state's part:
the slots from k on below the slot of the merge's end value, as the part's own has it; the slots
that the end of the lookup's key side names with a coefficient that is not 0; the slots that the row
of the lookup's leaves names whatever is kept that has no coefficient there; the slot of its bits'
value. -/
def k4W4 (k : Nat) (fo : Forest.Heard) (a₀ : LayOwn) (j : Nat) : Prop :=
  (∃ o, a₀.own = some o ∧ k ≤ j ∧ j < o.wo.sFv) ∨ cf Reading.gl fo.cEnd j ≠ 0 ∨
    (∀ kept, cf Reading.gl kept j = 0 → cf Reading.gl (fo.leaves.rowForm oneE kept) j ≠ 0) ∨
    j = fo.sBit

/-- CONDITIONAL on every hypothesis. **live4 of `goodLayers_of_clauses`, to its letter**, at the set
`k4W4` of the earlier ledger's next slot, of what the earlier state holds as heard, and of a₀. -/
theorem k4_live4_form {p4 : Par} {s₀ s₁ : S} {mine : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))}
    (h : (blockAtS p4).decide s₀ (mine.map noDigest) cols = .ok s₁)
    (Qk : K4Pub) (eP : Qk.P = p4.P) (ehp : Qk.hp = p4.hp) (eg : Qk.g = p4.g)
    (hrf : roundsFit ((OnBytes.Desc.First.K4.entries Qk.P Qk.hp Qk.g).map fun e => { entry := e })
      mine = true)
    (hw : ∀ r ∈ mine, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    {fr : List Fmt.Drawn} (hM : (k4MarkWide Qk).test fr (mine.map (·.drawn)) = none)
    (hC : k4CoinZero Qk (mine.map (·.drawn)) = none)
    {a : LayOwn} {fo : Forest.Heard} (ha : s₀.here = .lay a) (hfo : a.fo = some fo)
    (hF : Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (N : _root_.Fo.Tp.PadNames fo a.F) (hll : p4.P.y.h.ll - 1 = 1) (hLam : p4.P.y.LamM ≤ 2)
    (a₀ : LayOwn) (hcar : ∀ a₁, s₁.here = .lay a₁ → a₀.own = a₁.own) :
    ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, k4W4 a.F.next fo a₀ j →
      liveAt (plainOf lf ++ layersBack o) j = true := by
  obtain ⟨o₁, G, hs₁, H⟩ :=
    k4_live_of_yes_words h Qk eP ehp eg hrf hw hM hC ha hfo hF hfree N hll hLam
  obtain ⟨o₂, G₂, hs₂, H₂⟩ := k4_planes_of_yes h ha hfo
  have hown₁ : a₀.own = some o₁ := by
    have e : s₁.here = .lay { a with F := G, own := some o₁ } := by rw [hs₁]
    exact hcar _ e
  have hown₂ : a₀.own = some o₂ := by
    have e : s₁.here = .lay { a with F := G₂, own := some o₂ } := by rw [hs₂]
    exact hcar _ e
  intro gC gD o lf hh j hj
  have e₁ : o = o₁ := Option.some.inj (hh.own.symm.trans hown₁)
  have e₂ : o = o₂ := Option.some.inj (hh.own.symm.trans hown₂)
  subst e₁
  subst e₂
  obtain ⟨hA, hB, _⟩ := H (!p4.k3Runs) p4.P a₀.F lf rfl hh.front
  rcases hj with ⟨o', ho', hk, hlt⟩ | hj | hj
  · have e₃ : o' = o := Option.some.inj (ho'.symm.trans hh.own)
    subst e₃
    exact hA j hk hlt
  · exact hB j hj
  · exact H₂ (!p4.k3Runs) p4.P a₀.F lf hh.front j hj

/-- CONDITIONAL on every hypothesis. **un4 of `goodLayers_of_clauses`, to its letter.** -/
theorem k4_un4_form {p4 : Par} {s₀ s₁ : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p4).decide s₀ rs cols = .ok s₁)
    {a : LayOwn} {fo : Forest.Heard} (ha : s₀.here = .lay a) (hfo : a.fo = some fo)
    (hF : Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (N : _root_.Fo.Tp.PadNames fo a.F)
    (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ a.F.next)
    (s : S) (a₀ : LayOwn) (n : Nat) (hs : s.here = .lay a₀)
    (hcar : ∀ a₁, s₁.here = .lay a₁ → a₀.own = a₁.own) :
    ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf lf ++ layersBack o) j = true := by
  obtain ⟨o₁, G, hs₁, H⟩ := k4_unnamed_of_yes h ha hfo hF hfree N hlv
  have hown : a₀.own = some o₁ := by
    have e : s₁.here = .lay { a with F := G, own := some o₁ } := by rw [hs₁]
    exact hcar _ e
  intro gC gD o lf hh j _ hm
  have e₁ : o = o₁ := Option.some.inj (hh.own.symm.trans hown)
  subst e₁
  have e₂ : j = o.wo.sFv := mergeOf_lay_eq hs hh.own hm
  subst e₂
  exact H (!p4.k3Runs) p4.P a₀.F lf rfl hh.front

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.k4W4
#print axioms ProofFile.Honest.K4.Live.k4_live4_form
#print axioms ProofFile.Honest.K4.Live.k4_un4_form
