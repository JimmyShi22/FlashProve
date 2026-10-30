-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PromiseAt.lean: THE TABLE's PROMISE BEHIND K10's WRITING, AT THE k-TH
PLACE OF A LIST OF PLACES, IN THE WORDS IN WHICH THE TABLE's OWN PROMISE AT A BORDER IS WRITTEN. One
statement and its proof. A file BESIDE the table of joints: it turns nothing of it.

  `k10_promise_at`: ps a list of places at which the two tests on the table say yes (`closersFit`,
    PromiseBehind.lean; `closersNext`, ShapeBehind.lean: both beside this file); ps[k]? = some p of
    the kind K10. From `onAt` at ps[k]? and the k-th open set (`openSets links ps (start links)`),
    at a; a yes of `closeFrame` at what K10 reads of a's record: `onAt` at ps[k + 1]? and the (k +
    1)-th open set, at K10's writing. These are the two sides of `onQ k` and `onQ (k + 1)`
    (Johnson/Desc/Sound/BordersQ.lean), unfolded, with the open public items Q, Q' as letters.
Limits. PREMISES STILL: "what is kept lies in its group" at the place's segment; the plan's numbers
of trees and of messages are the same at the two places; AND THE SIX SENTENCES ON THE MEANING's
LETTERS of `k10_promise_behind` (ShapeBehind.lean). `onQ` is not named in code here:
that the two sides are its unfolding is held by reading. It speaks of K10's writing, not of the
seated block or its piece. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.ShapeBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

open VerifiableInference.Desc.K9 (recOf putRec)

theorem k10_promise_at {P W : Type} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (k : Nat) (p : Place) (hF : closersFit links ps (start links) = true)
    (hX : closersNext links ps = true) (hk : ps[k]? = some p) (hK : p.kind = .K10)
    (hKept : ∀ t ∈ N.keptOf (p.link.getD 0), t ∈ N.group (p.link.getD 0))
    (ht : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hm : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (Q Q' : List Pub) (a : P × S) (z' : P) (y y' : Strs)
    (es : List Fmt.Entry) (rs : List Fmt.RoundView) (x : OnBytes.ReqFrame × OnBytes.Statement)
    (hx : Close.closeFrame (recOf a.2).owed (recOf a.2).frame (recOf a.2).st es rs = .ok x)
    (ha : onAt N Mg links ps[k]? ((openSets links ps (start links))[k]?.getD []) Q a y)
    (hDec : Mg.decodes a y → Mg.decodes (z', putRec a.2 ⟨none, x.1, x.2⟩) y')
    (hIn : a.2.failed = none → Mg.inOrder a = true →
      Mg.inOrder (z', putRec a.2 ⟨none, x.1, x.2⟩) = true)
    (hPub : a.2.failed = none →
      pubHeld Mg ((openSets links ps (start links))[k]?.getD []) Q a = true →
      pubHeld Mg ((openSets links ps (start links))[k + 1]?.getD []) Q'
        (z', putRec a.2 ⟨none, x.1, x.2⟩) = true)
    (hPP : a.2.failed = none → (∀ q ∈ Q, Mg.pubP q a) →
      ∀ q ∈ Q', Mg.pubP q (z', putRec a.2 ⟨none, x.1, x.2⟩))
    (hHeld : a.2.failed = none →
      ∀ t ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.held t.1 t.2 a = true → Mg.held t.1 t.2 (z', putRec a.2 ⟨none, x.1, x.2⟩) = true)
    (hSN : a.2.failed = none →
      ∀ t ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.shown t.1 t.2 y ∧ Mg.noColl t.1 t.2 a y →
          Mg.shown t.1 t.2 y' ∧ Mg.noColl t.1 t.2 (z', putRec a.2 ⟨none, x.1, x.2⟩) y') :
    onAt N Mg links ps[k + 1]? ((openSets links ps (start links))[k + 1]?.getD []) Q'
      (z', putRec a.2 ⟨none, x.1, x.2⟩) y' := by
  obtain ⟨Ok, e1, e2, e3, e4, e5⟩ := closersFit_at links ps _ k p hF hk hK
  obtain ⟨p', f1, f2, f3⟩ := closersNext_at links ps k p hX hk hK
  rw [e1, Option.getD_some] at ha hPub hHeld hSN
  rw [e2, Option.getD_some] at hPub ⊢
  rw [hk] at ha ht hm
  rw [f1] at ht hm ⊢
  exact k10_promise_behind N Mg links p p' Ok Q Q' a z' y y' es rs x hx e5
    (sampled_step_close N Ok _ _ e3 e4 hKept) f2 f3 ht hm ha hDec hIn hPub hPP hHeld hSN

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.k10_promise_at
