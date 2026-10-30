-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadReturnsOf.lean: the kind "lookup" (K3): the field
headReturns of `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean), which says "at the digits of the
head's link the step without a round behind the lookup returns", reduced to what it asks of other
kinds. The thread is a variable. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the step without a round is `quietHead`
(Johnson/Desc/First/Look/K3Whole.lean).

What is shown.
  `quietHead_returns`: the six facts below give the step's return, and say what it lays. This is the
    converse of `quietHead_whole` (Honest/K3/Law/Thread/QuietHeadWhole.lean).
  `covered_put`: the covered positions read nothing of the open link's part.
  `headReturns_of_thr`: the field, to the letter, from `hHead`, `hN` and `hRest`.
The step `quietHead` makes six tests. Each is covered by one of the three hypotheses:
  1 the head's link is open: `hHead`, from the thread in front.
  2 the covered positions are made: `hRest`, which is assumed and not shown in this file; see below.
  3 what the head's own rounds heard is laid: `hHead`.
  4 the head's tables are laid: `hHead`.
  5 the claim on the weights is made: `hRest`, which is assumed and not shown in this file; see
    below.
  6 the plan has one claim on the weights: `hN`, a test with code on public data.

Hypotheses that remain, in `headReturns_of_thr`.
  `hHead`: an implication from the thread in front: the state stands in the head's link, which
    is open, and what the head heard and the head's tables are laid. Whoever gives the thread's form
    and rider shows it.
  `hN`: the plan has one claim on the weights.
  `hRest`: it too is stated under the thread in front. It holds two returns.
    The covered positions read the request's words (as many as the plan says and two; every token an
      entry of the vocabulary; the two numbers of the request's range in order) and the reply that
      was heard (it is heard; it is an entry of the vocabulary): not the reply that the instance
      asks about.
    The claim on the weights (`weightsClaim`, Johnson/Desc/First/Look/LookQuiet.lean) refuses at
      five points: four on the public layout (the call "HD0"; its segment "HD0"; the last unit of
      the weights' layout is of the sort 13; each group of that unit is named "x" or "kk") and one
      on what the head heard: at every covered position the checked token is an entry of the
      vocabulary.

In `quietHead_returns`: `hh`, `ho`: the state stands in the head's link, which is opened; `hx`,
`ht`: what the head heard and the head's tables are laid; `hc`, `hw`: the covered positions and the
claim on the weights return; `hn`: one claim on the weights.

Users. `headReturns_of_thr` is called in Honest/K3/Law/Thread/RidersAtSite.lean and
Honest/K3/Law/Thread/RidersAtHeadSite.lean; `quietHead_returns` in
Honest/K3/Law/Thread/CarriesHeadDigits.lean. Honest/K3/Law/Thread/HeadReturnsVals.lean calls
`headReturns_of_thr` too.

Limits. On the verifier's side alone. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtThreadSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietHeadWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf quietHead seatDigits)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (weightsClaim)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The six facts give the step's return.** -/
theorem quietHead_returns (X : OnBytes.Model.Verify.Public) (u : FS)
    {a : VerifiableInference.Desc.First.HeadOwn} {cov : OnBytes.Model.Head.Covered}
    {x : OnBytes.Model.Head.Heard} {tt : OnBytes.Model.Head.Tables}
    {claim : OnBytes.Model.WsClaim} (hh : u.here = .head a) (ho : a.opened = true)
    (hc : u.covered X.T X.P.h.V = .ok cov) (hx : a.x = some x) (ht : a.t = some tt)
    (hw : weightsClaim
      { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
        x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 } X.layers.wsLay = .ok claim)
    (hn : (X.H.NCL == 1) = true) :
    quietHead X u = .ok { u with here := .head { a with claim := some claim } } := by
  unfold quietHead
  rw [hh]
  simp only [need, named, ho, hc, hx, ht, hw, hn, if_true, bind, Except.bind, pure, Except.pure]

/-- **The covered positions read nothing of the open link's part.** -/
theorem covered_put (s : FS) (h' : VerifiableInference.Desc.First.Here) (T V : Nat) :
    ({ s with here := h' } : FS).covered T V = s.covered T V := rfl

variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- **The field headReturns, from the thread in front, one public test, and two returns that are for
the files of other kinds to show.** No instance of these hypotheses is exhibited in this file. -/
theorem headReturns_of_thr (b : Nat) (Z : Pub) (s : Site)
    (hHead : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      ∃ a, st.here = .head a ∧ a.opened = true ∧ a.x.isSome = true ∧ a.t.isSome = true)
    (hN : (Z.p.X.H.NCL == 1) = true)
    (hRest : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env) a x tt, Thr T b k st m E →
      st.here = .head a → a.x = some x → a.t = some tt →
      ∃ cov claim, st.covered Z.p.X.T Z.p.X.P.h.V = .ok cov ∧ weightsClaim
        { h := Z.p.X.hS, L := Z.p.X.HLy, b := OnBytes.Model.Verify.borderOf Z.p.X.y,
          hp := Z.p.X.H, cov := cov, x := x, t := tt,
          iU3 := (Z.p.X.H.tl.ix.U.getD 2 none).getD 0 } Z.p.X.layers.wsLay = .ok claim) :
    s.digits = true → s.caller = .head → ∀ (k : Coins Bk) (st : FS) (m : Mid W X)
    (E : Env) (F : Fork) (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (s' : FS), Thr T b k st m E →
    (seatOf K3Lot.ofForm s.digits).fork st = some F → rs.length = (s.p.entries.getD []).length →
    hearV (faceOf s.shape) F rs = some (g, G) →
    decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' →
    ∃ t, HeadBehind Z.p.X s' t := by
  intro hd _ k st m E F rs g G s' hT _ _ _ hdv
  obtain ⟨a, ha, ho, hx, ht⟩ := hHead k st m E hT
  obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 hx
  obtain ⟨tt, ht'⟩ := Option.isSome_iff_exists.1 ht
  obtain ⟨cov, claim, hcov, hw⟩ := hRest k st m E a x tt hT ha hx' ht'
  rw [hd] at hdv
  obtain ⟨F₁, H, G₁, a1, _, _, _, _, e⟩ :=
    decideVia_whole (seatDigits K3Lot.ofForm) s.p st s' rs hdv
  have a1' : st.fork? = some F₁ := a1
  obtain ⟨tl, htl⟩ := tl_of_fork st a1'
  rw [digits_put K3Lot.ofForm st htl a1' H G₁] at e
  simp only [S.putTl, S.putFork, ha, ho, if_true] at e
  refine ⟨_, quietHead_returns Z.p.X s' (a := _) (by rw [e]) ?_ ?_ ?_ ?_ hw hN⟩
  · rfl
  · rw [e]
    exact hcov
  · exact hx'
  · exact ht'

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.quietHead_returns
#print axioms ProofFile.Honest.K3.Law.AtThr.covered_put
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_of_thr
