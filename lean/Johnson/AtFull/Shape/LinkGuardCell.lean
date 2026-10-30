-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkGuardCell.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: WHAT
THE GUARDED STEP OF SwitchReturns.lean (switch_att_both, switch_lay_both) DOES AT A STATE THAT IS
REACHED THERE, WHOEVER PLAYS, UNDER THE HEAD P5J.AtMgA ALONE: its test on values accepts; and where
the seated member says yes from such a state s to t, the guarded step returns the shape and the
makes of t at those of s. A joining of laws; nothing is evaluated here.

Why. With the guard linkGd in front, SwitchReturns.lean has Carries only where the guarded step
returns. LinkGuardHead.lean has the guard at every reached state; SwitchAtHead.lean has the step
behind the guard from a yes (switch_att_at, switch_lay_at). Here the two are joined.

  **switchW_under_head**: k ≤ 353, s reached at the border k: switchW s = true: ONE LINE OVER THE
    LIBRARY's onesV_true_reached (Johnson/AtFull/Shape/SwitchOnesPlain.lean), at the walk's own copy
    of the frame: nothing new to the library but the letters. (linkB_reached, LinkGuardReached.lean,
    proves the same anew at the 23 borders, beside linkB.)
  guarded_ok: a guarded step returns what the step behind the guard returns, where the guard
    accepts.
  **switch_att_cell** (12), **switch_lay_cell** (11): 1 ≤ l < 24: every letter tied as in
    switch_att_both | switch_lay_both; the member b by its number 14 l + 0 + 2 in cF.blocksInOrder: for every
    s reached at 14 l + 2 and every yes of b from s to t: that theorem's own guarded step returns
    shA t at shA s.

Limits. FROM A YES, AT A REACHED STATE: that anything is reached, or that the member says yes, is
not said. "Reached" is over the list of the wrapped sub-protocols (cF.blocksInOrder.map below), from
ProofFile.startS Zp, at ft = 0. NO TABLE IS NAMED: that the table of steps (Tab.switch, TableOfSteps.lean)
lays this very step at 14 l + 2 is stated by no law here. The two top laws speak of the links'
places alone: nothing at 339 or 353. The full size alone: beneath the guard stand closed tests at
written values that Lean's kernel has evaluated (LinkGuardWhole.lean's Limits). It stands over the
another house's files (Johnson/Desc/K2/Honest/Returns/). That the head has a member is shown in
scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean);
that these three hold together, at two named sets of public files, in a side library. At the
format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkGuardHead
import Johnson.AtFull.Shape.SwitchOnesPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (HeadPar)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K2.Honest.Returns
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (subAt k2P)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {z : ProofFile.InstPub}

/-- **THE SWITCH's TEST ON VALUES ACCEPTS AT EVERY STATE REACHED AT A BORDER UP TO THE LAST CODE
SWITCH, UNDER THE HEAD ALONE**: the library's onesV_true_reached at the walk's own copy of the
frame. -/
theorem switchW_under_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {k : Nat} (hk : k ≤ 353)
    {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (z, s)) : switchW s = true :=
  onesV_true_reached h hk hr _ List.mem_cons_self

/-- Where the guard accepts, the guarded step returns what the step behind it returns. -/
theorem guarded_ok {g : ShA → Bool} {f : ShA → Option ShA} {a b : ShA} (hg : g a = true)
    (hf : f a = some b) : optE (fun y => if g y then f y else none) a = .ok b :=
  optE_ok.2 (by rw [if_pos hg]; exact hf)

/-- **AN ATTENTION LINK's SWITCH: FROM A YES AT A REACHED STATE THE GUARDED STEP RETURNS.** -/
theorem switch_att_cell (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .attention) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (p : Attention.Plan) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.A[Y.g]? = some p ∧ cF.blocksInOrder[14 * l + 0 + 2]? = some b ∧
      ∀ (z : ProofFile.InstPub) (s : S) rs gs t,
        Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * l + 2) (z, s) →
        b.decide s rs gs = .ok t →
        optE (fun y =>
          if linkGd (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openAttG (attPar Y p l)))
          else none) (shA s) = .ok (shA t) := by
  obtain ⟨Bs, P, n, HP, Y, p, Lk, b, a1, a2, a3, a4, a5, a6, -, a8, hc⟩ :=
    switch_att_at h l h1 h24 hs
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  refine ⟨Bs, P, n, HP, Y, p, b, a1, a2, a3, a4, a5, a6, a8, fun z s rs gs t hr hd => ?_⟩
  exact guarded_ok (linkGd_at_base h a1 (by omega) a2 a3 hr _ _) (hc s rs gs t hd)

/-- **A LAYERS' LINK's SWITCH BEHIND LINK 0: THE LIKE.** -/
theorem switch_lay_cell (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .layers) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (hp : Layer.HPlan2) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.G[Y.g]? = some hp ∧ cF.blocksInOrder[14 * l + 0 + 2]? = some b ∧
      ∀ (z : ProofFile.InstPub) (s : S) rs gs t,
        Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * l + 2) (z, s) →
        b.decide s rs gs = .ok t →
        optE (fun y =>
          if linkGd (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openLayG (layPar Zp.p.X Y hp l)))
          else none) (shA s) = .ok (shA t) := by
  obtain ⟨Bs, P, n, HP, Y, hp, Lk, b, a1, a2, a3, a4, a5, a6, -, a8, hc⟩ :=
    switch_lay_at h l h1 h24 hs
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  refine ⟨Bs, P, n, HP, Y, hp, b, a1, a2, a3, a4, a5, a6, a8, fun z s rs gs t hr hd => ?_⟩
  exact guarded_ok (linkGd_at_base h a1 (by omega) a2 a3 hr _ _) (hc s rs gs t hd)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.switchW_under_head
#print axioms Johnson.AtFull.Shape.guarded_ok
#print axioms Johnson.AtFull.Shape.switch_att_cell
#print axioms Johnson.AtFull.Shape.switch_lay_cell
