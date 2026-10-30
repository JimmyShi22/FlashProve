-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/OpeningAtHead.lean: THE FIRST SEGMENT's OPENING, WHOLE, AT ITS SEAT IN THE
PROOF FILE's OWN FIRST CHAIN (member 2 of the flat list: link 0's first place): the member has one
step on the chain's shape, with both laws at the seated block's own decision. Under the head
P5J.AtMgA; a joining of laws; nothing is evaluated.
  1 `first_keeps`: the opening's yes leaves the mark of failure and what goes out.
  2 `openingGS P g₂`: the step at the seat: no mark; then the opening's own step openG
    (Johnson/Desc/First/Shape/Opening.lean); then g₂, the step of the frame's "opened".
  `row_zero`: which row of the frame stands at link 0: with X the link's record as built, hp the
    layers' plan of its group, and P the row's letters made of these: the row's "opened" is
    openLayZero P fvs kCol (fvs, kCol: off the public part), and its own test on the plan is paid.
  **`opening_at`**: with Bs what the maker's own ProofFile.baseOf returns at the public part, and X, hp, P
    as in row_zero: the member b at number 2 of cF.blocksInOrder is such that, at the step openingGS
    (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (openZeroG P fvs kCol): where b says yes and the
    step returns, it returns the shape behind; and where the step returns, b says yes on two rounds
    in which no seed's factor is 0 and round 2 holds as many answers as the place counts. THE STEP
    IS NAMED: a function of the public part alone.
By IM.k1_first_sits (Johnson/IMR/FirstSeats.lean: the seat holds K1's own block with the row's
"opened" joined), joined_iff (OpenedAtHead.lean: the seated decision, half by half, both ways),
open_carries | open_returns (Opening.lean), openZero_carries | openZero_returns
(Johnson/Desc/First/Walk/Shape/FrameEnds.lean), framesOf_arms (Johnson/Top/H0/Walk/FrameRows.lean),
IM.hear_at_flat and IM.flatIx_scope (the number in the flat list); in row_zero besides:
P1L20.plans_hold (Johnson/P1L20R/FrameSits.lean), plans_at (PlansAtHead.lean), sub_kind
(OpenedAtHead.lean).
Limits. The two premises on the rounds stand as in Sending.lean. THE STATEMENT HANDS OUT NO
b.rounds, though "returns" speaks at two rounds: OpeningFrame.lean's opening_more_at has them. The
converse of "returns" fails by the sending's tests on the plan alone (Opening.lean). UNDER THE HEAD:
that it has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). NO STATE IS SHOWN AT WHICH THE STEP
RETURNS. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.OpenedAtHead
import Johnson.Desc.First.Shape.Opening

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame framesOf_arms fvsOf pubOf)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)

/-! ## 1 What the opening leaves -/

/-- The opening's yes leaves the mark of failure and what goes out. -/
theorem first_keeps (q : Params.First) (gp : _root_.Desc.Plain.GPar) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K1.firstSegmentOpening (Cl := Unit) q gp).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out := by
  unfold VerifiableInference.Desc.K1.firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain ⟨⟨c, d⟩, -, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact ⟨rfl, rfl⟩

/-! ## 2 The member at link 0's first place -/

/-- **The step at the seat**: no mark; the opening (openG, Johnson/Desc/First/Shape/Opening.lean);
then the step g₂ of the frame's "opened". -/
def openingGS (P : VerifiableInference.Desc.K1.Par) (g₂ : ChainSh → Except String ChainSh)
    (a : ChainSh) : Option ChainSh :=
  if a.marked then none else (openG P a).bind fun m => (g₂ m).toOption

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The frame's row at link 0: which text its "opened" is, with the row's own test on the plan. -/
theorem row_zero (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {fs : List LinkFrame}
    (hfs : framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs) {f : LinkFrame}
    (hf : fs[0]? = some f) :
    ∃ X hp P, Zp.p.built.links[0]? = some X ∧ X.kind = 0 ∧ Zp.p.X.G[X.g]? = some hp ∧
      P = ⟨pubOf X, 0, Zp.p.X.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ ∧
      planLayZero Zp.first.shape P = true ∧
      f.opened = openLayZero P (fvsOf Zp.p.built.links) Zp.first.lin.kCol := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := P1L20.plans_hold h.scope h.reads O (plans_at h) hfs (by omega : 0 < 25) hf
  rcases framesOf_arms hfs hf with ⟨Y, hY, hk, -⟩ | ⟨-, Y, p, P, a1, a2, a3, a4, e1, e2, -⟩ |
    ⟨n, -⟩ | ⟨n, -⟩
  · exfalso
    have e := sub_kind h (by omega : 0 < 25) hY
    rw [hk] at e
    exact nomatch e
  · rw [e1] at hp
    exact ⟨Y, p, P, a1, a2, a3, a4, hp, e2⟩
  · exact absurd rfl n
  · exact absurd rfl n

theorem opening_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (b : Block S ProofFile.Cl), ∃ X hp P,
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Zp.p.built.links[0]? = some X ∧ Zp.p.X.G[X.g]? = some hp ∧
      P = ⟨pubOf X, 0, Zp.p.X.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ ∧
      cF.blocksInOrder[2]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        openingGS (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp))
          (openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol) (chainSh s) = some u →
        u = chainSh t) ∧
      ∀ s r₁ r₂ gs u,
        openingGS (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp))
          (openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol) (chainSh s) = some u →
        (∀ y ∈ VerifiableInference.Desc.K1.seedsOf (VerifiableInference.Desc.K1.firstPar
          Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp)) r₁, isZeroE y.2 = false) →
        (VerifiableInference.Desc.K1.answersIn r₂).length =
          (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp)).answers →
        ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, eL, eb, fs, f, hfs, hf, e⟩ := IM.k1_first_sits h.scope h.reads O
  obtain ⟨X, hp, P, x1, -, x3, x4, hpl, eo⟩ := row_zero h hfs hf
  have hO : Keeps f.opened := by
    rw [eo]
    exact keeps_zero _ _ _
  have c1 : ∀ s t u, f.opened s = .ok t →
      openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol (chainSh s) = .ok u →
      u = chainSh t := by
    rw [eo]
    exact fun s t u => openZero_carries P _ _ s t u
  have c2 : ∀ s u, openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol (chainSh s) = .ok u →
      ∃ t, f.opened s = .ok t := by
    rw [eo]
    exact fun s u => openZero_returns P _ _ hpl s u
  have hy := joined_iff e (by intro k; cases k) hO
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 0 ≤ 24) 0] at q
  refine ⟨Bs, b, X, hp, P, O.made, x1, x3, x4, q, ?_⟩
  generalize openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol = g₂ at c1 c2 ⊢
  refine ⟨fun s rs gs t u hd hg => ?_, fun s r₁ r₂ gs u hg hz hnn => ?_⟩
  · obtain ⟨m, h1, -, -, h4⟩ := (hy s t rs gs).1 hd
    unfold openingGS at hg
    split at hg
    · cases hg
    · obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg
      have em : m' = chainSh m := open_carries _ _ (gs := gs) h1 hm'
      subst em
      cases hg2 : g₂ (chainSh m) with
      | error w =>
        rw [hg2] at hu
        cases hu
      | ok u' =>
        rw [hg2] at hu
        obtain rfl : u' = u := Option.some.inj hu
        exact c1 m t u' h4 hg2
  · unfold openingGS at hg
    split at hg
    · cases hg
    · rename_i hm
      obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg
      obtain ⟨m, hd, em⟩ := open_returns _ _ (gs := gs) hm' hz hnn
      subst em
      obtain ⟨k1, k2⟩ := first_keeps _ _ hd
      have hf0 : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      cases hg2 : g₂ (chainSh m) with
      | error w =>
        rw [hg2] at hu
        cases hu
      | ok u' =>
        obtain ⟨t, ht⟩ := c2 m u' hg2
        refine ⟨t, (hy s t [r₁, r₂] gs).2 ⟨m, hd, k1.trans hf0, ?_, ht⟩⟩
        unfold ProofFile.sameReply
        rw [k2]
        exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_keeps
#print axioms Johnson.AtFull.Shape.row_zero
#print axioms Johnson.AtFull.Shape.opening_at
#print axioms Johnson.AtFull.Shape.openingGS
