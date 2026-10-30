-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/OpeningFrame.lean: MEMBER 2 OF THE PROOF FILE's OWN FIRST CHAIN (G0:1 whole:
the first segment's opening with the row's "opened" behind it) IN THE FORM THAT THE THREAD's FRAME
ASKS (ProofFile.Honest.Carries | Returns at firstZA g vals, Johnson/AtFull/Shape/FrameForm.lean). Under
the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  `opening_more_at`: the member's declared rounds are K1's at the first segment's parameters
    (K1.rounds (K1.firstPar Bs.G₀.first (K1.gpOf Zp))); behind a yes on two rounds formsOf t.st =
    openForms ‹these parameters› ‹the number of messages in front› (formsOf s.st): the row's
    "opened" leaves the statement.
  `openingA P g₂`: the step on the whole: openingGS P g₂ on the chain's shape (OpeningAtHead.lean);
    among the makes a new group with no row in it, and the new messages' rows that the first sending
    lays (openForms, Johnson/Desc/First/Shape/ChainF.lean: sendForms over one empty group more).
  **`opening_frame`**: with Bs, X, hp and P tied by the same equations as in opening_at: for every g
    with g 2 = openingA (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (openZeroG P (fvsOf Zp.p.built.links)
    Zp.first.lin.kCol) and every vals with vals 2 s rs gs = seedsV ‹these parameters› rs: Carries
    and Returns at 2.
By opening_at | row_zero (OpeningAtHead.lean), joined_iff | keeps_zero (OpenedAtHead.lean),
openZero_lays (Johnson/Desc/First/Walk/Shape/FrameEnds.lean), first_forms (ChainF.lean),
IM.k1_first_sits (Johnson/IMR/FirstSeats.lean), carries_of_seat | returns_of_seat | seedsV
(FrameForm.lean), k1_fit (FormsAtHead.lean).
Limits. The step g and the test vals are letters with an equation at one number: no table of all 358
is built here. "Carries" is under the step's own return. seedsV IS A TEST ON VALUES IN A ROUND (no
seed's factor is 0). UNDER THE HEAD: that it has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). No state is shown by a theorem at
which the step returns. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or
hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.AtFull.Shape.OpeningAtHead
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame framesOf_arms fvsOf pubOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns carries_seat returns_seat)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Member 2's declared rounds, and the makes of the rows behind a yes on two rounds. -/
theorem opening_more_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.blocksInOrder[2]? = some b ∧
      b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.firstPar
        Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp)) ∧
      ∀ s r₁ r₂ gs t, b.decide s [r₁, r₂] gs = .ok t →
        formsOf t.st = openForms (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)) (chainSh s).core.st.oracles.length
          (formsOf s.st) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, eL, eb, fs, f, hfs, hf, e⟩ := IM.k1_first_sits h.scope h.reads O
  obtain ⟨X, hp, P, x1, -, x3, x4, hpl, eo⟩ := row_zero h hfs hf
  have hO : Keeps f.opened := by
    rw [eo]
    exact keeps_zero _ _ _
  have hy := joined_iff e (by intro k; cases k) hO
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 0 ≤ 24) 0] at q
  refine ⟨Bs, b, O.made, q, ?_, fun s r₁ r₂ gs t hd => ?_⟩
  · rw [e]
    exact List.append_nil _
  · obtain ⟨m, h1, -, -, h4⟩ := (hy s t [r₁, r₂] gs).1 hd
    rw [eo] at h4
    obtain ⟨-, im, -, rfl⟩ := openZero_lays h4
    have h1' : (VerifiableInference.Desc.K1.firstSegmentOpening (Cl := Unit) Bs.G₀.first
        (VerifiableInference.Desc.K1.gpOf Zp)).decide s [r₁, r₂]
        (gs.take (VerifiableInference.Desc.K1.firstSegmentOpening (Cl := Unit) Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)).openings) = .ok m := h1
    show formsOf m.st = _
    exact first_forms h1'

/-- The step of member 2 on the whole: openingGS on the chain's shape; among the makes a new group
with no row in it, and the new messages' rows that the first sending lays (openForms,
Johnson/Desc/First/Shape/ChainF.lean). -/
def openingA (P : VerifiableInference.Desc.K1.Par) (g₂ : ChainSh → Except String ChainSh)
    (x : ShA) : Except String ShA :=
  match openingGS P g₂ x.1 with
  | some u => .ok (u, openForms P x.1.core.st.oracles.length x.2)
  | none => .error "the opening's member refuses on shapes"

/-- **The frame's two premises at member 2** (G0:1 whole: the first segment's opening with the row's
"opened" behind it). -/
theorem opening_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase), ∃ X hp P,
      (cF.blocksInOrder[2]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Zp.p.built.links[0]? = some X ∧ Zp.p.X.G[X.g]? = some hp ∧
      P = ⟨pubOf X, 0, Zp.p.X.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ ∧
      ∀ (ft : Nat) g vals,
        g 2 = openingA (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp))
          (openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol) →
        (∀ s rs gs, vals 2 s rs gs = seedsV (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)) rs) →
        Carries cF.blocksInOrder ft (firstZA g vals) 2 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 2 := by
  obtain ⟨Bs, b, X, hp, P, e1, x1, x3, x4, q, hc, hr⟩ := opening_at h
  obtain ⟨Bs₁, b₁, e1', q₁, hrd, hf⟩ := opening_more_at h
  obtain rfl : Bs = Bs₁ := Except.ok.inj (e1.symm.trans e1')
  obtain rfl : b = b₁ := Option.some.inj (q.symm.trans q₁)
  refine ⟨Bs, X, hp, P, by rw [q]; rfl, e1, x1, x3, x4, fun ft g vals hg hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u hfit hd hu => ?_
    rw [hg] at hu
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, -⟩ := k1_fit hfit
    unfold openingA at hu
    split at hu
    · rename_i w hw
      cases hu
      have := hc s _ gs t w hd hw
      subst this
      show (chainSh t, _) = (chainSh t, formsOf t.st)
      rw [hf s (noDigest r₁) (noDigest r₂) gs t hd]
      rfl
    · cases hu
  · refine returns_of_seat q fun s rs gs u hfit hu hvv => ?_
    rw [hg] at hu
    rw [hv] at hvv
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, han⟩ := k1_fit hfit
    unfold openingA at hu
    split at hu
    · rename_i w hw
      refine hr s (noDigest r₁) (noDigest r₂) gs w hw ?_ han
      intro y hy
      have := List.all_eq_true.1 hvv y hy
      simpa using this
    · cases hu

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.opening_more_at
#print axioms Johnson.AtFull.Shape.opening_frame
#print axioms Johnson.AtFull.Shape.openingA
