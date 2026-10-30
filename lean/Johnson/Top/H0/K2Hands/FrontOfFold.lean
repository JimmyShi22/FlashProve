-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontOfFold.lean: the code switch's law: «THE TEST ON THE FRONT ACCEPTS»
(frontB2, FrontB2.lean) FROM FACTS ON THE VERIFIER's STATE t IN FRONT OF THE SWITCH, each in the
form in which a theorem along the fold ends, and from closed facts at the place's written entry.
ONE CALL. A law file; no running text imports it.

  TargetLike T T₀   two targets agree in what the test reads: the shape, the two cuts, the kept
                    shapes.
  RowsLike out R₀ W₀ olds   the carried rows out agree with the written rows R₀ in what the test
                    reads (the two codes, the number of masks, the kept rows' count), their kept
                    members are olds, and their form's and vectors' sizes are the frame W₀'s.
  frontB2_of_fold   the theorem. ITS PREMISES, EACH WITH ITS PAYER:
    h      the text makes the front fx of t.
    hc     t.st.codes = cs                          the fold's fact «codes»
    hM     the messages' shapes are the listed M    the fold's fact «msgShapes», by msgShape_at
    hn     t.st.oracles.size = n0                   the count of messages at the cut
    hT     the target of the frame's group at its link is like x₀'s   the fold's facts «groups» |
           «frameGroups», «shape» | «frameShape», the link's number; a closed fact on the public
           shape's groups
    hR     ONE NAMED PREMISE: the copy of the frame that the switch is handed still carries out, the
           last closing's output                    the walk's
    hO     RowsLike out …                           the closing's law on its output, the kept
           members' numbers, closed facts
    hg     the front's group is grp                 at a link the front pushes it; else the text
           asks it
    hf     that group is there with so many rows    the front's group is fresh
    c1 c2 c3 c4   closed facts at the written entry: its codes; its kept shapes are M's at olds;
           olds lie below n0; its own kept members lie below its own count.
Limits. Nothing is paid here. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes

/-- Two targets agree in what the test reads. -/
structure TargetLike (T T₀ : SwitchTarget) : Prop where
  shape : T.shape = T₀.shape
  main : T.main = T₀.main
  rest : T.rest = T₀.rest
  kept : T.kept.toList.map (·.shape) = T₀.kept.toList.map (·.shape)

/-- The carried rows agree with the written rows, the place's numbers and the frame in what the test
reads. -/
structure RowsLike (out R₀ : SingleRows) (W₀ : SwitchFrame) (olds : List ℕ) : Prop where
  code : out.code = R₀.code
  maskCode : out.maskCode = R₀.maskCode
  masks : out.masks = R₀.masks
  keptRows : out.keptRows = R₀.keptRows
  kept : (switchKept out).toList = olds
  tensors : ∀ v ∈ out.c.tensors, v.vars = W₀.code.logEll
  d0 : (out.d.getD 0 #[]).size ≤ W₀.zk.ell
  d1 : (out.d.getD 1 #[]).size ≤ W₀.zk.ell

/-- **The test on the front accepts.** -/
theorem frontB2_of_fold {p : K2.P2} {t : S} {fx x₀ : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    {grp rows n0 : ℕ} {olds : List ℕ} {cs : Codes} {M : List OracleShape} {out : SingleRows}
    (h : K2.frontAt p t = some fx) (hc : t.st.codes = cs)
    (hM : ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = M[o]?)
    (hn : t.st.oracles.size = n0)
    (hT : ∀ g : ReqGroup, (t.check.frame.groups[t.check.frame.link]? = some g ∨
      ∃ a, t.here = .fin a ∧ a.G = some g) → TargetLike g.target x₀.T)
    (hR : ∀ f, CopyAt p t f → f.rows = out) (hO : RowsLike out x₀.f.rows W₀ olds)
    (hg : fx.f.group = grp) (hf : ∃ G, fx.st.groups[grp]? = some G ∧ G.rows.size = rows)
    (c1 : x₀.st.codes = cs) (c2 : keptShapes x₀ = olds.map fun o => M[o]?)
    (c3 : ∀ o ∈ olds, o < n0) (c4 : keptBelowB x₀ = true) :
    frontB2 x₀ W₀ grp rows n0 olds fx = true := by
  obtain ⟨e1, e2, f, hcp, er, -, -, g, eT, hgr⟩ := front_of_state h
  have eo : fx.f.rows = out := er.trans (hR f hcp)
  have T := hT g hgr
  refine test_of_facts ⟨by rw [e1, hc, c1], by rw [eo]; exact hO.kept, ?_, c3, c4,
    by rw [eT]; exact T.shape, by rw [eT]; exact T.main, by rw [eT]; exact T.rest,
    by rw [eT]; exact T.kept, by rw [eo]; exact hO.code, by rw [eo]; exact hO.maskCode,
    by rw [eo]; exact hO.masks, by rw [eo]; exact hO.keptRows, hg, hf, by rw [e2]; exact hn,
    by rw [eo]; exact hO.tensors, by rw [eo]; exact hO.d0, by rw [eo]; exact hO.d1⟩
  rw [c2, e2]
  refine List.map_congr_left fun o ho => hM o ?_
  rw [hn]
  exact c3 o ho

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frontB2_of_fold
