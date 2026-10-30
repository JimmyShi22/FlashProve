-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SendWStepAtHead.lean: W's SENDING AT THE MEMORY WITH KIND K13's QUIET
SUB-PROTOCOL BEHIND IT (the place M:4; member 356 of the flat list) AT ITS SEAT IN THE PROOF FILE's
OWN FIRST CHAIN: the member has one step on the chain's shape, with both laws at the seated block's
own decision. Under the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  `sendW_keeps`: the sending's yes leaves the mark of failure and what goes out.
  `sendWGS P p`: the step at the seat: no mark; W's sending's step (wG,
    Johnson/Desc/First/Shape/SendW.lean); then, where two tests on the shape behind it pass
    (K13.Honest.ready4 and pads4, Johnson/Desc/K13/Honest/ShapeM4Ready.lean, read through viewM4 of
    Chain.lean), the quiet sub-protocol's step (rowsBG, Johnson/Desc/First/Shape/RowsBehindW.lean).
  **`sendW_step_at`**: with msg what linMessageW reads off the first chain's parameters: the member
    b at number 356 of cF.blocksInOrder is such that, at the step sendWGS (wPar Zp msg) (K13.whereOf Zp):
    where b says yes and the step returns, it returns the shape behind; and where the step returns,
    b says yes on two rounds in which no seed's factor is 0 and round 2 holds as many answers as the
    place counts. EVERY PARAMETER OF THE STEP IS TIED TO A VALUE.
By sendW_at (SendWAtHead.lean: the seated decision, half by half, both ways), sendW_carries |
sendW_returns (SendW.lean), rowsB_carries | rowsB_leaves (RowsBehindW.lean), sh4_view (Chain.lean)
and another house's rowsB_returns_shape (ShapeM4Ready.lean: the quiet sub-protocol says yes where
ready4 and pads4 pass at its own shape).
Limits. "Carries" is under the step's own return. ready4 and pads4 are enough for the quiet
sub-protocol's yes, not equal to its guards: so the step may refuse where the member says yes. The
two premises on the rounds stand as in Sending.lean. THE STATEMENT HAS NO CLAUSE ON b.rounds, though
"returns" speaks at two rounds: SendWFrame.lean's sendW_rounds_at has it. The makes of the
statement's rows behind the member (Forms.lean) are not treated here: see SendWFormsAtHead.lean.
UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and `protocolDataWellFormed`
accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named
sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). NO STATE IS SHOWN AT WHICH THE STEP
RETURNS. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.SendWAtHead
import Johnson.Desc.First.Shape.RowsBehindW
import Johnson.Desc.K13.Honest.ShapeM4Ready

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- W's sending's yes leaves the mark of failure and what goes out. -/
theorem sendW_keeps {P : VerifiableInference.Desc.K1.Par} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K1.sendAtS (Cl := Unit) P).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out := by
  simp only [VerifiableInference.Desc.K1.sendAtS] at h
  split at h
  · split at h
    · cases hb : (VerifiableInference.Desc.K1.sendOwn (Cl := Unit) P).decide
          { owed := VerifiableInference.Desc.K1.owedOf s,
            held := VerifiableInference.Desc.K1.stateOf s #[] } rs gs with
      | error e => simp [hb, Except.map] at h
      | ok y =>
        simp only [hb, Except.map, Except.ok.injEq] at h
        subst h
        exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- **The step at the seat**: no mark; W's sending (wG, Johnson/Desc/First/Shape/SendW.lean); then,
where another house's two tests on the shape pass (K13.Honest.ready4, pads4, read through viewM4),
the quiet sub-protocol's step (rowsBG, Johnson/Desc/First/Shape/RowsBehindW.lean). -/
def sendWGS (P : VerifiableInference.Desc.K1.Par) (p : VerifiableInference.Desc.K13.Where)
    (a : ChainSh) : Option ChainSh :=
  if a.marked then none
  else (wG P a).bind fun m =>
    if VerifiableInference.Desc.K13.Honest.ready4 p.lin (viewM4 m) &&
        VerifiableInference.Desc.K13.Honest.pads4 p.lin (viewM4 m) then rowsBG p m
    else none

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem sendW_step_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (b : Block S ProofFile.Cl) (msg : Array OracleNotice),
      linMessageW Zp.first.lin = some msg ∧ cF.blocksInOrder[356]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        sendWGS (wPar Zp msg) (VerifiableInference.Desc.K13.whereOf Zp) (chainSh s) = some u →
        u = chainSh t) ∧
      ∀ s r₁ r₂ gs u,
        sendWGS (wPar Zp msg) (VerifiableInference.Desc.K13.whereOf Zp) (chainSh s) = some u →
        (∀ y ∈ VerifiableInference.Desc.K1.seedsOf (wPar Zp msg) r₁, isZeroE y.2 = false) →
        (VerifiableInference.Desc.K1.answersIn r₂).length = (wPar Zp msg).answers →
        ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨b, msg, hm, q, hy⟩ := sendW_at h
  refine ⟨b, msg, hm, q, fun s rs gs t u hd hg => ?_, fun s r₁ r₂ gs u hg hz hnn => ?_⟩
  · obtain ⟨⟨m, h1, h2⟩, -, -⟩ := (hy s t rs gs).1 hd
    unfold sendWGS at hg
    split at hg
    · cases hg
    · obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg
      obtain rfl := sendW_carries h1 hm'
      split at hu
      · rw [rowsB_carries h2] at hu
        exact (Option.some.inj hu).symm
      · cases hu
  · unfold sendWGS at hg
    split at hg
    · cases hg
    · rename_i hmk
      obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg
      obtain ⟨m, hd, em⟩ := sendW_returns (gs := gs.take (VerifiableInference.Desc.K1.sendAtS
        (Cl := Unit) (wPar Zp msg)).openings) hm' hz hnn
      subst em
      split at hu
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        rw [← sh4_view] at hc
        obtain ⟨t, ht, -⟩ := VerifiableInference.Desc.K13.Honest.rowsB_returns_shape (Cl := Unit)
          hc.1 hc.2 ([r₁, r₂].drop 2) (gs.drop (VerifiableInference.Desc.K1.sendAtS
            (Cl := Unit) (wPar Zp msg)).openings)
        obtain ⟨k1, k2⟩ := sendW_keeps hd
        obtain ⟨j1, j2⟩ := rowsB_leaves ht
        have hf : s.failed = none := by
          have h1 : (chainSh s).marked = false := by simpa using hmk
          have h2 : s.failed.isSome = false := h1
          simpa using h2
        refine ⟨t, (hy s t [r₁, r₂] gs).2 ⟨⟨m, hd, ht⟩, j1.trans (k1.trans hf), ?_⟩⟩
        unfold ProofFile.sameReply
        rw [j2, k2]
        exact beq_self_eq_true _
      · cases hu

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sendW_keeps
#print axioms Johnson.AtFull.Shape.sendW_step_at
#print axioms Johnson.AtFull.Shape.sendWGS
