-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/NamedAt346.lean: the kind "lookup" (K3): at every state that
the first chain's own sub-protocols reach at border 346, right behind the lookup on the digits of
the head's link: each of the four families of forms in what that lookup heard (the rows, the key
side's end form, the form on the bits' end slot, the leaves' start form) names no entry, and slots
alone that are there and filled in the state's ledger: the library's `Fo.Tp.PadNames`
(Johnson/Top/H/Keep/PadNamed.lean). Under the library's hypothesis `P5J.AtMgA` alone. Theorems; no
definition.

Terms. Honest/K3/GLOSSARY.md. "Reached": the library's `Reach` (Johnson/Top/H0/Walk/Reach.lean) over
the chain's own list of sub-protocols, not over the list of the proofs' wrapped ones (`below`,
Johnson/Desc/Sound/ChainRule.lean).

What is shown.
  `sized_345`: every state reached at border 345 stands in the head's link, and that link's own
    ledger has its sizes. (Whether the link's field opened is set is not said.)
  `padNames_behind_digits_any`: `padNames_behind_digits` (Honest/K3/Law/NamedDigits.lean) with
    "whatever ledger the state in front holds has its sizes" in the place of a named ledger with its
    sizes.
  `padNames_at_345`: the same at the decision of the chain's own sub-protocol number 345.
  `padNames_346`: the main theorem: the title's sentence.

Follows.
  `sized_345` is the first half of the library's `heard_345` (Johnson/P5J/K03WtBackAt.lean), which
    speaks of states reached over the wrapped list. Its proof is that theorem's, line for line (the
    same lines stand in `P4.waK6_at_346`, Johnson/P4R/WaK6At346.lean), with `P4.reach_last` and
    `P4.step_yes` (Johnson/P4R/Back341N.lean) in the place of `P4.peel`: each lemma that this half
    calls takes a sub-protocol of the chain's own list and its decision. With that change: each call
    of `P4.peel` is two lines here; `h341` stands for `reach_raw h341`; the line on
    `Came.mergeClaim_behind`, which serves the second half, is left out; the last two lines are one.
  `padNames_at_345`: its hypotheses down to `hd` and the first thirteen lines of its proof are those
    of the library's `P4.digits_345` (Johnson/P4R/WaK6At346.lean).
K03WtBackAt.lean is imported, and through it WaK6At346.lean. That the sentence was wanted at a
reached state, and its form, is an ask from the side of the files under Honest/Thread/.

Related. The library's `four_behind_digits` (Johnson/Desc/First/Link/Law/FourBehindDigits.lean) has
the same hypotheses as `padNames_behind_digits`; it says of the four forms of `four8 tl g` that each
slot lies in the leaves' window or is filled at every later ledger. Its statement does not speak of
the rows. The library's `padNames_behind_calls` (Johnson/Desc/First/Link/Law/K4AtFront.lean) shows
`PadNames` behind the seated lookup on the calls. The library's `four_at_head`
(Johnson/Desc/First/Link/Law/FourAtBatch.lean) takes a stronger sentence than that of `sized_345` as
its hypothesis `hLed`: at every such state a ledger is open, and has its sizes.

Hypotheses that remain. In `padNames_346`: `P5J.AtMgA`; the state is reached at 346; and, without a
name, in front of the conclusion's arrows: the state holds the ledger F, and g is what the digits'
seat reads as heard. In `sized_345` and `padNames_at_345`: the scope, the files read, the
description's return and its test on the plan; in the first besides: the state is reached at 345; in
the second: b0 is the chain's sub-protocol number 345, its decision accepts from s to t, and
whatever ledger s holds has its sizes. In `padNames_behind_digits_any`: those of
`padNames_behind_digits`, with the change told above.

Limits. Where sub-protocol 345 never accepts from a reached state nothing is reached at 346, and the
main theorem says nothing. That a ledger is open and that something is heard at the state behind is
said by `padNames_at_345`, not by the main theorem. Nothing over the sub-protocol at 346. At the
full size alone. No instance of `P5J.AtMgA` is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P5J.K03WtBackAt
import Johnson.Desc.ProofFile.Honest.K3.Law.NamedDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.OnPublicFiles (theStated_yes_digits decide_named)

/-- `padNames_behind_digits` under "whatever ledger the state in front holds has its sizes". No
instance of these hypotheses is exhibited in this file. -/
theorem padNames_behind_digits_any {Cl' : Type} (claim : Aff → Cl')
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl')
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    (hS : ∀ F, s.fork? = some F → OnBytes.PscRun.Sized F) :
    ∃ (G : Fork) (g : Forest.Heard), s₂.fork? = some G ∧
      (Desc.K3.seatDigits claim).heard s₂ = some g ∧ _root_.Fo.Tp.PadNames g G ∧
      OnBytes.PscRun.Sized G := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, -⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨F, y, hF, -, -, -⟩ :=
    decide_named (Desc.K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  exact padNames_behind_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd hF
    (hS F hF)

end ProofFile.Honest.K3.Law

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.PscRun (Sized)
open OnBytes.Model (Fork Aff)
open ProofFile (Cl)
open P4 (reach_last step_yes yes_341 kept_342 kept_343 kept_344 wellLaid_341 plan_at)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At a state reached at border 345: the head's link, and a ledger with its sizes.** No instance
of these hypotheses is exhibited in this file. -/
theorem sized_345 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {XP : Type} {start : XP → S} {z : XP} {s345 : S} (h345 : Reach 0 c.blocksInOrder start 345 (z, s345)) :
    ∃ o, s345.here = .head o ∧ Sized o.F := by
  obtain ⟨s344, B4, h344, hB4, y4⟩ := reach_last h345
  obtain ⟨r4, g4, d4⟩ := step_yes y4
  obtain ⟨s343, B3, h343, hB3, y3⟩ := reach_last h344
  obtain ⟨r3, g3, d3⟩ := step_yes y3
  obtain ⟨s342, B2, h342, hB2, y2⟩ := reach_last h343
  obtain ⟨r2, g2, d2⟩ := step_yes y2
  obtain ⟨s341, B1, h341, hB1, y1⟩ := reach_last h342
  obtain ⟨r1, g1, d1⟩ := step_yes y1
  have c1 := yes_341 hS hR O hB1 d1
  have c2 : WellLaid ((seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s341) :=
    wellLaid_341 hS hR O (plan_at O hOk 340) h341 _ _
  obtain ⟨a, F1, X0, Q, -, hop, -, e⟩ := Came.decide_record _ _ _ _ c1
  have ho2 : s342.here = .head { a with F := F1, x := some X0, squaresP := some Q } := by rw [e]
  have eL : (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s342 = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  have hz2 : Sized ({ a with F := F1, x := some X0, squaresP := some Q } : HeadOwn).F := by
    have hL := blockAt_later _ _ _ _ s341 s342 r1 g1 c1
    rw [eL] at hL
    exact hL.sized (sized_of_wellLaid c2)
  have k2 := kept_342 hS hR O hB2 d2 ho2
  obtain ⟨o3, ho3, hz3⟩ := k2.next ho2 hz2
  have k3 := kept_343 hS hR O hB3 d3 ho3
  obtain ⟨o4, ho4, hz4⟩ := k3.next ho3 hz3
  have k4 := kept_344 hS hR O hB4 d4 ho4
  exact k4.next ho4 hz4

/-- **At the decision of sub-protocol 345 all four families are named behind it.** No instance of
these hypotheses is exhibited in this file. -/
theorem padNames_at_345 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {b0 : Block S Cl} {s t : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hB : c.blocksInOrder[345]? = some b0) (hd : b0.decide s rs gs = .ok t)
    (hz : ∀ F, s.fork? = some F → Sized F) :
    ∃ (G : Fork) (g : OnBytes.Model.Forest.Heard), t.fork? = some G ∧
      t.tl?.bind (·.heard) = some g ∧
      _root_.Fo.Tp.PadNames g G ∧ Sized G := by
  obtain ⟨Lk, b, b', h1, h2, hb', hla⟩ := IM.k3_of hS hR O 24 (by decide) true
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  obtain ⟨e4, eN, -⟩ := Meaning.scope_plans hS hR O.public
  have hH : VerifiableInference.Desc.K3.isHead Bs.G₀.W 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [e4, eN]
    rfl
  have hpc : (IM.k3Place 24 true).piece = VerifiableInference.Desc.K3.pieceAt Bs.G₀.W 24 true := by
    unfold VerifiableInference.Desc.K3.pieceAt
    rw [hH]
    rfl
  obtain ⟨G, g, hG, hg, N, hs⟩ := padNames_behind_digits_any _ _ _ _ _ _ b' hb'
    (IM.plan_alone O hOk h1 h2 hla) 24 rfl hpc s t rs gs ((IM.k3_yes hla s t rs gs).1 hd).1 hz
  exact ⟨G, g, hG, hg, N, hs⟩

end

/-- **At every state reached at border 346 the four families of what the lookup on the head's digits
heard are named at the state's ledger.** Conditional on `P5J.AtMgA`. No instance of this hypothesis
is exhibited in this file. -/
theorem padNames_346 {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Cl' : Type} (claim : Aff → Cl')
    (z : ProofFile.InstPub) (s : S) (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, s)) :
    ∀ g F, s.fork? = some F → (VerifiableInference.Desc.K3.seatDigits claim).heard s = some g →
      _root_.Fo.Tp.PadNames g F := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨s5, b0, h345, hB, y⟩ := reach_last hr
  obtain ⟨rs, gs, hd⟩ := step_yes y
  obtain ⟨o, ho, hz⟩ := sized_345 h.scope h.reads O h.laid.planOk h345
  have hz' : ∀ F, s5.fork? = some F → Sized F := by
    intro F hF
    cases hq : o.opened with
    | false => simp [S.fork?, ho, hq] at hF
    | true =>
      have e : o.F = F := by simpa [S.fork?, ho, hq] using hF
      exact e ▸ hz
  obtain ⟨G, g', hG, hg', N, -⟩ := padNames_at_345 h.scope h.reads O h.laid.planOk hB hd hz'
  intro g F hF hg
  obtain rfl : G = F := Option.some.inj (hG.symm.trans hF)
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  exact N

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.padNames_behind_digits_any
#print axioms ProofFile.Honest.K3.Law.sized_345
#print axioms ProofFile.Honest.K3.Law.padNames_at_345
#print axioms ProofFile.Honest.K3.Law.padNames_346
