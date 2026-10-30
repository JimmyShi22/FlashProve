-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamClaim.lean: with honest data, the claim left at the base case is true at
the honest prover's last message.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. inv_end and claimTrue_of_inv hold for all parameters.
  inv_end          if the invariant BodyInv holds in front of some stage, it holds in front of the
                   last stage (the point where the algorithm's recursion ends: bodyEnd,
                   Johnson/Prover/Link/BodyEnd.lean).
  claimTrue_of_inv   at the last stage, the invariant gives ClaimTrue: the claim left at the base
                     case is true.
  fr_inv0          at the full-size parameters, the invariant holds in front of the first stage, at
                   the verifier's state as the prover's algorithm computes it. This holds for all
                   data that satisfy Meant, all coin variables and all verifier messages.
  fr_claimTrue     hence ClaimTrue holds at the last stage, under the same conditions.
  fr_claimPremise  hence the premise of Spec.linkShiftIn on the honest run holds, in that
                   statement's own form, at these data and at the challenges of every verifier
                   message. It holds at all coin variables, not only at those in the places
                   (InPlaces), and at every sampled element. It uses only the arm ClaimTrue of the
                   premise, never the arm LamZero.

Meant (Johnson/Prover/Link/LinkYesStm.lean) is the relation between the instance, the two tables and
the rows: each OOD sample is that of its table's rows, each table is the codeword of its rows, the
two tables hold the same cells, and the tables' words are well formed.

Why. Spec.linkShiftIn (SpecShiftIn.lean) compares what the honest prover's algorithm and the
simulator's algorithm disclose, up to a shift of the coins. It has one premise on the honest run: at
the last stage the sampled element is 0, or the claim left at the base case is true (ClaimTrue,
Johnson/LinkSim/AtText/Defs.lean). The proof that the link's verifier accepts the honest prover's
view (the format's view, on which the verifier's decision is written, not the disclosed view;
link_yes, Johnson/Prover/Link/LinkJoinF.lean) carries an invariant along the stages (BodyInv,
Johnson/Prover/Link/BodyInv.lean). At the last stage, one clause of that invariant is that claim,
read in the field. This file extracts it.

How it fits. fr_claimPremise is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean):
Johnson/LinkSim/AtHome/HomeTies.lean uses it at homeR b Z, with the honest data's Meant from
home_meant, and home_upTo (Johnson/LinkSim/AtHome/RoadCloses.lean) passes it on.

Sources. fr_inv0 makes the calls of the first half of the proof of linkYes_of
(Johnson/Prover/Link/LinkJoinE.lean) again, in its order; no lemma there hands out what they give.
claimTrue_of_inv draws the premises of claim_of_holds (Johnson/Prover/Link/BaseClaim.lean) from the
invariant as base_yes and base_yes_five do (Johnson/Prover/Link/BaseWhole.lean).

Limits.
- fr_inv0, fr_claimTrue and fr_claimPremise hold at the full-size parameters alone, and only for
  data that satisfy Meant. This file does not prove that any data satisfy Meant. Meant's seven
  clauses are proved at homeR b Z in meant_home (Johnson/Goal/Conditions/LinkMeant.lean), and Meant
  of the honest data there in home_meant (Johnson/LinkSim/AtHome/HomeTies.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecShiftIn
import Johnson.Prover.Link.LinkJoinF

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Params OnBytes.Slice Cb
open OnBytes.LinkSim.AtText
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (frP p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open OnBytes.Flat (dsFull RecFull)
open _root_.Run.PQ (SgX)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)
open Johnson.Prover.Link
open Johnson.Prover.Link.Full (pF curF nxtF)

/-- **The invariant reaches the last stage.** -/
theorem inv_end (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64), BodyInv p K (PlanAll p) D rest j cur l o t P col →
      BodyInv p K (PlanAll p) D [] (bodyEnd p K D rest j cur l o t P col).j
        (bodyEnd p K D rest j cur l o t P col).cur (bodyEnd p K D rest j cur l o t P col).l
        (bodyEnd p K D rest j cur l o t P col).o (bodyEnd p K D rest j cur l o t P col).t
        (bodyEnd p K D rest j cur l o t P col).P (bodyEnd p K D rest j cur l o t P col).col
  | [], _, _, _, _, _, _, _, h => h
  | next :: rest, j, cur, l, o, t, P, col, h =>
    inv_end p K D rest _ _ _ _ _ _ _ (hstep_at p K D next rest j cur l o t P col h).2

/-- **At the last stage the invariant gives ClaimTrue**: the claim left at the base case is true. -/
theorem claimTrue_of_inv (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (e : BEnd)
    (h : BodyInv p K (PlanAll p) D [] e.j e.cur e.l e.o e.t e.P e.col) : ClaimTrue p e := by
  obtain ⟨-, -, row, L, c, cl, m, star, a, hI⟩ := h
  have hF := hI.form.front
  have hcl : claimEnd p e = cl := by
    show ((stageAt p e.j e.cur).bind fun c => claimAt e.t.st.codes c (rowOf e.t)).getD _ = cl
    rw [rowOf_claim hF.pass, hF.stage]
    show (claimAt e.t.st.codes c row).getD _ = cl
    rw [hF.claim]
    rfl
  obtain ⟨cd, hcd, hl⟩ := code_of_pair _ _ _ _ _ hF.pair
  have hl' : cd.ell = (sgOf e.cur).C.l := hl
  have hk : c.k = 0 := by
    have h1 := H2K.JointK.stageAt_k hF.stage
    have h2 : (sgOf e.cur).h + (sgOf e.cur).g = e.cur.k := congrArg (·.k) hI.form.st
    have h3 := hI.form.h0
    have h4 := hI.form.g0
    omega
  have hfit : (row.c.fixLow [zeroE]).fits (ceilLog2 cd.ell) = true := by
    have h := hF.fits
    rw [hcd] at h
    rw [Own.formFits_agrees]
    exact h
  unfold ClaimTrue
  rw [hcl]
  exact claim_of_holds (sgOf e.cur) hI.form.h0 hI.form.g0 e.t.st.codes c row cl cd hcd hl' hk
    hF.claim hfit hI.form.fix _ hI.holds

section Full
variable (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
  (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE) (hM : Meant rr y M₀ M₁) (C : LCoins)
  (ρ : Rho (uL (ckP .two) dsFull))

include hM

/-- **The invariant in front of the first stage**, at the verifier's state as the prover's algorithm
computes it, for data that satisfy Meant, at the full-size parameters. -/
theorem fr_inv0 :
    BodyInv pF C.body (PlanAll pF) (drawsOf (drawnSL (ckP .two) dsFull ρ))
      (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6
      (lT frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lPS frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lCol frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ))) := by
  have hst : (p12Of frP).nums.stages = curF :: nxtF :: pF.nums.stages.drop 2 :=
    Full.stages_two_full
  have hrs := rs_full 97 (linOf rr y M₀ M₁) C ρ
  have hA := linkAll_rs frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ))
    curF _ hst
  have hfit := fit_full 97 (linOf rr y M₀ M₁) C ρ
  have hdr := drawn_rvOf (linkNext frP frS 97 (linOf rr y M₀ M₁) C) dsFull 0 []
    (drawnSL (ckP .two) dsFull ρ) (length_drawnSL _ _ ρ)
  have hsv := served_full 97 (linOf rr y M₀ M₁) C y ρ hM.wide
  rw [← hdr] at hsv
  obtain ⟨d', G', c, hc, h6, -, hSe, hO, hn⟩ := front6_walks_full rr _ _ [] hfit hsv
  have h5 : (rvOf dsFull 0 [] (linkNext frP frS 97 (linOf rr y M₀ M₁) C)
      (drawnSL (ckP .two) dsFull ρ)).take 5 =
      lFront frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)) := by
    rw [hrs, hA, List.append_assoc]
    exact List.take_left' rfl
  rw [h5] at hc h6
  have hcs : c = lStoredCols frP frS (linOf rr y M₀ M₁)
      (drawsOf (drawnSL (ckP .two) dsFull ρ)) := by
    have hc' := hc
    unfold lFront at hc'
    have hTa : frP.S.table.tree.a = frS.P.T.a := fr_linkSizesR.logN
    rw [want6 frP _ _ _ _ _ plan_full.1, stored_cols frP frS (linOf rr y M₀ M₁)
      (drawsOf (drawnSL (ckP .two) dsFull ρ)) dsFull frS.P.T.a _ y _
      ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 3⟩ rfl hTa rfl] at hc'
    exact (Option.some.inj hc').symm
  rw [List.append_nil, hcs] at h6
  obtain ⟨row, -, -, -, f3, f4⟩ := inv0_full (linOf rr y M₀ M₁) C ρ rfl rfl d' G' h6 hSe hO hn
    (front0_meets rr y M₀ M₁ hM C ρ d' G' h6 hSe hO hn)
  rw [f3]
  exact f4

/-- **The claim left at the base case is true at the honest prover's last message.** -/
theorem fr_claimTrue (e : BEnd)
    (he : linkEnd frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)) =
      some e) : ClaimTrue (p12Of frP) e := by
  have hst : (p12Of frP).nums.stages = curF :: nxtF :: pF.nums.stages.drop 2 :=
    Full.stages_two_full
  unfold linkEnd at he
  rw [hst] at he
  obtain rfl := Option.some.inj he
  exact claimTrue_of_inv pF C.body _ _ (inv_end pF C.body _ _ _ _ _ _ _ _ _
    (fr_inv0 rr y M₀ M₁ hM C ρ))

omit hM in
/-- **The premise of Spec.linkShiftIn on the honest run**, in its own form, for data that satisfy
Meant. -/
theorem fr_claimPremise (hM : Meant rr y M₀ M₁) (ρ : Rho (uL (ckP .two) dsFull)) :
    ∀ C, InPlaces frP frS C → ∀ e,
      linkEnd frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)) = some e →
      LamZero (drawsOf (drawnSL (ckP .two) dsFull ρ)) e ∨ ClaimTrue (p12Of frP) e :=
  fun C _ e he => Or.inr (fr_claimTrue rr y M₀ M₁ hM C ρ e he)

end Full

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.inv_end
#print axioms OnBytes.LinkSim.Seam.claimTrue_of_inv
#print axioms OnBytes.LinkSim.Seam.fr_inv0
#print axioms OnBytes.LinkSim.Seam.fr_claimTrue
#print axioms OnBytes.LinkSim.Seam.fr_claimPremise
