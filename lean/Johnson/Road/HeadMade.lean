-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadMade.lean: the parts of a run of the output head's check are the verifier's own
results: from its public part and from the check itself.

The theorems of Johnson/Road/HeadPlace.lean, Johnson/Road/HeadReads.lean and
Johnson/Road/HeadSeg.lean begin "if layout returns L", "if planH2 returns H0", "if ownerOf returns
O", "if tablesOf succeeds". This file draws these hypotheses from two words of the verifier: its
public part publicOf (OnBytes/Model/VerifyPublic.lean) returns X, and its check of the head's
sub-proof, called as the link of the head calls it (headPlanOf, OnBytes/Model/VerifyLinks.lean),
succeeds.

What is compared with what: texts of the verifier with each other. The library is mentioned only
through the type of the cells and the sizes DF.

Main definitions: PublicH (what is used of what publicOf returns).
Main theorems.
 - pub_fields, layout_of_polLayout, ok_of_either, ok_of_either2; publicH_of_public: publicOf, taken
   apart.
 - lent_of_public: in what publicOf returns, the last matrix of the head's list is marked as another
   sub-proof's and bears the label that the stream which leaves the last group of layers has in the
   list of that group's plan (lent_label, Johnson/Road/HeadSeg.lean).
 - madeH_of_run: the record MadeH of Johnson/Road/HeadReads.lean, of the run that the check builds.
 - trueH_of_public: so, if every record of the run's list of tables holds what it says of matrices
   M, the reads are true of the cells that are read in M (trueH_of_made).
 - claim_of_public: the one claim on the weights that the check hands to the merge, on the library's
   output matrix (claim_of_run, Johnson/Road/HeadWeight.lean).

The hypotheses, and where they are met. publicOf returns: at the full-size example a run
(Johnson/Road/HeadPlaceRun.lean). The check succeeds: no run and no theorem; it needs a proof.
FullH, Switches, Sized, Sized2: as in Johnson/Road/HeadPlace.lean. SizedW, the switch, the number of
column bits, lamS = 13: at that example a run
(Johnson/Road/HeadWeightRun.lean [not in this library]). Holds: it can be met at any matrices
(Johnson/Road/HeadMet.lean); no theorem concludes it of a verifier's run.

What is not claimed. That two matrices with one label have the same entries (LentH). Nothing is a
statement on what a verifier's acceptance shows. The program does not import this file.
-/
import Johnson.Road.HeadSeg
import Johnson.Road.HeadWeight
import Johnson.Road.HeadRunParts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading World HTailF2 Fork wsLayOf)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HPlanH2 planH2)
open OnBytes.Model.Verify (Public publicOf polLayout borderOf ownerOf layerShape weightShape)

/-! ## The public part, taken apart -/

/-- What the layers' public record keeps of its arguments: the layout and the layout of the
weights. -/
theorem pub_fields {y : Lay} {sc : Model.Layer.Scales} {rope : Array ℕ} {wsLay : Model.WsLay}
    {V : ℕ} {tokv : Array ℕ} {set : Model.Settings} {P : Model.Layer.Pub}
    (hP : Model.Layer.Pub.of y sc rope wsLay V tokv set = .ok P) : P.y = y ∧ P.wsLay = wsLay := by
  unfold Model.Layer.Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- The layout that polLayout returns is what the layers' layout returns on the shape and the call
lines of the scan that it returns. -/
theorem layout_of_polLayout {pol : ByteArray} {P : Model.PolScan} {y : Lay}
    (h : polLayout pol = .ok (P, y)) : Model.Layer.layout (layerShape P) P.polCalls = .ok y := by
  unfold Model.Verify.polLayout at h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  assumption

/-- If either of two steps, chosen by a condition, and one continuation return a value, the
continuation returns it on some value. -/
theorem ok_of_either {c : Prop} [Decidable c] {α β : Type} {x x' : Except String α}
    {jp : α → Except String β} {y : β} (h : (if c then x >>= jp else x' >>= jp) = .ok y) :
    ∃ a, jp a = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩
  · rw [if_neg hc] at h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩

/-- The same where the first branch has two steps. -/
theorem ok_of_either2 {c : Prop} [Decidable c] {α β γ : Type} {x : Except String γ}
    {g : γ → Except String α} {x' : Except String α} {jp : α → Except String β} {y : β}
    (h : (if c then x >>= fun a => g a >>= jp else x' >>= jp) = .ok y) : ∃ a, jp a = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    obtain ⟨b, -, h⟩ := ok_of_bind h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩
  · rw [if_neg hc] at h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩

/-- What is used here of what the verifier's public part returns: five of its lines, on its own
results. -/
structure PublicH (X : Public) : Prop where
  /-- the layers' layout -/
  lay : Model.Layer.layout (layerShape X.P) X.P.polCalls = .ok X.y
  /-- the layout of the committed weights -/
  ws : wsLayOf (weightShape X.P X.y) X.y.h.p3 X.P.lkW = .ok X.layers.wsLay
  /-- the head's layout -/
  head : Model.Head.layout X.hS X.y.tauFC = .ok X.HLy
  /-- what the head's plan reads of the last group's plan -/
  owner : ownerOf X.y X.G = .ok X.owner
  /-- the head's plan: what planH2 returns, with one field rewritten -/
  plan : ∃ H0, planH2 X.P.settings X.hS X.HLy (borderOf X.y) X.owner X.y.NGr X.P.lkW = .ok H0 ∧
    X.H = { H0 with Fp := H0.Fp.trimL }

/-- **The public part, taken apart.** -/
theorem publicH_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) : PublicH X := by
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_either h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_either2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  obtain ⟨e1, e2⟩ := pub_fields (by assumption)
  have hy := layout_of_polLayout hpl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    exact hy
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1, e2]
    assumption
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    assumption
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    assumption
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    refine ⟨?H0, ?a, ?b⟩
    case a => assumption
    case b => rfl

/-! ## Whose matrix the head borrows -/

/-- **In what the public part returns, the head borrows the stream of the last group.** For hf in
four parts: the matrix with the number NHf + 3 of the head's plan is marked as a matrix of another
sub-proof and bears the label of the matrix with the number firstM y 5, the stream that goes out, in
the list of the plan of the last group of layers. -/
theorem lent_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (hN : X.hS.NHf = 4) :
    ∃ P stream, X.G.back? = some P ∧ P.tl.mats[firstM X.y 5]? = some stream ∧
      (X.H.tl.mats.getD (X.hS.NHf + 3) {}).aId = stream.aId ∧
      (X.H.tl.mats.getD (X.hS.NHf + 3) {}).kind = 1 ∧
      (X.H.tl.mats.getD (X.hS.NHf + 3) {}).foreign = some 0 := by
  have A := publicH_of_public h
  obtain ⟨H0, hH, e⟩ := A.plan
  have k := lent_label A.owner hH hN
  rw [e]
  exact k

/-! ## The run that the check builds -/

section Run

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **The parts of the run are the verifier's own results.** If the public part returns X and the
check of the head's sub-proof, called on X as the head's link calls it, succeeds, then the run that
the check builds meets the record MadeH, and the record of the smallness test on which its messages
run has the plan's list of matrices. Ft: the state from which tablesOf has run; every array has as
many columns in it as in the state F that the caller handed in. -/
theorem madeH_of_run {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) {cov : Model.Head.Covered} {Lc Lc' : Model.LinkCtx}
    {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    (H : Walk.OkL (Model.Head.runForkHidH2 X.hS X.HLy (borderOf X.y) X.H X.owner cov
      X.layers.wsLay) Lc F C wo Lc' G D) :
    ∃ (iU3 : ℕ) (x : Model.Head.Heard) (t : Model.Head.Tables) (H0 : HPlanH2) (tl0 : HTailF2)
      (Ft Ft' : Fork) (Ct Ct' : Ctx),
      MadeH (Parts.runOf X.hS X.HLy (borderOf X.y) X.H cov x t iU3) X.y.tauFC X.y X.P.settings
        X.owner X.y.NGr X.P.lkW H0 Ft Ft' Ct Ct' ∧
      X.H.tl.closeFuns t.funs = some tl0 ∧ tl0.mats = X.H.tl.mats ∧ tl0.NM = X.H.tl.NM ∧
      Walk.Kept F Ft := by
  have A := publicH_of_public h
  obtain ⟨H0, hH, e⟩ := A.plan
  obtain ⟨-, iU3, x, t, tl0, tl1, tl2, claim, Lt, Lt', Lw, Lw', Fh, Fh', Ft, Ft', Fs, Fs', Fc, Fc',
    Fm, Fm', Fw, Fw', Ch, Ch', Ct, Ct', Cs, Cs', Cc, Cc', Cm, Cm', Cw, Cw',
    a1, -, -, a4, a5, -, -, -, -, -, kt, -⟩ := Parts.run_parts H
  obtain ⟨-, c2, c3⟩ := closeFuns_keeps a5
  refine ⟨iU3, x, t, H0, tl0, Ft, Ft', Ct, Ct', ⟨A.head, rfl, hH, ?_, ?_, a1, a4⟩, a5, c2, c3, kt⟩
  · show X.H.tl.mats = H0.tl.mats
    rw [e]
  · show X.H.tl.NM = H0.tl.NM
    rw [e]

/-- **From the verifier's two words to true reads.** If the public part returns X, at the sizes at
which the library's head is written, and the check of the head's sub-proof succeeds on X, then for
the run R that the check builds and the record tl0 on which the smallness test's messages run: in
every world in which each record of the run's list of tables holds what it says of matrices M, the
reads are true of the cells that are read in M by the verifier's rule. -/
theorem trueH_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (hF : FullH X.hS) (S : Switches (layerShape X.P))
    (Z : Sized (layerShape X.P) Inst.Model.All.DF) (Z2 : Sized2 (layerShape X.P) Inst.Model.All.DF)
    {cov : Model.Head.Covered} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx}
    {wo : Model.WsForkOut}
    (H : Walk.OkL (Model.Head.runForkHidH2 X.hS X.HLy (borderOf X.y) X.H X.owner cov
      X.layers.wsLay) Lc F C wo Lc' G D) :
    ∃ (iU3 : ℕ) (x : Model.Head.Heard) (t : Model.Head.Tables) (tl0 : HTailF2),
      X.H.tl.closeFuns t.funs = some tl0 ∧
      ∀ (K3 : ℕ) (M : Mats K), (∀ Fn ∈ t.funs, Holds ρ W tl0 iU3 K3 M Fn) →
        TrueH ρ W (Parts.runOf X.hS X.HLy (borderOf X.y) X.H cov x t iU3) K3
          (cellsH X.hS X.HLy (borderOf X.y) M) := by
  obtain ⟨iU3, x, t, H0, tl0, Ft, Ft', Ct, Ct', A, a5, c2, c3, -⟩ := madeH_of_run h H
  exact ⟨iU3, x, t, tl0, a5, fun K3 M hM =>
    trueH_of_made A hF (publicH_of_public h).lay S Z Z2 c2 c3 hM⟩

/-- **The claim on the weights of the verifier's own run, on the library's output matrix.** If the
public part returns X, the shape of the weights that it hands to wsLayOf agrees with the library's
reference parameters, the switch is on, the number of column bits is the library's, the plan has 13
rounds over the channels, and the check of the head's sub-proof succeeds on X: then the check has
made one claim on the weights and handed it, with the slot x.sV, to the merge; and if the check has
drawn 13 challenges over the channels, the sum that the claim speaks of, in any matrix Wc, is the
sum of claim_of_run (Johnson/Road/HeadWeight.lean) on the library's output matrix read in Wc. -/
theorem claim_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (Zs : SizedW (weightShape X.P X.y) Inst.Model.ppref)
    (hp3 : X.y.h.p3 = true) (hlk : X.P.lkW = Inst.Model.Layout.kRef) (hlam : X.H.lamS = 13)
    {cov : Model.Head.Covered} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx}
    {wo : Model.WsForkOut}
    (H : Walk.OkL (Model.Head.runForkHidH2 X.hS X.HLy (borderOf X.y) X.H X.owner cov
      X.layers.wsLay) Lc F C wo Lc' G D) (Wc : Wm K) :
    ∃ (iU3 : ℕ) (x : Model.Head.Heard) (t : Model.Head.Tables) (claim : Model.WsClaim),
      (∃ Fm Fm' Cm Cm', Ok (Model.wsForkEnd X.layers.wsLay #[claim] #[x.sV]) Fm Cm wo Fm' Cm') ∧
      (13 ≤ x.rs.size → ∃ ew, claimVal ρ X.layers.wsLay Wc claim =
        ∑ v ∈ Finset.range Inst.Model.Head.nV, ∑ k ∈ Finset.range Inst.Model.Head.nD,
          ρ.val ((avOf (Parts.runOf X.hS X.HLy (borderOf X.y) X.H cov x t iU3) ew).getD v zeroE) *
            eqR ρ x.rs 0 13 k * Inst.Model.Head.Hof Wc k v) := by
  have hws := (publicH_of_public h).ws
  rw [hp3, hlk] at hws
  obtain ⟨-, iU3, x, t, tl0, tl1, tl2, claim, Lt, Lt', Lw, Lw', Fh, Fh', Ft, Ft', Fs, Fs', Fc, Fc',
    Fm, Fm', Fw, Fw', Ch, Ch', Ct, Ct', Cs, Cs', Cc, Cc', Cm, Cm', Cw, Cw',
    -, -, -, -, -, -, a7, a8, -⟩ := Parts.run_parts H
  refine ⟨iU3, x, t, claim, ⟨Fm, Fm', Cm, Cm', a8⟩, fun hs => ?_⟩
  obtain ⟨ew, -, -, hv⟩ := claim_of_run ρ Zs hws a7 hlam hs Wc
  exact ⟨ew, hv⟩

end Run

#print axioms publicH_of_public
#print axioms lent_of_public
#print axioms madeH_of_run
#print axioms trueH_of_public
#print axioms claim_of_public

end OnBytes.Road.Hd
