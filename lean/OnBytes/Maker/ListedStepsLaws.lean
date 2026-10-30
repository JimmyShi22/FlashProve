-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedStepsLaws.lean: the named tests of OnBytes/Maker/ListedSteps.lean say yes, all
of them, just where the verifier along lists says yes behind its chain. Proofs.

No soundness: a test. This module states laws on what the runs of lean/Ask/ call; it states nothing
on soundness.

Main names:
  `afterBOL_det`: the value of afterBOL at a family g of oracle answers, as one conjunction on the
    two forests.
  `behindSteps_yes`: all fourteen lines of behindSteps say yes if and only if strictBBL says yes and
    afterBOL's value at g is yes.
  `acceptSteps_yes`: all nine lines of acceptSteps say yes if and only if the description of a whole
    file accepts.
  `wholeSteps_yes`: all twenty-three lines of wholeSteps say yes if and only if strictBBL says yes
    and afterBOL's value at g is yes, at the whole file's values.
Limits: they speak of the part behind the chain, at a given value (ρ, rts, ph) of the chain; the
chain itself is not in them. g is any family. Nothing on time or memory. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

/-! ### On Bool -/

theorem and9 (a b c d e f g h i : Bool) :
    (a && (b && (c && (d && (e && (f && (g && (h && (i && true))))))))) =
      (a && b && c && d && e && f && g && h && i) := by
  simp only [Bool.and_assoc, Bool.and_true]

theorem and14 (s1 s2 s3 s4 s5 s6 s7 f1 f2 a1 a2 a3 a4 a5 : Bool) :
    (s1 && (s2 && (s3 && (s4 && (s5 && (s6 && (s7 && (f1 && (f2 && (a1 && (a2 && (a3 && (a4 &&
      (a5 && true)))))))))))))) =
      ((s1 && s2 && s3 && s4 && s5 && s6 && s7) && (f1 && f2 && a1 && a2 && a3 && a4 && a5)) := by
  simp only [Bool.and_assoc, Bool.and_true]

theorem isSome_ite_unit (c : Bool) :
    (if c = true then some () else none : Option Unit).isSome = c := by
  cases c <;> rfl

theorem ite_and_bool (p : Prop) [Decidable p] (q v : Bool) :
    (if p ∧ q = true then v else false) = (decide p && q && v) := by
  by_cases hp : p <;> cases q <;> simp [hp]

theorem steps_onF {α : Type} (a b : Option (List α)) (p1 p2 p3 p4 p5 : List α → Bool) :
    (a.isSome && b.isSome && onF p1 (bothF a b) && onF p2 (bothF a b) && onF p3 (bothF a b) &&
      onF p4 (bothF a b) && onF p5 (bothF a b)) =
      onF (fun F => p1 F && p2 F && p3 F && p4 F && p5 F) (bothF a b) := by
  cases a <;> cases b <;> simp [onF, bothF]

theorem onF_absorb {α : Type} (o : Option α) (p : α → Bool) (c s : Bool) :
    (s && onF (fun F => p F && c) o && c) = (s && onF (fun F => p F && c) o) := by
  cases o <;> cases c <;> simp [onF]

theorem det_ite {S : Rom.OSpec} {α : Type} (g : Rom.Fam S) (p : Prop) [Decidable p]
    (a b : Rom.OComp S α) : (if p then a else b).det g = if p then a.det g else b.det g := by
  split <;> rfl

section Letters
open TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem afterFL_det {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)
    (Fs : List (Forest lam L)) (s : List (Dig lam)) (g : Fam (typedOracleFamily lam K L)) :
    (afterFL Q sh wl depthReq x π ρ rts ph Fs s).det g =
      ((runForests Fs s).det g && (reqPart depthReq π ph).det g &&
        Q.loc.accept x (wl.build fun p => (π.ext p).map Opening.sym)
          (mkTr Q.loc.shape Q.ann sh rts π.plains ρ π.opens)) := by
  unfold afterFL
  rw [OComp.det_bind, OComp.det_bind]
  rfl

/-- **The value of afterBOL at g.** -/
theorem afterBOL_det {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (rd : Leaves)
    (rdE : List E.Pos) (g : Fam (typedOracleFamily lam K L)) (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape)
    (ph : Phase lam) :
    (afterBOL Q sh wl nOpen maxDepth embS embE depthReq cms x π rd rdE ρ rts ph).det g =
      onF (fun F => decide ((flatF F).length ≤ nOpen) &&
          ((flatF F).all fun c => c.wellFormed && decide (c.depth ≤ maxDepth)) &&
          (runForests F (readsF F)).det g && (reqPart depthReq π ph).det g &&
          Q.loc.accept x (wl.build fun p => (π.ext p).map Opening.sym)
            (mkTr Q.loc.shape Q.ann sh rts π.plains ρ π.opens))
        (bothF (forestsBL Q.loc.shape Q.ann sh embS rts π.opens rd)
          (forestExtL wl embE cms π.ext rdE)) := by
  unfold afterBOL forestsOfL
  cases forestsBL Q.loc.shape Q.ann sh embS rts π.opens rd with
  | none => rfl
  | some a =>
    cases forestExtL wl embE cms π.ext rdE with
    | none => rfl
    | some b =>
      show (if (flatF (a ++ b)).length ≤ nOpen ∧
          ((flatF (a ++ b)).all fun c => c.wellFormed && decide (c.depth ≤ maxDepth)) = true then
        afterFL Q sh wl depthReq x π ρ rts ph (a ++ b) (readsF (a ++ b))
        else (pure false : TypedOracleComputation lam K L Bool)).det g = _
      rw [det_ite, afterFL_det]
      show (if (flatF (a ++ b)).length ≤ nOpen ∧
          ((flatF (a ++ b)).all fun c => c.wellFormed && decide (c.depth ≤ maxDepth)) = true then
        _ else false) = _
      rw [ite_and_bool]
      simp only [onF, bothF, Bool.and_assoc]

/-- **All fourteen lines say yes just where the verifier along lists says yes behind its chain.** -/
theorem behindSteps_yes (sMT sFS : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (own : Leaves)
    (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos) (g : Fam (typedOracleFamily lam K L))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (behindSteps sMT sFS Q sh wl nOpen maxDepth embS embE depthReq cms x π own listed rd rdE g ρ
        rts ph).yes =
      (strictBBL sMT sFS Q sh wl depthReq π own listed rd rdE rts ph &&
        (afterBOL Q sh wl nOpen maxDepth embS embE depthReq cms x π rd rdE ρ rts ph).det g) := by
  rw [afterBOL_det]
  refine (and14 _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  exact congrArg₂ and rfl (steps_onF _ _ _ _ _ _ _)

end Letters

section Whole
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **All nine lines say yes just where the description accepts.** -/
theorem acceptSteps_yes (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : _root_.Iop.Tr (chainsOf C D tF tJ t3).sh) :
    (acceptSteps C D tF tJ t3 silent run x y τ).yes =
      (wholeDesc C D tF tJ t3 silent run).accept x y τ := by
  refine (and9 _ _ _ _ _ _ _ _ _).trans ?_
  exact (isSome_ite_unit _).symm

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- **All twenty-three lines say yes just where the verifier along lists says yes behind its
chain**, at a whole file's values. -/
theorem wholeSteps_yes (sMT sFS : ℕ)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) (g : Rom.Fam (typedOracleFamily 256 (K + 1) L))
    (ρ : Rho (chainsOf C D tF tJ t3).sh) (rts : RootsOfChain 256 (chainsOf C D tF tJ t3).sh)
    (ph : Phase 256) :
    (wholeSteps C K chal D tF tJ t3 silent run sMT sFS embS embE depthReq cms x π own listed g ρ
        rts ph).yes =
      (strictBBL sMT sFS (wholeDesc C D tF tJ t3 silent run).batch
          (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) depthReq π own listed
          (rdWhole C D tF tJ t3 ρ) (rdEWhole C D tF tJ t3 ρ) rts ph &&
        (afterBOL (L := L) (wholeDesc C D tF tJ t3 silent run).batch
          (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) (nOpenW D) (maxDepthW D) embS embE depthReq
          cms x π (rdWhole C D tF tJ t3 ρ) (rdEWhole C D tF tJ t3 ρ) ρ rts ph).det g) := by
  unfold wholeSteps Steps.yes
  rw [List.all_append]
  change (Steps.yes _ && Steps.yes _) = _
  rw [behindSteps_yes, acceptSteps_yes, afterBOL_det]
  exact onF_absorb _ _ _ _

end Whole

end OnBytes.Maker

#print axioms OnBytes.Maker.behindSteps_yes
#print axioms OnBytes.Maker.acceptSteps_yes
#print axioms OnBytes.Maker.wholeSteps_yes
