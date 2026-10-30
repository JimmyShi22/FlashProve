-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskShellLaws.lean: what the stages of Johnson/RunOne/AskShell.lean return is what the
verifier along lists (verifyWholeL, OnBytes/Maker/ListedWhole.lean) returns, at the runner's own
family of oracle answers and the runner's own test on queries. Proofs.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Main names:
  `runOk_fst`, `runOk_ok`: the runner runOk returns the tree's value at its family, and says whether
    the test has passed every query of that run (Rom.OComp.askedOK, Run/DetAlong.lean).
  `askedOK_bind`: the queries of "first c, then k" are those of c and those of k at c's value.
  `detG_getD`: the run that refuses at the first query which a test turns away (detG,
    OnBytes/Maker/Page/Guard.lean), no value counting as no, says yes just where the test passes
    every query asked and the tree's value is yes.
  `stages_eq`: verifyWholeL is the chain, then strictBBL, then afterBOL, as a tree of queries.
  `behindOf_verdict`: the verdict of behindOf is the value of verifyWholeL at the input's family g.
  `behindOf_written`: "written" says that the input's test passes every query of that run.
  `behindOf_answer`: **"written && verdict" is the guarded run of verifyWholeL** at the input's test
    and family, no value counting as no.
  No premise.
Limits: g and the test are the input's, whatever they are. Of the twenty-three named tests:
wholeSteps_yes (OnBytes/Maker/ListedStepsLaws.lean). Nothing on time or memory. Nothing on
soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskShell
import OnBytes.Maker.Page.Guard
import Run.DetAlong

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Compile hiding ON
open OnBytes.Maker _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ### Trees of queries -/

section Trees
variable {S : OSpec} {α β : Type}

theorem askedOK_bind (g : Fam S) (P : (o : S.ι) → S.Dom o → Bool) (c : OComp S α)
    (k : α → OComp S β) :
    (c.bind k).askedOK g P = (c.askedOK g P && (k (c.det g)).askedOK g P) := by
  induction c with
  | pure a => exact (Bool.true_and _).symm
  | sample n f ih => exact ih 0
  | query o q f ih =>
    exact (congrArg (fun b => P o q && b) (ih (g o q))).trans (Bool.and_assoc _ _ _).symm

theorem detG_getD (ok : (o : S.ι) → S.Dom o → Bool) (g : Fam S) (c : OComp S Bool) :
    (Page.detG ok g c).getD false = (c.askedOK g ok && c.det g) := by
  induction c with
  | pure a => exact (Bool.true_and a).symm
  | sample n k ih => exact ih 0
  | query o q k ih =>
    show (if ok o q = true then Page.detG ok g (k (g o q)) else none).getD false =
      ((ok o q && (k (g o q)).askedOK g ok) && (k (g o q)).det g)
    cases ok o q
    · rfl
    · exact ih (g o q)

end Trees

/-! ### The runner -/

section Runner
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : Nat} {α : Type}
  (ok : (o : OracleName) → domOf 256 L o → Bool) (g : Rom.Fam (typedOracleFamily 256 K L))

/-- **The runner's value is the tree's value at its family.** -/
theorem runOk_fst (c : OComp (typedOracleFamily 256 K L) α) (acc : Array String) (b : Bool) :
    (runOk ok g c acc b).1 = c.det g := by
  induction c generalizing acc b with
  | pure a => rfl
  | query o q k ih => exact ih _ _ _
  | sample n k ih => exact ih 0 _ _

/-- **The runner says whether the test has passed every query of that run.** -/
theorem runOk_ok (c : OComp (typedOracleFamily 256 K L) α) (acc : Array String) (b : Bool) :
    (runOk ok g c acc b).2.2 = (b && c.askedOK g ok) := by
  induction c generalizing acc b with
  | pure a => exact (Bool.and_true b).symm
  | query o q k ih => exact (ih _ _ _).trans (Bool.and_assoc _ _ _)
  | sample n k ih => exact ih 0 _ _

end Runner

/-! ### The stages -/

section Stages
variable {Xi X : Type} (C : _root_.Run.PQ.CK) (D : WholeD) (tF₀ : FrontMsg (List OnBytes.E))
  (tJ₀ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
  (silent : Xi → FrontMsg (List OnBytes.E) →
    _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (rn₀ : Xi → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool) (Kn : Nat)
  (chal : ∀ e k, (Fin Kn → Dig 256) → C.Ch e k) (L : BatchProtocolWithLeafBody Unit X) (t : _root_.Compile.Tag)

/-- What the verifier along lists does behind its chain, at the chain's value. -/
def restOf (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) : ChainVal C D tF₀ tJ₀ → TypedOracleComputation 256 (Kn + 1) L Bool
  | none => pure false
  | some (ρ, rts, ph) =>
    if strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph then
      afterAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) ρ rts ph
    else pure false

/-- **The verifier along lists is the chain, then strictBBL, then afterBOL.** -/
theorem stages_eq (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) :
    (verifyWholeL (L := L) C Kn chal D tF₀ tJ₀ ByteArray.empty silent rn₀
        A.sMT A.sFS t A.eS A.embP (fun _ => A.xo) A.eE A.dR A.cms A.x A.π A.own A.listed) =
      (chainTree C D tF₀ tJ₀ silent rn₀ Kn chal L t A).bind
        (restOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A) := by
  unfold verifyWholeL verifyBSL chainTree
  congr 1
  funext r
  rcases r with _ | ⟨ρ, rts, ph⟩ <;> rfl

theorem ran_ok {α : Type} (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) (c : TypedOracleComputation 256 (Kn + 1) L α) :
    (runOk A.ok A.g c #[] true).2.2 = c.askedOK A.g A.ok :=
  (runOk_ok A.ok A.g c #[] true).trans (Bool.true_and _)

/-- The verdict behind a run of the chain is the value of what the verifier does behind it. -/
theorem behindAt_verdict (A : In C D tF₀ tJ₀ silent rn₀ Kn L t)
    (r7 : ChainVal C D tF₀ tJ₀ × Array String × Bool) :
    (behindAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A r7).verdict =
      (restOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A r7.1).det A.g := by
  rcases r7 with ⟨_ | ⟨ρ, rts, ph⟩, log, b⟩
  · rfl
  · show (true &&
        strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph &&
        (runOk A.ok A.g
          (afterAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) ρ rts ph)
          #[] true).1) =
      (if strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph = true then
        afterAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) ρ rts ph
      else pure false).det A.g
    rw [runOk_fst]
    cases strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph <;> rfl

/-- "written" behind a run of the chain: the chain's flag, and the queries of what the verifier does
behind it. -/
theorem behindAt_written (A : In C D tF₀ tJ₀ silent rn₀ Kn L t)
    (r7 : ChainVal C D tF₀ tJ₀ × Array String × Bool) :
    (behindAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A r7).written =
      (r7.2.2 && (restOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A r7.1).askedOK A.g A.ok) := by
  rcases r7 with ⟨_ | ⟨ρ, rts, ph⟩, log, b⟩
  · rfl
  · show (b &&
        (!strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph ||
        (runOk A.ok A.g
          (afterAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) ρ rts ph)
          #[] true).2.2)) =
      (b && (if strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph = true then
        afterAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) ρ rts ph
      else pure false).askedOK A.g A.ok)
    rw [ran_ok]
    cases strictAt C D tF₀ tJ₀ silent rn₀ Kn chal L t A (rdAt C D tF₀ tJ₀ ρ)
          (rdEAt C D tF₀ tJ₀ ρ) rts ph <;> rfl

/-- **The stages' verdict is the value of the verifier along lists at the input's family.** -/
theorem behindOf_verdict (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) :
    (behindOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A).verdict =
      (verifyWholeL (L := L) C Kn chal D tF₀ tJ₀ ByteArray.empty silent rn₀
        A.sMT A.sFS t A.eS A.embP (fun _ => A.xo) A.eE A.dR A.cms A.x A.π A.own A.listed).det
        A.g := by
  rw [stages_eq, OComp.det_bind,
    ← runOk_fst A.ok A.g (chainTree C D tF₀ tJ₀ silent rn₀ Kn chal L t A) #[] true]
  exact behindAt_verdict C D tF₀ tJ₀ silent rn₀ Kn chal L t A _

/-- **"written" says that the input's test passes every query that the verifier along lists asks.**
-/
theorem behindOf_written (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) :
    (behindOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A).written =
      (verifyWholeL (L := L) C Kn chal D tF₀ tJ₀ ByteArray.empty silent rn₀
        A.sMT A.sFS t A.eS A.embP (fun _ => A.xo) A.eE A.dR A.cms A.x A.π A.own A.listed).askedOK
        A.g A.ok := by
  rw [stages_eq, askedOK_bind,
    ← runOk_fst A.ok A.g (chainTree C D tF₀ tJ₀ silent rn₀ Kn chal L t A) #[] true,
    ← ran_ok C D tF₀ tJ₀ silent rn₀ Kn L t A (chainTree C D tF₀ tJ₀ silent rn₀ Kn chal L t A)]
  exact behindAt_written C D tF₀ tJ₀ silent rn₀ Kn chal L t A _

/-- **"written && verdict" is the guarded run of the verifier along lists**, at the input's test and
family; no value counts as no. -/
theorem behindOf_answer (A : In C D tF₀ tJ₀ silent rn₀ Kn L t) :
    ((behindOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A).written &&
        (behindOf C D tF₀ tJ₀ silent rn₀ Kn chal L t A).verdict) =
      (Page.detG (S := typedOracleFamily 256 (Kn + 1) L) A.ok A.g
        (verifyWholeL (L := L) C Kn chal D tF₀ tJ₀ ByteArray.empty silent rn₀
        A.sMT A.sFS t A.eS A.embP (fun _ => A.xo) A.eE A.dR A.cms A.x A.π A.own A.listed)).getD
        false := by
  rw [detG_getD, behindOf_written, behindOf_verdict]

end Stages

end Johnson.RunOne.Ask

#print axioms Johnson.RunOne.Ask.runOk_fst
#print axioms Johnson.RunOne.Ask.runOk_ok
#print axioms Johnson.RunOne.Ask.behindOf_verdict
#print axioms Johnson.RunOne.Ask.behindOf_written
#print axioms Johnson.RunOne.Ask.behindOf_answer
