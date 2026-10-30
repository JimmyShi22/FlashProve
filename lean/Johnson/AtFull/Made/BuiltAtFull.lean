-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/BuiltAtFull.lean: `buildLinksH` RETURNS AT THE FULL SIZE: the premise h₁ of
`madeAt_of_parts` (Johnson/AtFull/Made/Ledger.lean) FROM: the three first steps' returns (the
ledger's a₂, a₃, a₄); TWO EQUATIONS ON WHAT `declareLinks` RETURNED (its entries' views and what
is declared are the written ones); one number of the public parameters; the committed table's
layout as `wsLayOf` returns it; EIGHT EQUATIONS ON THE FIRST CHAIN's PARAMETERS AS READ BACK; and
one closed fact, `linksFit` at the written views, which LinksFitFull.lean decides.
Ten theorems: joinings of Johnson/AtFull/Made/BuiltOfParts.lean, LinksView.lean and
LinksFull.lean.
  `held_at`, `rows_at`, `ws_parts`, `limbs_at`, `tableHeld_at`, `reqOk_at`, `listed_at`, `fit_at`,
    `numbers_at`: the eight tests h₄ to h₁₁, each from just the equations on what it reads.
    `built_at_full`: the end.
WHICH OF THE ELEVEN STEPS ARE CLOSED HERE. Of `buildLinksH_of_parts`' eleven premises: THREE ARE
TAKEN AS THEY ARE (a₂, a₃, a₄: shown elsewhere) · SEVEN ARE BROUGHT TO EQUATIONS ON WRITTEN VALUES,
their conditions decided by Lean's kernel or needing no decision (h₄, h₅, h₆, h₇, h₈, h₁₁ by the
kernel in LinksFull.lean; h₉: no position is listed) · ONE IS BROUGHT TO ANOTHER FILE's CLOSED FACT
(h₁₀: hF). So the file closes no step outright: each of the seven still hangs on its equations.
WHAT IT READS OF THE PUBLIC PARAMETERS X: NGr, p4 (in a₄) and layers.wsLay: nothing else. No
spelled-out X stands anywhere.
Limits. THE EQUATIONS ARE HYPOTHESES: hv and hd are owed by whoever shows `declareLinks`' return
(one closed return gives both); hY by the public parameters' own make (in the goals' scope:
`args_at_scope`, Johnson/Goal/PlanValues/KeyArgsAtScope.lean [not in this library]); p₁ to p₈ by whoever shows what
`ProofChains.read` returns. WHAT A RUN HAS SEEN AT `VerifierAndGoals.storedPublicFiles` (an evaluation, no theorem): hv,
hd, hN and p₁ to p₈ true AS EQUATIONS (a code has just the three numbers that the run compares);
OF hY LESS: the two layouts have one lk, one m0 and, unit by unit, six numbers in common: THE
UNITS' INDEX GROUPS WERE NOT COMPARED; hF: the test accepts. No soundness is claimed.

-/
import Johnson.AtFull.Made.BuiltOfParts
import Johnson.AtFull.Made.LinksFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (layoutFull proofCodesWritten)

/-- **h₄.** -/
theorem held_at {declared : Array FrameLink} {p : Params.First} (hd : declared = declaredFull)
    (p₂ : p.shape = shapeFull) (p₃ : p.layout = layoutFull) : heldAgainst declared p = .ok () := by
  have e : heldAgainst declared p =
      if heldB declared p.shape p.layout then pure () else throw "plan-layout" := rfl
  rw [e, hd, p₂, p₃, heldB_full]
  rfl

/-- **h₅.** -/
theorem rows_at {links : Array LinkH} {NGr : Nat}
    (hv : links.toList.map Johnson.AtFull.Made.viewOf = viewFull) (hN : NGr = 12) :
    tableRows links NGr = .ok () := by
  subst hN
  exact (tableRows_narrow links 12).symm.trans
    ((congrArg (fun a => tableRows a 12) (narrow_of_views hv)).trans tableRows_full)

/-- What the test on the committed table's layout gives. -/
theorem ws_parts {Y : WsLay}
    (hY : wsLayOf Lk6.AtPlan.wsFull true recordLines.blockLog = .ok Y) :
    (Y.U.any fun u => u.nlw == 4 && u.X != 12) = false ∧ wfLayoutOk Y = true ∧
      Y.m0 = 3076096 ∧ Y.lk = 18 := by
  have h := wsTests_full
  unfold wsTests at h
  rw [hY] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2.symm, h.2.symm⟩

/-- **h₆.** -/
theorem limbs_at {Y : WsLay}
    (hY : wsLayOf Lk6.AtPlan.wsFull true recordLines.blockLog = .ok Y) :
    weightLimbs Y = .ok () := by
  obtain ⟨h1, h2, -, -⟩ := ws_parts hY
  unfold weightLimbs
  rw [h1, h2]
  rfl

/-- **h₇.** -/
theorem tableHeld_at {Y : WsLay} {p : Params.First}
    (hY : wsLayOf Lk6.AtPlan.wsFull true recordLines.blockLog = .ok Y)
    (p₄ : p.lin.matrixRows = 3076096) (p₅ : p.lin.kCol = 18) :
    Stages.tableHeld Y p = .ok () := by
  obtain ⟨-, -, h3, h4⟩ := ws_parts hY
  unfold Stages.tableHeld
  rw [p₄, p₅, h3, h4]
  rfl

/-- **h₈.** -/
theorem reqOk_at {p : Params.First} (p₁ : p.codes = proofCodesWritten) (p₂ : p.shape = shapeFull) :
    reqOk p.codes p.shape = true := by
  rw [p₁, p₂]
  exact reqOk_full

/-- **h₉**: no position is listed. -/
theorem listed_at {p : Params.First} (p₈ : p.given.plan.posB = 0) : listedFits p = .ok () := by
  unfold listedFits
  simp only [p₈]
  rfl

/-- **h₁₀**, from the closed fact at the written views. -/
theorem fit_at {links : Array LinkH} {p : Params.First}
    (hv : links.toList.map Johnson.AtFull.Made.viewOf = viewFull)
    (p₁ : p.codes = proofCodesWritten) (p₂ : p.shape = shapeFull) (p₃ : p.layout = layoutFull)
    (p₅ : p.lin.kCol = 18)
    (hF : linksFit (viewFull.map ofView).toArray proofCodesWritten shapeFull layoutFull 18 =
      .ok ()) :
    linksFit links p.codes p.shape p.layout p.lin.kCol = .ok () := by
  rw [p₁, p₂, p₃, p₅, (tests_at_view hv 0 p proofCodesWritten shapeFull layoutFull 18).2.2]
  exact hF

/-- **h₁₁.** -/
theorem numbers_at {links : Array LinkH} {p : Params.First}
    (hv : links.toList.map Johnson.AtFull.Made.viewOf = viewFull) (p₂ : p.shape = shapeFull)
    (p₆ : p.pendingRows = 13) (p₇ : p.identifiers = idsFull) : numbersHeld links p = .ok () := by
  rw [(tests_at_view hv 0 p p.codes p.shape p.layout 0).2.1]
  have e : numbersHeld (viewFull.map ofView).toArray p =
      if numbersB (viewFull.map ofView).toArray p.shape p.pendingRows p.identifiers then pure ()
      else throw "parameters-not-admitted" := rfl
  rw [e, p₂, p₆, p₇, numbersB_full]
  rfl

/-- **`buildLinksH` RETURNS AT THE FULL SIZE**: the ledger's h₁ at built := { links := links }. -/
theorem built_at_full {X : Public} {chains : Chains} {links₀ links : Array LinkH}
    {declared : Array FrameLink}
    (a₂ : headLast links₀ = .ok ()) (a₃ : linksCount links₀ = .ok ())
    (a₄ : declareLinks links₀ X.NGr X.p4 = .ok (links, declared))
    (hv : links.toList.map Johnson.AtFull.Made.viewOf = viewFull) (hd : declared = declaredFull)
    (hN : X.NGr = 12)
    (hY : wsLayOf Lk6.AtPlan.wsFull true recordLines.blockLog = .ok X.layers.wsLay)
    (p₁ : chains.proof.first.codes = proofCodesWritten)
    (p₂ : chains.proof.first.shape = shapeFull) (p₃ : chains.proof.first.layout = layoutFull)
    (p₄ : chains.proof.first.lin.matrixRows = 3076096) (p₅ : chains.proof.first.lin.kCol = 18)
    (p₆ : chains.proof.first.pendingRows = 13) (p₇ : chains.proof.first.identifiers = idsFull)
    (p₈ : chains.proof.first.given.plan.posB = 0)
    (hF : linksFit (viewFull.map ofView).toArray proofCodesWritten shapeFull layoutFull 18 =
      .ok ()) :
    buildLinksH links₀ X.NGr X.p4 X.layers.wsLay chains.proof.first = .ok { links := links } :=
  built_of_parts a₂ a₃ a₄ (held_at hd p₂ p₃) (rows_at hv hN) (limbs_at hY)
    (tableHeld_at hY p₄ p₅) (reqOk_at p₁ p₂) (listed_at p₈) (fit_at hv p₁ p₂ p₃ p₅ hF)
    (numbers_at hv p₂ p₆ p₇)

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.held_at
#print axioms Johnson.AtFull.Made.rows_at
#print axioms Johnson.AtFull.Made.ws_parts
#print axioms Johnson.AtFull.Made.limbs_at
#print axioms Johnson.AtFull.Made.tableHeld_at
#print axioms Johnson.AtFull.Made.reqOk_at
#print axioms Johnson.AtFull.Made.listed_at
#print axioms Johnson.AtFull.Made.fit_at
#print axioms Johnson.AtFull.Made.numbers_at
#print axioms Johnson.AtFull.Made.built_at_full
