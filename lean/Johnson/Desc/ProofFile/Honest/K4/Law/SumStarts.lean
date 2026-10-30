-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumStarts.lean: CONDITIONAL.

What is here. THE START AT TWO PRODUCT LEVELS OF THE FEED-FORWARD LAYERS' ROUNDS: the verifier's
start form is worth the reading of the total of a cube in the honest job's form. Both statements
stand at ANY table or tables, ANY number of variables and ANY arrays: no public data, input or maker
is named; the tie to the makers is the callers' (`start_squares`, `start_gated2`,
Law/W/StartsAt.lean). The squares: `normsStart`'s form. The second gated product: `start2`. Each by
two laws that end in one extension: on the form's worth (Johnson/Road/K4/W/Starts.lean, Gated.lean)
and on the total (SumTotalExt.lean beside this file). Statements and proofs.

  `squares_sigma`   **the squares**
  `gated2_sigma`   **the second gated product**

Limits. THE HONEST TABLES' ENTRIES READ AS THE LIBRARY's TERMS AT THE CELLS t: A PREMISE (htab),
shown nowhere here. THE WORLD's SLOTS HOLD THE LIBRARY's SUMS: a premise (hW; hS). The plan's number
of variables is the library's sum of three: a premise. The other premises are those of the two laws
that are called: the batching's powers, the half, public numbers and sizes. THE SQUARES' START
STANDS ONLY AT PLANS WITH xl = 5 (hNS: 2 xl - 1 = 9). The first gated product's start form is one
slot: nothing is to be shown of it but what that slot holds. At every reading into a field, in every
world, at all cells. No example of the premises is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumTotalExt
import Johnson.Road.K4.W.Starts
import Johnson.Road.K4.W.Gated

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE invE)
open OnBytes.Model (Reading World ledNS ofNat)
open OnBytes.Model.Layer (Lay downFrom normsStart)
open OnBytes.Road (pt eqR)
open OnBytes.Road.Rows (start2 hvOf)
open OnBytes.Road.K4.W (squares_start gated2_start)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell lFe slV' upV')
open OnBytes.Desc.First.K4 (dataFF)
open OnBytes.Desc.First.K4.Honest

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {t : Cell → K} [scl : Scl] {D : Dim}

/-- **The squares' start form is worth the reading of the total of the squares' cube.** tab: the
honest table. gam: the batching element. -/
theorem squares_sigma (y : Lay) (sW mu : ℕ) (gp rhoI PV : Array E) (lNI : ℕ) (gam : K) (tab : Tab)
    (hNS : ledNS y.h.xl = 9) (hNI : y.NI = D.nNu) (hhalf : ρ.val (invE (ofNat 2)) * 2 = 1)
    (hsz : rhoI.size = lNI) (hPV : PV.size = D.lT) (hmu : mu = lNI + y.lPd + D.lT)
    (hN : D.nNu ≤ 2 ^ lNI) (hd : D.d ≤ 2 ^ y.lPd)
    (hgp : ∀ s, s < 9 → ρ.val (gp.getD s zeroE) = gam ^ s)
    (hW : ∀ ν, ν < D.nNu → ∀ s, s < 9 →
      W.slot (sW + 9 * ν + s) = OnBytes.Road.wHat D t ν (pt ρ PV) s)
    (htab : ∀ X, X < 2 ^ mu → ρ.val (tab.getD X zeroE) = (dataFF D t lNI).sqTab y.lPd gam X) :
    (normsStart y sW gp rhoI PV).1.value ρ W =
      ρ.val (sqJobOf mu (normsStart y 0 gp rhoI PV).2 tab).cube.total := by
  have hs : (normsStart y 0 gp rhoI PV).2.size = mu := by
    show (rhoI ++ Array.replicate y.lPd _ ++ PV).size = mu
    rw [Array.size_append, Array.size_append, Array.size_replicate, hsz, hPV, hmu]
  rw [sq_total_ext ρ mu _ tab hs,
    squares_start (uP := pt ρ PV) y sW gp rhoI PV lNI gam (pt ρ (normsStart y 0 gp rhoI PV).2) hNS
      hNI hhalf hsz hN hd hgp
      (fun j hj => squares_pt_first ρ y 0 gp rhoI PV j (by rw [hsz]; exact hj))
      (fun j hj => by rw [← hsz]; exact squares_pt_half ρ y 0 gp rhoI PV j hj)
      (fun j _ => by rw [← hsz]; exact squares_pt_last ρ y 0 gp rhoI PV j) hW, ← hmu]
  exact Blocks.ext_congr (fun X hX => by rw [htab X hX]) _

omit scl in
/-- **The second gated product's start form is worth the reading of the total of its cube.** tb: the
two honest tables. -/
theorem gated2_sigma {rs rt rhoM : Array E} {u : ℕ → K} {sH1 LamM lfe : ℕ} (mu : ℕ)
    (order : List ℕ) (tb : Tab × Tab) (hlfe : lfe = lFe D) (hle : lfe ≤ rs.size)
    (hrho : rhoM.size = D.lL - 1) (hrt : rt.size = D.lT) (hLam : LamM = 2 ^ (D.lL - 1))
    (hmu : mu = D.lL - 1 + lFe D + D.lT)
    (hS : ∀ lm, lm < LamM → W.slot (sH1 + 1 + lm) =
      ∑ yv ∈ Finset.range (2 ^ lfe), eqR ρ rs 0 lfe yv * hvOf D t u (pt ρ rt) (1 + lm) yv)
    (htab : ∀ X, X < 2 ^ mu → ρ.val (tb.1.getD X zeroE) = slV' D t X ∧
      ρ.val (tb.2.getD X zeroE) = upV' D t X) :
    (start2 LamM sH1 rhoM).value ρ W =
      ρ.val (levelJob mu order (rhoM ++ downFrom rs lfe ++ rt) tb).cube.total := by
  have hs : (rhoM ++ downFrom rs lfe ++ rt).size = mu := by
    rw [Array.size_append, Array.size_append, hrho, hrt, hmu, ← hlfe]
    simp only [downFrom, Array.size_reverse, Array.size_extract]
    omega
  rw [level_total_ext ρ mu order _ tb hs, gated2_start hlfe hle hrho hLam hS, ← hmu]
  exact Blocks.ext_congr (fun X hX => by rw [(htab X hX).1, (htab X hX).2]) _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.squares_sigma
#print axioms ProofFile.Honest.K4.gated2_sigma
