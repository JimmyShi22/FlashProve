-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.ChainJoh
import Johnson.Desc.K12.Law.BatPriceOk
/-
Johnson/Desc/K12/Law/PayPub.lean: THE PUBLIC HALF OF WHAT THE PAYER OF THE BATCHING's CONVERSE ASKS,
AND ITS PAYMENT FROM TESTS WITH CODE. NO SOUNDNESS IS
CLAIMED. NOTHING ON HIDING.
  PayPub π rad rows v₀   of the plan's first stage a: StageJ at the radius (the facts on codes) · lstJ (radius) * (rows − 1) ≤ v₀
  lstJB_eq       the native bound on the list (Johnson/Desc/K12/Law/SmallOk.lean) IS the library's Sg.lstJ at the stage in the library's form
  geoB_eq … wOfB_eq   the native number w (Johnson/Desc/K12/Law/BatPriceOk.lean) IS the w of the format's block sampler at the second field: (bsOf .two ds).w
  payPub_of_joh  johOk p r = true · the radius letter is r · the plan's first written round is w0
    ⇒ PayPub p rad w0.entry.rows (batV0 p r): AT v₀ := batV0 THE NUMBER's CLAUSE HOLDS WITH EQUALITY
WHAT IT DOES NOT SAY: that e₀ := v₀ * w is small against the round's verifier messages: that is
batPriceOk's comparison, a run's; its law towards the library's RoundBelow (the number of a written
round's verifier messages is chalsB) is owed · johOk's yes is a run's word.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by
decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (Stage)

/-- What the payer asks that is public: of the plan's first stage and "BAT"'s number of rows. -/
def PayPub (π : P12) (rad : Sg → ℕ) (rows v₀ : ℕ) : Prop :=
  ∀ (a : Stage) (rest : List Stage), π.nums.stages = a :: rest →
    (sgOf a).StageJ (rad (sgOf a)) ∧ (sgOf a).lstJ (rad (sgOf a)) * (rows - 1) ≤ v₀

theorem lstJB_eq (a : Stage) (e : ℕ) : lstJB (stN a) e = (sgOf a).lstJ e := rfl

theorem geoB_eq (F T : ℕ) : ∀ n, geoB F T n = geo F T n
  | 0 => rfl
  | n + 1 => by
    show T ^ n + F * geoB F T n = T ^ n + F * geo F T n
    rw [geoB_eq F T n]

theorem w0B_eq (m f Q : ℕ) : w0B m f Q = w0 m f Q := by
  unfold w0B w0
  rw [geoB_eq]

theorem wNB_eq (m f Q : ℕ) : wNB m f Q = wN m f Q := by
  unfold wNB wN wxB wx
  rw [w0B_eq, geoB_eq]

theorem wtB_eq : ∀ d : Fmt.Draw, wtB d = wt .two d
  | .elem => by
    show w0B 1 (2 ^ 32 - 1) (2 ^ 64) ^ 3 = w0 1 (2 ^ 32 - 1) (2 ^ 64) ^ 3
    rw [w0B_eq]
  | .elemNZ => wNB_eq _ _ _
  | .pos _ => rfl
  | .trits _ => rfl
  | .sealed => rfl

theorem wtAllB_eq : ∀ ds : List Fmt.Draw, wtAllB ds = wtAll .two ds
  | [] => rfl
  | d :: ds => by
    show wtB d * wtAllB ds = wt .two d * wtAll .two ds
    rw [wtB_eq, wtAllB_eq ds]

theorem wOfB_eq (ds : List Fmt.Draw) : wOfB ds = (bsOf .two ds).w := by
  show wtAllB ds * (2 ^ 64) ^ (4 * ((Fmt.mostAll ds + 3) / 4) - Fmt.mostAll ds) =
    wtAll .two ds * (2 ^ 64) ^ (4 * ((Fmt.mostAll ds + 3) / 4) - Fmt.mostAll ds)
  rw [wtAllB_eq]


theorem payPub_of_joh (p : P12) (r : Stage → ℕ) (rad : Sg → ℕ) (hr : ∀ s, rad s = r s.st)
    (hj : johOk p r = true) (w0 : WR) (l : List WR) (hw : writtenOf p.nums = some (w0 :: l)) :
    PayPub p rad w0.entry.rows (batV0 p r) := by
  intro a rest hs
  unfold johOk johAll at hj
  rw [hs] at hj
  unfold johWalk at hj
  rw [ok_append, ok_tag, Bool.and_eq_true] at hj
  refine ⟨by rw [hr]; exact stageJ_of_L hj.1, ?_⟩
  have hv : batV0 p r = lstJB (stN a) (r (stN a)) * (w0.entry.rows - 1) := by
    unfold batV0 batAtB
    rw [hs, hw]
    rfl
  rw [hv, hr, lstJB_eq]
  exact le_refl _

end H2K.Pub

#print axioms H2K.Pub.lstJB_eq
#print axioms H2K.Pub.wOfB_eq
#print axioms H2K.Pub.payPub_of_joh
