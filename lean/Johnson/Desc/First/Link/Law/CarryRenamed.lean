-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CarryRenamed.lean: `carryAt_of_row` (CarryAtRow.lean) WHERE THE
CLOSING's FILES TYPE THE GROUP OVER ANOTHER LIST THAN THE CODE SWITCH's TYPED ROW DOES (at the
first link the row's list has a message that is no member of the group; the closing's list may
leave it out): from
`carryRow r …` to `CarryAt R' …` at R' := (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ).keep
kp', given a bijection of the two types of kept slots that keeps a slot's member's number in the
list and its row. By `near_rename` (KeptRename.lean), `open_word_eq` (OpenWordEq.lean: general in
the list) and `outVec_eq_vecOf` (CarryVecs.lean). A theorem.

  `carryAt_renamed`: **carryRow r H p orc smp t y · r.rad ≤ e · φ : ‹the row's kept slots› ≃ R'.Kp
    with (φ κ)'s member's number = κ's and (φ κ)'s row = κ's · FrontFitsAt at R''s letters and
    r.kept, at every front and frame that the text makes of t ⊢ there are the front fx and its
    frame W₀ with CarryAt R' N fx.f.rows (foldedAt R'.Sh.par (readP (h + g) fx.f.rows.gamma)
    (R'.Sh.rho.wd (R'.G.word (wordsOf G cs' l' seat y))) z).** NOTHING TIES cs' · l' · mem' · kp' TO
    THE ROW BUT φ AND FrontFitsAt.
Limits. `FrontFitsAt` IS A PREMISE, shown at no value; so is φ. The first half of `CarriedAt` alone.
Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.CarryAtFull
import Johnson.Desc.First.Link.Law.KeptRename

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound (wordsOf)
open VerifiableInference.Desc.First.K2Caller (SwRow carryRow faAt plainD plainR memK rowK plK)
open VerifiableInference.Desc.First.K2Hands (carryOf_claim vecOf coordOf)
open VerifiableInference.Desc.First.Close (CarryAt SlotNames foldedAt)

theorem carryAt_renamed (r : SwRow) (H : r.OK) (cs' : OnBytes.Codes)
    (l' : List (OnBytes.OracleShape × ℕ)) (mem' : Fin l'.length → Prop) [DecidablePred mem']
    (t₀ e : ℕ) (oM oZ : Fin l'.length → ℕ)
    (hM : ∀ i, mem' i → (l'.get i).1.mainRows ≠ 0 → cMain cs' (l'.get i).1 = (stageOf r.g t₀).C)
    (hZ : ∀ i, mem' i → (l'.get i).1.maskRows ≠ 0 → cMask cs' (l'.get i).1 = (stageOf r.g t₀).Z)
    (kp' : {i // mem' i} → Prop) [DecidablePred kp']
    (φ : (plainR r H).Kp ≃ (Johnson.Top.H.Rows.keep
      (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp').Kp)
    (hφ : ∀ κ, (φ κ).1.1.1.val = κ.1.1.1.val ∧ (φ κ).2.val = κ.2.val)
    {Xi : Type} (G : FileDescription Xi) (seat : Fin l'.length → ℕ × ℕ) (y : Strs) (p : First.K2.P2)
    (t : First.S) (orc : Strs → ℕ → ℕ → List UInt64)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
    (no ix : {i // mem' i} → ℕ)
    (z : (Johnson.Top.H.Rows.keep
      (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp').Sh.par.Cw.Word)
    (N : SlotNames (Johnson.Top.H.Rows.keep
      (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp')) (he : r.rad ≤ e)
    (hF : ∀ fx W₀, First.K2.frontAt p t = some fx → First.K2.frameAt fx = some W₀ →
      FrontFitsAt cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ kp' r.kept G seat y p t (orc y) no ix
        z N fx W₀)
    (hC : carryRow r H p orc smp t y) :
    ∃ fx W₀, First.K2.frontAt p t = some fx ∧ First.K2.frameAt fx = some W₀ ∧
      CarryAt (Johnson.Top.H.Rows.keep
          (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp') N fx.f.rows
        (foldedAt (Johnson.Top.H.Rows.keep
            (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp').Sh.par
          (readP ((stageOf r.g t₀).h + (stageOf r.g t₀).g) fx.f.rows.gamma)
          ((Johnson.Top.H.Rows.keep
            (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp').Sh.rho.wd
            ((Johnson.Top.H.Rows.keep
              (rowsPort cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ) kp').G.word
              (wordsOf G cs' l' seat y))) z) := by
  obtain ⟨fx, W₀, h1, h2, h3⟩ := hC
  have F := hF fx W₀ h1 h2
  refine ⟨fx, W₀, h1, h2, ?_⟩
  have hc := carryOf_claim (plainD r H) (faAt r H p orc smp) _ (a := (t, fx, W₀)) (y := y)
    (w := ()) (τ := readE fx.f.rows.target)
    (v := vecOf (plainR r H).s (plainR r H).Kp fx.f.rows rowK (plK W₀)) rfl h3
  obtain ⟨c', k1, k2⟩ := near_rename (plainR r H).s φ
    (fun q α => readE (((First.K2.longFront p t fx (orc y) q.val).getD #[]).getD
      (coordOf (plainR r H).s (plainR r H).Kp W₀ fx.f.rows memK rowK α) zeroE))
    (vecOf (plainR r H).s (plainR r H).Kp fx.f.rows rowK (plK W₀)) (readE fx.f.rows.target) r.rad
    hc
  have hs : ∀ κ', (φ.symm κ').1.1.1.val = κ'.1.1.1.val ∧ (φ.symm κ').2.val = κ'.2.val :=
    fun κ' => by
      have := hφ (φ.symm κ')
      rw [Equiv.apply_symm_apply] at this
      exact ⟨this.1.symm, this.2.symm⟩
  refine carryAt_of_near _ N fx.f.rows _ _
    (open_word_eq cs' l' mem' (stageOf r.g t₀) e oM oZ hM hZ kp' G seat y p t fx (orc y) no ix
      F.good F.lays F.firstZ F.masks F.gamma F.expK F.expH F.member F.main F.mask z F.fresh h2
      (fun κ => r.kept.idxOf κ.1.1.1.val) F.kept F.all)
    he rfl
    (outVec_eq_vecOf _ N fx.f.rows (fun κ => κ.2.val)
      (fun κ => W₀.kept.getD (r.kept.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩) F.names F.places)
    ⟨c', ?_, ?_⟩
  · refine Nat.le_trans (Nat.le_of_eq ?_) k1
    congr 1
    funext pN
    rcases pN with q | q | q
    · funext sy
      obtain ⟨o, ⟨⟩⟩ := sy
      cases o with
      | none => rfl
      | some κ' =>
        show readE (((First.K2.longFront p t fx (orc y) q.val).getD #[]).getD
            (1 + (First.K2Hands.rowsBefore W₀.kept (r.kept.idxOf κ'.1.1.1.val) + κ'.2.val))
            zeroE) =
          readE (((First.K2.longFront p t fx (orc y) q.val).getD #[]).getD
            (1 + (First.K2Hands.rowsBefore W₀.kept (r.kept.idxOf (φ.symm κ').1.1.1.val) +
              (φ.symm κ').2.val)) zeroE)
        rw [(hs κ').1, (hs κ').2]
    · rfl
    · rfl
  · rw [← k2]
    refine Finset.sum_congr rfl fun j' _ => ?_
    congr 1
    rcases j' with ⟨o, x⟩ | x | x
    · cases o with
      | none => rfl
      | some κ' =>
        show (fx.f.rows.kept.toList.map fun f =>
            if (W₀.kept.getD (r.kept.idxOf κ'.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).old = f.oracle then
              formAt f.c (κ'.2.val +
                2 ^ (W₀.kept.getD (r.kept.idxOf κ'.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).rowBits * x.val)
            else 0).sum =
          (fx.f.rows.kept.toList.map fun f =>
            if (W₀.kept.getD (r.kept.idxOf (φ.symm κ').1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).old =
                f.oracle then
              formAt f.c ((φ.symm κ').2.val +
                2 ^ (W₀.kept.getD (r.kept.idxOf (φ.symm κ').1.1.1.val)
                  ⟨0, 0, 0, 0, [], 0⟩).rowBits * x.val)
            else 0).sum
        rw [(hs κ').1, (hs κ').2]
    · rfl
    · rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carryAt_renamed
