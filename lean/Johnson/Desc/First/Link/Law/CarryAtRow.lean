-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
(The fresh mask's word is a letter z; `FrontFits` has ONE clause on it, `fresh`:
see OpenWordFront.lean.)
Johnson/Desc/First/Link/Law/CarryAtRow.lean: **FROM THE CODE SWITCH's FILES' SENTENCE «carry» AT A
TYPED ROW (`carryRow`, Johnson/Top/H0/K2Caller/CarryK2.lean) TO `CarryAt`
(Johnson/Desc/First/Close/Law/Carry.lean) OF THE TYPED FOLD OF THE TABLE's OWN WORDS**: the first
half of `CarriedAt` (Leads.lean), in the row's own letters. A structure and a theorem. No other
file turns.

  `FrontFits`: ALL THAT IS ASKED OF A FRONT fx AND ITS FRAME W₀, BY NAME: `open_word_eq`'s premises
    (OpenWordEq.lean) and: the closing's names N of the kept slots are the frame's kept places'.
  `carryAt_of_row`: **carryRow r H p orc smp t y · r.rad ≤ e · FrontFits at every front and frame
    that the text makes of t ⊢ there are the front fx and its frame W₀ with CarryAt R N fx.f.rows
    (foldedAt R.Sh.par (readP (h + g) fx.f.rows.gamma) (R.Sh.rho.wd (R.G.word (wordsOf G r.cs r.lo
    seat y))) z)**, R := (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ).keep r.kp:
    AT ANY t₀ · oM · oZ: the switch's files' plain letters (0 · 0 · 0) name the same folded code.
Limits. `FrontFits` IS A PREMISE: none of its clauses is shown at a value. The second half of
`CarriedAt` is not treated. That the closing's own group is this R at the row's numbers is not said.
Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.CarryJoin
import Johnson.Top.H0.K2Caller.CarryK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound (wordsOf)
open VerifiableInference.Desc.First.K2Caller (SwRow KeptSeat carryRow faAt plainD plainR memK rowK
  plK plain_none)
open VerifiableInference.Desc.First.K2Hands (carryOf_claim vecOf)
open VerifiableInference.Desc.First.Close (CarryAt SlotNames foldedAt)

variable (r : SwRow) (H : r.OK) (t₀ e : ℕ) (oM oZ : Fin r.lo.length → ℕ)
  (hM : ∀ i, r.mem i → (r.lo.get i).1.mainRows ≠ 0 → cMain r.cs (r.lo.get i).1 = (stageOf r.g t₀).C)
  (hZ : ∀ i, r.mem i → (r.lo.get i).1.maskRows ≠ 0 → cMask r.cs (r.lo.get i).1 = (stageOf r.g t₀).Z)

local notation "RK" =>
  Johnson.Top.H.Rows.keep (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) r.kp

/-- **ALL THAT IS ASKED OF A FRONT AND ITS FRAME.** -/
structure FrontFits {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ) (Y : Strs)
    (p : First.K2.P2) (t : First.S) (orc : ℕ → ℕ → List UInt64) (no ix : {i // r.mem i} → ℕ)
    (z : (RK).Sh.par.Cw.Word) (N : SlotNames RK) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) :
    Prop where
  good : (RK).Good
  lays : LaysFit RK fx.f.rows.layout ix
  firstZ : ∀ a, (RK).nZ a ≠ 0 →
    fx.f.rows.layout.maskFirst.getD (ix a) none = some ((RK).oZ a)
  masks : fx.f.rows.masks = 2
  gamma : fx.f.rows.gamma.length = (stageOf r.g t₀).h + (stageOf r.g t₀).g
  expK : fx.f.rows.layout.k = (stageOf r.g t₀).h + (stageOf r.g t₀).g
  expH : fx.f.rows.layout.h = (stageOf r.g t₀).h
  member : ∀ a, fx.f.rows.layout.members[ix a]? = some (no a)
  main : ∀ a : {i // r.mem i}, (r.lo.get a.1).1.mainRows ≠ 0 →
    KeptSeat G p t fx orc Y (no a) (r.lo.get a.1).1 (seat a.1)
      (2 ^ (cMain r.cs (r.lo.get a.1).1).a)
  mask : ∀ a : {i // r.mem i}, MaskSeat G p t fx orc Y (no a) (r.lo.get a.1).1 (seat a.1)
    (2 ^ (stageOf r.g t₀).C.a) fun x => x % 2 ^ aOf r.cs (r.lo.get a.1).1
  fresh : ∀ (q : Fin (2 ^ (stageOf r.g t₀).C.a)) (b : Fin (stageOf r.g t₀).h → Bool),
    z q (b, ()) = readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val)
  kept : ∀ κ : (RK).Kp, ∃ k, W₀.kept[r.kept.idxOf κ.1.1.1.val]? = some k ∧ k.old = no κ.1.1 ∧
    κ.2.val < k.rows
  all : ∀ q : Fin (2 ^ (stageOf r.g t₀).C.a), ∃ seg, First.K2.longFront p t fx orc q.val = some seg
  names : ∀ κ : (RK).Kp, N.orc κ = (W₀.kept.getD (r.kept.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).old
  places : ∀ (κ : (RK).Kp) x, N.idx κ x = κ.2.val +
    2 ^ (W₀.kept.getD (r.kept.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).rowBits * x.val

/-- **FROM «carry» AT A TYPED ROW TO CarryAt.** -/
theorem carryAt_of_row {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ) (y : Strs)
    (p : First.K2.P2) (t : First.S) (orc : Strs → ℕ → ℕ → List UInt64)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
    (no ix : {i // r.mem i} → ℕ) (z : (RK).Sh.par.Cw.Word) (N : SlotNames RK) (he : r.rad ≤ e)
    (hF : ∀ fx W₀, First.K2.frontAt p t = some fx → First.K2.frameAt fx = some W₀ →
      FrontFits r t₀ e oM oZ hM hZ G seat y p t (orc y) no ix z N fx W₀)
    (hC : carryRow r H p orc smp t y) :
    ∃ fx W₀, First.K2.frontAt p t = some fx ∧ First.K2.frameAt fx = some W₀ ∧
      CarryAt RK N fx.f.rows
        (foldedAt (RK).Sh.par
          (readP ((stageOf r.g t₀).h + (stageOf r.g t₀).g) fx.f.rows.gamma)
          ((RK).Sh.rho.wd ((RK).G.word (wordsOf G r.cs r.lo seat y))) z) := by
  obtain ⟨fx, W₀, h1, h2, h3⟩ := hC
  have F := hF fx W₀ h1 h2
  refine ⟨fx, W₀, h1, h2, ?_⟩
  have hc := carryOf_claim (plainD r H) (faAt r H p orc smp) _ (a := (t, fx, W₀)) (y := y)
    (w := ()) (τ := readE fx.f.rows.target)
    (v := vecOf (plainR r H).s (plainR r H).Kp fx.f.rows rowK (plK W₀)) rfl h3
  obtain ⟨c, k1, k2⟩ := hc
  have e1 : (First.K2Hands.wordOf (stageOf r.g t₀) (RK).Kp fun q α =>
      readE (((First.K2.longFront p t fx (orc y) q.val).getD #[]).getD
        (First.K2Hands.coordOf (stageOf r.g t₀) (RK).Kp W₀ fx.f.rows
          (fun κ => r.kept.idxOf κ.1.1.1.val) (fun κ => κ.2.val) α) zeroE)) =
      (faAt r H p orc smp (t, fx, W₀) y).2.1.1 := by
    funext pN
    rcases pN with q | q | q
    · funext sy
      obtain ⟨o, ⟨⟩⟩ := sy
      cases o <;> rfl
    · rfl
    · rfl
  have e2 : vecOf (RK).s (RK).Kp fx.f.rows (fun κ => κ.2.val)
      (fun κ => W₀.kept.getD (r.kept.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩) =
      vecOf (plainR r H).s (plainR r H).Kp fx.f.rows rowK (plK W₀) := by
    funext j
    rcases j with ⟨o, x⟩ | x | x
    · cases o <;> rfl
    · rfl
    · rfl
  refine carryAt_of_near RK N fx.f.rows _ _
    (open_word_eq r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ r.kp G seat y p t fx (orc y) no ix
      F.good F.lays F.firstZ F.masks F.gamma F.expK F.expH F.member F.main F.mask z F.fresh h2
      (fun κ => r.kept.idxOf κ.1.1.1.val) F.kept F.all)
    he rfl
    (outVec_eq_vecOf RK N fx.f.rows (fun κ => κ.2.val)
      (fun κ => W₀.kept.getD (r.kept.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩) F.names F.places)
    ⟨c, ?_, ?_⟩
  · rw [e1]
    exact k1
  · rw [e2]
    exact k2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carryAt_of_row
