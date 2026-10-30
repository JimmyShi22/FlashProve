-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
(The fresh mask's word is a letter z with the one clause `fresh`: see
OpenWordFront.lean.)
Johnson/Desc/First/Link/Law/CarryAtFull.lean: `carryAt_of_row` (CarryAtRow.lean) CARRIED FROM THE
CODE SWITCH's TYPED ROW's OWN LETTERS TO THE CLOSING's FILES' GROUP AT THE FULL SIZE
(`groupFullLayK lo hlo gs hgs kb`, Johnson/Desc/First/Close/Law/CornersKept.lean), where the row's
public numbers are that group's. The two kinds' files write «kept» in two ways (a list of numbers; a
flag a message): two predicates, so two types of kept slots: they are laid on one another here,
once. A structure and theorems.

  `FrontFitsAt`: `FrontFits` (CarryAtRow.lean) in general letters: codes cs · list l · members mem ·
    stage s · radius e · corners oM | oZ · kept members kp · the list kl of the kept members'
    numbers in the list.
  `carryAt_kp`: `carryAt_of_row` at any predicate kp that holds just of the row's kept members.
  `carryAt_full`: **r.cs = codesFull2 · r.lo = lo · r.g = gs · (kb i = true ↔ i ∈ r.kept) · r.rad ≤
    radFull · FrontFitsAt at the closing's group's letters, at every front and frame that the text
    makes of t · carryRow r H p orc smp t y ⊢ there are the front fx and its frame W₀ with CarryAt
    (groupFullLayK lo hlo gs hgs kb) N fx.f.rows (foldedAt … z).**
Limits. The five equations on the row's public numbers are premises. `FrontFitsAt` IS A PREMISE,
shown at no value. The first half of `CarriedAt` alone. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.CarryAtRow
import Johnson.Desc.First.Close.Law.CornersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound (wordsOf)
open VerifiableInference.Desc.First.K2Caller (SwRow KeptSeat carryRow plainD)
open VerifiableInference.Desc.First.Close (CarryAt SlotNames foldedAt groupFullLayK layAt sizesM
  sizesZ)

section General
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

local notation "RP" => Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp

/-- **ALL THAT IS ASKED OF A FRONT AND ITS FRAME, IN GENERAL LETTERS.** -/
structure FrontFitsAt (kl : List ℕ) {Xi : Type} (G : FileDescription Xi)
    (seat : Fin l.length → ℕ × ℕ) (Y : Strs) (p : First.K2.P2) (t : First.S)
    (orc : ℕ → ℕ → List UInt64) (no ix : {i // mem i} → ℕ) (z : (RP).Sh.par.Cw.Word)
    (N : SlotNames RP) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) : Prop where
  good : (RP).Good
  lays : LaysFit RP fx.f.rows.layout ix
  firstZ : ∀ a, (RP).nZ a ≠ 0 → fx.f.rows.layout.maskFirst.getD (ix a) none = some ((RP).oZ a)
  masks : fx.f.rows.masks = 2
  gamma : fx.f.rows.gamma.length = s.h + s.g
  expK : fx.f.rows.layout.k = s.h + s.g
  expH : fx.f.rows.layout.h = s.h
  member : ∀ a, fx.f.rows.layout.members[ix a]? = some (no a)
  main : ∀ a : {i // mem i}, (l.get a.1).1.mainRows ≠ 0 →
    KeptSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1) (2 ^ (cMain cs (l.get a.1).1).a)
  mask : ∀ a : {i // mem i}, MaskSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1)
    (2 ^ s.C.a) fun x => x % 2 ^ aOf cs (l.get a.1).1
  fresh : ∀ (q : Fin (2 ^ s.C.a)) (b : Fin s.h → Bool),
    z q (b, ()) = readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val)
  kept : ∀ κ : (RP).Kp, ∃ k, W₀.kept[kl.idxOf κ.1.1.1.val]? = some k ∧ k.old = no κ.1.1 ∧
    κ.2.val < k.rows
  all : ∀ q : Fin (2 ^ s.C.a), ∃ seg, First.K2.longFront p t fx orc q.val = some seg
  names : ∀ κ : (RP).Kp, N.orc κ = (W₀.kept.getD (kl.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).old
  places : ∀ (κ : (RP).Kp) x, N.idx κ x = κ.2.val +
    2 ^ (W₀.kept.getD (kl.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).rowBits * x.val

end General

/-- **AT ANY PREDICATE THAT HOLDS JUST OF THE ROW's KEPT MEMBERS.** -/
theorem carryAt_kp (r : SwRow) (H : r.OK) (t₀ e : ℕ) (oM oZ : Fin r.lo.length → ℕ)
    (hM : ∀ i, r.mem i → (r.lo.get i).1.mainRows ≠ 0 →
      cMain r.cs (r.lo.get i).1 = (stageOf r.g t₀).C)
    (hZ : ∀ i, r.mem i → (r.lo.get i).1.maskRows ≠ 0 →
      cMask r.cs (r.lo.get i).1 = (stageOf r.g t₀).Z)
    (kp : {i // r.mem i} → Prop) [inst : DecidablePred kp] (hkp : ∀ a, kp a ↔ r.kp a)
    {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ) (y : Strs) (p : First.K2.P2)
    (t : First.S) (orc : Strs → ℕ → ℕ → List UInt64)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
    (no ix : {i // r.mem i} → ℕ)
    (z : (Johnson.Top.H.Rows.keep
      (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) kp).Sh.par.Cw.Word)
    (N : SlotNames (Johnson.Top.H.Rows.keep
      (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) kp)) (he : r.rad ≤ e)
    (hF : ∀ fx W₀, First.K2.frontAt p t = some fx → First.K2.frameAt fx = some W₀ →
      FrontFitsAt r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ kp r.kept G seat y p t (orc y) no
        ix z N fx W₀)
    (hC : carryRow r H p orc smp t y) :
    ∃ fx W₀, First.K2.frontAt p t = some fx ∧ First.K2.frameAt fx = some W₀ ∧
      CarryAt (Johnson.Top.H.Rows.keep
          (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) kp) N fx.f.rows
        (foldedAt (Johnson.Top.H.Rows.keep
            (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) kp).Sh.par
          (readP ((stageOf r.g t₀).h + (stageOf r.g t₀).g) fx.f.rows.gamma)
          ((Johnson.Top.H.Rows.keep
            (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) kp).Sh.rho.wd
            ((Johnson.Top.H.Rows.keep
              (rowsPort r.cs r.lo r.mem (stageOf r.g t₀) e oM oZ hM hZ) kp).G.word
              (wordsOf G r.cs r.lo seat y))) z) := by
  obtain rfl : kp = r.kp := funext fun a => propext (hkp a)
  obtain rfl : inst = fun a => inferInstanceAs (Decidable (a.1.val ∈ r.kept)) :=
    Subsingleton.elim _ _
  exact carryAt_of_row r H t₀ e oM oZ hM hZ G seat y p t orc smp no ix z N he
    (fun fx W₀ h1 h2 =>
      have F := hF fx W₀ h1 h2
      ⟨F.good, F.lays, F.firstZ, F.masks, F.gamma, F.expK, F.expH, F.member, F.main, F.mask,
        F.fresh, F.kept, F.all, F.names, F.places⟩) hC

/-- **AT THE CLOSING's FILES' GROUP AT THE FULL SIZE.** -/
theorem carryAt_full (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
    (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool) (r : SwRow) (H : r.OK)
    (hcs : r.cs = codesFull2) (hl : r.lo = lo) (hgr : r.g = gs)
    (hkb : ∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) (he : r.rad ≤ radFull)
    {Xi : Type} (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ) (y : Strs) (p : First.K2.P2)
    (t : First.S) (orc : Strs → ℕ → ℕ → List UInt64)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
    (no ix : {i // memMain lo i} → ℕ) (z : (groupFullLayK lo hlo gs hgs kb).Sh.par.Cw.Word)
    (N : SlotNames (groupFullLayK lo hlo gs hgs kb))
    (hF : ∀ fx W₀, First.K2.frontAt p t = some fx → First.K2.frameAt fx = some W₀ →
      FrontFitsAt codesFull2 lo (memMain lo) (stageOf gs 219) radFull
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        (hMFull lo hlo gs hgs 219) (hZFull lo hlo gs hgs 219) (fun a => kb a.1 = true) r.kept G
        seat y p t (orc y) no ix z N fx W₀)
    (hC : carryRow r H p orc smp t y) :
    ∃ fx W₀, First.K2.frontAt p t = some fx ∧ First.K2.frameAt fx = some W₀ ∧
      CarryAt (groupFullLayK lo hlo gs hgs kb) N fx.f.rows
        (foldedAt (groupFullLayK lo hlo gs hgs kb).Sh.par
          (readP ((stageOf gs 219).h + (stageOf gs 219).g) fx.f.rows.gamma)
          ((groupFullLayK lo hlo gs hgs kb).Sh.rho.wd
            ((groupFullLayK lo hlo gs hgs kb).G.word (wordsOf G codesFull2 lo seat y))) z) := by
  obtain ⟨set, cs', lo', g', rad', l', o', roots', kept', rider'⟩ := r
  dsimp only at hcs hl hgr
  subst hcs hl hgr
  exact carryAt_kp _ H 219 radFull _ _ _ _ (fun a => kb a.1 = true) (fun a => hkb a.1) G seat y p
    t orc smp no ix z N he hF hC

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carryAt_kp
#print axioms VerifiableInference.Desc.LinkJoin.carryAt_full
