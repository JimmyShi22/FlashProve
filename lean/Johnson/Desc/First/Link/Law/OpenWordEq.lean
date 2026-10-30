-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
(The fresh mask's word is a letter z with the one clause hz, as in OpenWordFront.lean.)

Johnson/Desc/First/Link/Law/OpenWordEq.lean: **THE OPEN WORD THAT THE CODE SWITCH's FILES MAKE OFF
WHAT THEIR TEXT READS (`wordOf` of `K2.longFront`: Johnson/Top/H0/K2Hands/StrMade.lean,
K2Caller/CarryK2.lean's faAt) IS THE CLOSING's FILES' TYPED FOLD OF THE TABLE's OWN WORDS, ARRANGED
(`foldedAt`: Johnson/Desc/First/Close/Law/Carry.lean, Leads.lean's CarriedAt): AN EQUATION OF
WORDS.** The debt that StrMade.lean's head names («whoever closes the block in front owes it AT
THIS STRING»). Theorems. No text already in the library turns.

  `kept_front`: the typed folded word's slot κ at the position q is, read in the field, what the
    front reads at the kept row's place 1 + (rowsBefore W₀.kept (mk κ) + κ's row): by `kept_symbol`
    (WordJoin.lean), `membPort_wd_main`, `keptSym_seat` and
    `longFront_kept`.
  `open_word_eq`: **under `open_word_front`'s premises (OpenWordFront.lean) at EVERY position · the
    front's frame is W₀ · W₀ lists, at the place mk κ, a kept place with the slot's member's number
    and more rows than κ's · longFront answers at every position: foldedAt R.Sh.par (readP (h + g)
    rows.gamma) (R.Sh.rho.wd W) z = wordOf s R.Kp fun q α => readE ‹longFront … q›[coordOf
    W₀ rows mk ‹row› α].**
Limits. ALL PREMISES STAND: R.Good · LaysFit · KeptSeat and MaskSeat at every member · hz on the
fresh mask's word · the frame's kept places · «longFront answers at every position»: none is shown
at a value. Nothing on the samples. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.OpenWordFront
import Johnson.Top.H0.K2Hands.StrMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (rowAt wordsOf)
open VerifiableInference.Desc.First.K2Caller (KeptSeat keptSym_seat)
open VerifiableInference.Desc.First.K2Hands (keptSym longFront_kept coordOf rowsBefore)
open VerifiableInference.Desc.First.Close (foldedAt membPort_wd_main)

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

local notation "RP" => Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp

/-- **A KEPT SLOT.** -/
theorem kept_front {Xi : Type} (G : FileDescription Xi) (seat : Fin l.length → ℕ × ℕ) (Y : Strs)
    (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64)
    (no : {i // mem i} → ℕ) (hm : fx.f.rows.masks = 2) {W₀ : SwitchFrame}
    (hW : First.K2.frameAt fx = some W₀) (mk : (RP).Kp → ℕ)
    (hK : ∀ κ : (RP).Kp, ∃ k, W₀.kept[mk κ]? = some k ∧ k.old = no κ.1.1 ∧ κ.2.val < k.rows)
    (KS : ∀ a : {i // mem i}, (l.get a.1).1.mainRows ≠ 0 →
      KeptSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1) (2 ^ (cMain cs (l.get a.1).1).a))
    (z : (RP).Sh.par.Cw.Word) (g : Fin (s.h + s.g) → GE) (q : Fin (2 ^ s.C.a)) {seg : Array E}
    (h : First.K2.longFront p t fx orc q.val = some seg) (κ : (RP).Kp) :
    foldedAt (RP).Sh.par g ((RP).Sh.rho.wd ((RP).G.word (wordsOf G cs l seat Y))) z (.inl q)
        (some κ, ()) =
      readE (seg.getD (1 + (rowsBefore W₀.kept (mk κ) + κ.2.val)) zeroE) := by
  obtain ⟨k, hk, ho, hr⟩ := hK κ
  have h0 : (l.get κ.1.1.1).1.mainRows ≠ 0 := fun e0 => absurd κ.2.isLt (by
    show ¬ κ.2.val < (l.get κ.1.1.1).1.mainRows
    omega)
  have eC := hM κ.1.1.1 κ.1.1.2 h0
  have hq : q.val < 2 ^ (cMain cs (l.get κ.1.1.1).1).a := by rw [eC]; exact q.isLt
  rw [longFront_kept hm h hW (mk κ) k κ.2.val hk hr, ho,
    keptSym_seat (KS κ.1.1 h0) κ.2.val q.val κ.2.isLt hq, kept_symbol RP _ z g q κ ()]
  exact membPort_wd_main cs (l.get κ.1.1.1).1 (l.get κ.1.1.1).2 s (oM κ.1.1.1) (oZ κ.1.1.1)
    (hM κ.1.1.1 κ.1.1.2) (hZ κ.1.1.1 κ.1.1.2)
    (fun x => (RP).G.word (wordsOf G cs l seat Y) ⟨κ.1.1, x⟩) q ⟨q.val, hq⟩ rfl κ.2

/-- **THE TWO WORDS ARE ONE.** -/
theorem open_word_eq {Xi : Type} (G : FileDescription Xi) (seat : Fin l.length → ℕ × ℕ) (Y : Strs)
    (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64)
    (no : {i // mem i} → ℕ) (ix : {i // mem i} → ℕ) (hg : (RP).Good)
    (Ft : LaysFit RP fx.f.rows.layout ix)
    (hf : ∀ a, (RP).nZ a ≠ 0 → fx.f.rows.layout.maskFirst.getD (ix a) none = some ((RP).oZ a))
    (hm : fx.f.rows.masks = 2) (hγ : fx.f.rows.gamma.length = s.h + s.g)
    (hk : fx.f.rows.layout.k = s.h + s.g) (hh : fx.f.rows.layout.h = s.h)
    (hno : ∀ a, fx.f.rows.layout.members[ix a]? = some (no a))
    (KS : ∀ a : {i // mem i}, (l.get a.1).1.mainRows ≠ 0 →
      KeptSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1) (2 ^ (cMain cs (l.get a.1).1).a))
    (MS : ∀ a : {i // mem i}, MaskSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1)
      (2 ^ s.C.a) fun x => x % 2 ^ aOf cs (l.get a.1).1)
    (z : (RP).Sh.par.Cw.Word)
    (hz : ∀ (q : Fin (2 ^ s.C.a)) (b : Fin s.h → Bool),
      z q (b, ()) = readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val))
    {W₀ : SwitchFrame} (hW : First.K2.frameAt fx = some W₀)
    (mk : (RP).Kp → ℕ)
    (hK : ∀ κ : (RP).Kp, ∃ k, W₀.kept[mk κ]? = some k ∧ k.old = no κ.1.1 ∧ κ.2.val < k.rows)
    (hall : ∀ q : Fin (2 ^ s.C.a), ∃ seg, First.K2.longFront p t fx orc q.val = some seg) :
    foldedAt (RP).Sh.par (readP (s.h + s.g) fx.f.rows.gamma)
        ((RP).Sh.rho.wd ((RP).G.word (wordsOf G cs l seat Y))) z =
      First.K2Hands.wordOf s (RP).Kp fun q α =>
        readE (((First.K2.longFront p t fx orc q.val).getD #[]).getD
          (coordOf s (RP).Kp W₀ fx.f.rows mk (fun κ => κ.2.val) α) zeroE) := by
  funext pN
  rcases pN with q | q | q
  · obtain ⟨seg, hs⟩ := hall q
    funext sy
    obtain ⟨o, ⟨⟩⟩ := sy
    show _ = readE (((First.K2.longFront p t fx orc q.val).getD #[]).getD _ zeroE)
    rw [hs]
    cases o with
    | none =>
      exact (open_word_front cs l mem s e oM oZ hM hZ kp G seat Y p t fx orc no ix hg Ft hf hm hγ
        hk hh hno KS MS z hz q hs).1
    | some κ =>
      exact kept_front cs l mem s e oM oZ hM hZ kp G seat Y p t fx orc no hm hW mk hK KS _ _ q hs κ
  · obtain ⟨seg, hs⟩ := hall q
    funext sy
    obtain ⟨⟩ := sy
    show _ = readE (((First.K2.longFront p t fx orc q.val).getD #[]).getD _ zeroE)
    rw [hs]
    exact (open_word_front cs l mem s e oM oZ hM hZ kp G seat Y p t fx orc no ix hg Ft hf hm hγ
      hk hh hno KS MS z hz q hs).2.1
  · obtain ⟨seg, hs⟩ := hall q
    funext sy
    obtain ⟨⟩ := sy
    show _ = readE (((First.K2.longFront p t fx orc q.val).getD #[]).getD _ zeroE)
    rw [hs]
    exact (open_word_front cs l mem s e oM oZ hM hZ kp G seat Y p t fx orc no ix hg Ft hf hm hγ
      hk hh hno KS MS z hz q hs).2.2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kept_front
#print axioms VerifiableInference.Desc.LinkJoin.open_word_eq
