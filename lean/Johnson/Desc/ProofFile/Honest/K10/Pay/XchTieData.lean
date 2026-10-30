-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieData.lean: the closing of a segment (K10): the premise hData of `tab_of_switch`
(Pay/XchTieSwitch.lean): at a member of a segment's first sending, the data that the closing's job lays into the main rows are
the main rows that the code switch into the segment laid.

Both are `mainRows` (Johnson/Desc/K2/Honest/Carrying.lean) of what the fold in front left and of the segment's own messages.
What the fold left is, on both sides, the return of one text over the same segments (`closingFrom_congr`, Pay/XchCongr.lean).

  `mainRows_congr`    `mainRows` at message number n reads of the own messages the one of the number n − 1 − (kept members), and
                    that only behind the carrying message and the copies
  **`data_of_switch`**  the equation. Its premises: the two returns; the closing's segments in front are the switch's; the four
                    premises of `closingFrom_congr`; the segment's sizes are the switch's; the own message that n names, if any,
                    is the same on both sides

Limits. The premises are shown here of no run. No head and no thread is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieSwitch
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.K2.Honest (Left Sizes mainRows)
open ProofFile.Honest.K2 (SegmentPub SwitchPlace Stretch freshTable closingFrom lotClosingAt ownBy challengesOr0)
open ProofFile.Honest.K2.Law (senderOwn Laid inFirstOf dataAtOf)

/-- What `mainRows` reads of the own messages. -/
theorem mainRows_congr (Z : Sizes) (W : Left) {own own' : Nat → Nat → Nat → Cb.Gl.E} {n : Nat}
    (h : Z.kept.length < n → own (n - 1 - Z.kept.length) = own' (n - 1 - Z.kept.length)) :
    mainRows Z W own n = mainRows Z W own' n := by
  unfold mainRows
  by_cases c0 : (n == 0) = true
  · rw [if_pos c0, if_pos c0]
  · rw [if_neg c0, if_neg c0]
    by_cases c1 : n ≤ Z.kept.length
    · rw [if_pos c1, if_pos c1]
    · rw [if_neg c1, if_neg c1]
      exact h (Nat.lt_of_not_le c1)

/-- **The data that the closing's job lays at a member of the first sending are the switch's own main rows.** -/
theorem data_of_switch {S : SegmentPub} {p : SwitchPlace} {lay : OnBytes.Params.ReqLayout} {segs segsK : List SegmentPub}
    {D : RowData} {R : Readers} {ownK : Nat → Nat → Nat → Nat → Cb.Gl.E} {front heard' : List Fmt.Drawn}
    {kK k' : Nat → Except String Stretch} {x : Option (Left × List OnBytes.OracleShape) × Nat} {last : Nat}
    (hx : closingFrom freshTable ownK front kK segsK 0 0 none = .ok x) {Wl : Left}
    (hW : lotClosingAt lay segs p D R heard' k' = .ok Wl) (hsegs : segsK = segs.take p.link)
    (hFirst : ∀ T ∈ segsK, 0 < (T.sent.headD #[]).size)
    (hOwn : ∀ i T, segsK[i]? = some T → ownK (0 + i) =
      ownBy D R p.addrs (fun s m => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) heard' (0 + i))
    (hGam : ∀ T ∈ segsK, challengesOr0 front T.gamma = challengesOr0 heard' T.gamma)
    (hK : ∀ n, 0 ≤ n → n < 0 + (segsK.map (·.messages)).sum → kK n = k' n)
    (hsz : S.sizes = p.sizes) {n : Nat}
    (hown : p.sizes.kept.length < n →
      ownK last (n - 1 - p.sizes.kept.length) = senderOwn D R p (n - 1 - p.sizes.kept.length))
    {a : Laid} (ha : (inFirstOf S (x.1.map (·.1)) (ownK last))[n]? = some a) :
    a.2 = mainRows p.sizes Wl (senderOwn D R p) n := by
  subst hsegs
  obtain ⟨x', W2, hx', e1, e2⟩ := lotClosing_inv hW
  have hc := closingFrom_congr freshTable (segs.take p.link) 0 0 none hFirst hOwn hGam hK
  obtain rfl : x = x' := Except.ok.inj (hx.symm.trans (hc.trans hx'))
  rw [(inFirst_at S _ _ ha).2, e1]
  show mainRows S.sizes W2.1 (ownK last) n = _
  rw [hsz, e2]
  exact mainRows_congr p.sizes Wl hown

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mainRows_congr
#print axioms ProofFile.Honest.K10.data_of_switch
