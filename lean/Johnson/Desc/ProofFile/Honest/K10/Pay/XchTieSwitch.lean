-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieSwitch.lean: the closing of a segment (K10): the one equation that the field tie of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean) is brought down to in Pay/XchOwedMembers.lean, at a member that a code switch has
sent: the carrying message, a kept copy, or an own message of moment 0; every message of the switch's sending but the last,
the next fold's fresh mask.

  `fold_none`        such a message is no fresh mask
  `same_rows`        two returns of the shared text of a message's rows at the same arguments are one
  **`tab_of_switch`**  the witness's table of the message is `K1.rowsMsg` of the rows Rr that the closing's job has made anew. From:
      hm, hp    the two ties on the script, in the threads' forms, at the switch's text off the pad and at its pad's text
                (`tab_rows_off`, Honest/K2/Law/TabRowsOff.lean, has them)
      hH, hV    the switch is handed its coins, and its rows are laid
      hRr       Rr is the shared text's return at the switch's codes, the message's shape, data and a stretch kk
      hData     data are the switch's own main rows of the message
      hCoins    kk is the switch's own cut for the message
  `coins_of_book`    for hCoins: from the book's entry by which the closing's part carries the message's coins
  `inFirst_at`       for hData: what the closing's job takes as the shape and the data of a member of the first sending
  `closingFor_inv`, `lotClosing_inv`   for hData: what the switch's closing returns is the first part of what `closingFrom` returned

Limits. The premises named are shown here of no script, book or run. No head and no thread is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchLent
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff
import Johnson.Desc.ProofFile.Honest.K2.Law.SenderOwn
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K2.Honest (Left mainRows)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open ProofFile.Honest.K2 (SegmentPub SwitchPlace Closing Stretch FreshTable messageRows freshTable switchSent switchFresh
  dueBefore messageDue NoWord handed switchRowsLaid switchMsgOff switchPadTxt closingFor closingFrom lotClosingAt ownBy)
open ProofFile.Honest.K2.Law (SwitchCoins senderOwn Laid inFirstOf dataAtOf)
open ProofFile.Honest.K2.Reads (bind_ok')

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- A message of a switch's sending that is not the last is no fresh mask. -/
theorem fold_none (p : SwitchPlace) {n : Nat} (hn : n + 1 < (switchSent p.sizes p.others).size) :
    K2.foldAt (switchFresh p.sizes p.others p.foldVars) n = none := by
  unfold K2.foldAt switchFresh
  have hne : ((switchSent p.sizes p.others).size - 1 == n) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  show (if ((switchSent p.sizes p.others).size - 1 == n) = true then some p.foldVars else none) = none
  rw [hne]
  rfl

/-- Two returns of the shared text at the same arguments are one. -/
theorem same_rows {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (hf : fold = none) {data : Nat → Nat → Cb.Gl.E} {k : Stretch} {A B : Johnson.Prover.Send.Rows}
    (h1 : messageRows table codes s fold data k = .ok A) (h2 : messageRows table codes s none data k = .ok B) :
    A = B := by
  subst hf
  exact Except.ok.inj (h1.symm.trans h2)

/-- **At a member that a code switch has sent, the witness's table is the rows that the closing's job has made anew.** -/
theorem tab_of_switch (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (fx n num j t : Nat) (hm : OwnMsgs Q Vd N num fx (switchMsgOff 0 D readers closing p n))
    (hp : OwnPads Q Vd j t (fun k _ => switchPadTxt 0 p n k))
    (hw : NoWord (switchSent p.sizes p.others)) (hn : n + 1 < (switchSent p.sizes p.others).size)
    (k : Coins Bk) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed 0 p k = some c) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    (hN : N ≤ hd.length) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w (hd.take fx) = .ok V)
    {data : Nat → Nat → Cb.Gl.E} {kk : Stretch} {Rr : Johnson.Prover.Send.Rows}
    (hRr : messageRows freshTable p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape none data kk =
      .ok Rr)
    (hData : ∀ Wl, closing p (D w.x) (readers w) ((hd.take fx).take ((hd.take fx).length - 0))
        (Stretch.carried p.carries c.2.2) = .ok Wl →
      data = mainRows p.sizes Wl (senderOwn (D w.x) (readers w) p) n)
    (hCoins : ∀ c' : Cs (messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
        (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n)),
      c.1.cut (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n)
        (messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
          (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n)) = some c' → kk = ⟨_, c'⟩) :
    (Q.wit k w hd).tab p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape num j t =
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape Rr := by
  have hn' : n < (switchSent p.sizes p.others).size := by omega
  have h1 := K2.Law.tab_rows_off Q Vd N 0 D readers closing p fx n num j t hm hp hw hn' k hH w hv hd hN hV
  obtain ⟨Wl, hW, hR⟩ := K2.Law.rowsLaid_inv hV
  obtain ⟨c', hc', hmr⟩ := K2.rowsAll_at hR hn'
  have e : V n = Rr := same_rows (fold_none p hn) hmr (by
    rw [← hData Wl hW, ← hCoins c' hc']
    exact hRr)
  rw [h1, e]

/-- For hCoins: the carried stretch is the sender's own cut, by the book's entry. -/
theorem coins_of_book {look : Addr → (d : Due) × Cs d} {ds : List (String × Due)} {l : List Ahead} {y : CsAll ds}
    (h : lend look ds l = .ok y) {nn : Nat} {a : Ahead} (hn : l[nn]? = some a) {own : Addr} (ho : a.owner = own)
    {t : Due} {c₁ : Cs t} (h1 : (look own).2.cut ⟨0, 0⟩ t = some c₁) {st cnt : Due} (hs : a.start = st)
    (hc : a.count = cnt) {kk : Stretch} (hk : Stretch.carried ds y nn = .ok kk) :
    ∀ c' : Cs cnt, c₁.cut st cnt = some c' → kk = ⟨cnt, c'⟩ := by
  subst ho hs hc
  intro c' h2
  exact Except.ok.inj (hk.symm.trans (carried_is_own h hn h1 h2))

/-- For hData: the shape and the data of a member of the first sending, as the closing's job takes them. -/
theorem inFirst_at (S : SegmentPub) (prev : Option Left) (own : Nat → Nat → Nat → Cb.Gl.E) {n : Nat} {a : Laid}
    (h : (inFirstOf S prev own)[n]? = some a) :
    a.1 = ((S.sent.headD #[]).getD n default).shape ∧ a.2 = dataAtOf S prev own n := by
  unfold inFirstOf at h
  rw [List.getElem?_map] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [List.getElem?_zipIdx] at hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  have hy' : (S.sent.headD #[]).toList[n]? = some y := by
    rw [List.getElem?_take] at hy
    split at hy
    · exact hy
    · cases hy
  refine ⟨?_, ?_⟩
  · show y.shape = _
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hy']
    rfl
  · show dataAtOf S prev own (0 + n) = _
    rw [Nat.zero_add]

/-- For hData: what `closingFor` returns. -/
theorem closingFor_inv {table : FreshTable} {segs : List SegmentPub} {next : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {Wl : Left}
    (h : closingFor table segs next own heard k = .ok Wl) :
    ∃ (x : Option (Left × List OnBytes.OracleShape) × Nat) (W2 : Left × List OnBytes.OracleShape),
      closingFrom table own heard k segs 0 0 none = .ok x ∧ x.1 = some W2 ∧ W2.1 = Wl := by
  unfold closingFor at h
  obtain ⟨x, hx, h2⟩ := bind_ok' h
  obtain ⟨x1, x2⟩ := x
  cases x1 with
  | none => cases h2
  | some W2 =>
    refine ⟨_, W2, hx, rfl, ?_⟩
    have h3 : (if (W2.2 != next) = true then
        (Except.error "a switch's kept members are not those that the fold in front left" : Except String Left)
      else .ok W2.1) = .ok Wl := h2
    split at h3
    · cases h3
    · exact Except.ok.inj h3

/-- For hData: the same of the closing as the kind's lot lays it. -/
theorem lotClosing_inv {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {p : SwitchPlace} {D : RowData}
    {R : Readers} {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {Wl : Left}
    (h : lotClosingAt lay segs p D R heard k = .ok Wl) :
    ∃ (x : Option (Left × List OnBytes.OracleShape) × Nat) (W2 : Left × List OnBytes.OracleShape),
      closingFrom freshTable
        (ownBy D R p.addrs (fun s m => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) heard)
        heard k (segs.take p.link) 0 0 none = .ok x ∧ x.1 = some W2 ∧ W2.1 = Wl := by
  unfold lotClosingAt at h
  obtain ⟨_, -, h2⟩ := bind_ok' h
  exact closingFor_inv h2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.fold_none
#print axioms ProofFile.Honest.K10.same_rows
#print axioms ProofFile.Honest.K10.tab_of_switch
#print axioms ProofFile.Honest.K10.coins_of_book
#print axioms ProofFile.Honest.K10.inFirst_at
#print axioms ProofFile.Honest.K10.closingFor_inv
#print axioms ProofFile.Honest.K10.lotClosing_inv
