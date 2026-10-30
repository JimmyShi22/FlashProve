-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyMaskAtSegment.lean: the kind "the code switch" (K2): THE
LAST MESSAGE OF A SWITCH's OWN SENDING, THE NEXT FOLD's MASK: what `segmentGroupRows`
(Honest/K2/Closing.lean) lays anew of it at another switch is what the sender laid: the sister of
`copy_at_segment` (Honest/K2/Law/CopyAtSegment.lean), which stops in front of that message.
Statements with their proofs; no definition.

  `laidRows_noMain`, `messageRows_noMain`   a message without a main row is laid alike at any data
  `copyMask_at_segment`   R.fresh = some (V q), q the last message's number

WHY THE FIRST TWO. The sender lays that message at its own letter of data; `segmentGroupRows` lays it at
zeros. `messageRows` (Honest/K2/Sending.lean) reads the data at a main row alone.

ITS PREMISES, BY KIND: as `copy_at_segment`'s, with, PUBLIC, ON THE SEGMENT: its fold's row
variables are the sender's (hFv) · PUBLIC, ON THE SENDER: q is the number of its sending's last
message (hq), which has no main row (hm) · no premise on the data.

By: `segmentRows_mask` (Honest/K2/Law/RowsOfSegment.lean) · `copy_carried`
(Honest/K2/Law/CopyOne.lean) · `messageRows_laid` (Honest/K2/Law/Laid.lean) · `messageRows_again`
(Honest/K2/Law/MaskCoin.lean) · `bind_ok'` (Honest/K2/Law/Reads.lean). Kin, not called:
`foldAt_self` (Honest/K2/Law/ClearAtCore.lean [not in this library; so here read: not proved in this
library]) has what the proof's step hfold says; that file does not lie beneath this one, and two
lines inside the proof spare the import.

Limits. All Limits of CopyOne.lean stand. None of the premises is paid here. An equation at each
run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtSegment
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows zeroG)
open Reads

variable {Bk : ProverCoinCounts}

theorem laidRows_noMain (table : FreshTable) (codes : OnBytes.Codes) {s : OnBytes.OracleShape}
    (hs : s.mainRows = 0) (fold : Option Nat) (d d' : Nat → Nat → Cb.Gl.E) (cF : Array Cb.Gl.F)
    (cE cM cT : Array Cb.Gl.E) :
    laidRows table codes s fold d cF cE cM cT = laidRows table codes s fold d' cF cE cM cT := by
  unfold laidRows
  simp [hs]

/-- A message without a main row is laid alike at any data. -/
theorem messageRows_noMain {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    (hs : s.mainRows = 0) {fold : Option Nat} {d : Nat → Nat → Cb.Gl.E}
    (d' : Nat → Nat → Cb.Gl.E) {k : Stretch} {R : Johnson.Prover.Send.Rows}
    (h : messageRows table codes s fold d k = .ok R) :
    messageRows table codes s fold d' k = .ok R := by
  obtain ⟨R', h'⟩ := messageRows_again (table' := table) (data' := d') (k' := k) rfl h
  obtain ⟨-, -, -, cF, cE, cM, cT, a1, a2, a3, a4, e⟩ := messageRows_laid h
  obtain ⟨-, -, -, cF', cE', cM', cT', b1, b2, b3, b4, e'⟩ := messageRows_laid h'
  obtain rfl : cF = cF' := Except.ok.inj (a1.symm.trans b1)
  obtain rfl : cE = cE' := Except.ok.inj (a2.symm.trans b2)
  obtain rfl : cM = cM' := Except.ok.inj (a3.symm.trans b3)
  obtain rfl : cT = cT' := Except.ok.inj (a4.symm.trans b4)
  rw [h', e', e, laidRows_noMain table codes hs fold d' d]

/-- **THE JOIN, AT THE LAST MESSAGE.** q: its number. -/
theorem copyMask_at_segment (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    {S : SegmentPub} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {base : Nat} {R : GroupRows}
    (hR : segmentGroupRows freshTable S prev prevKept own (Stretch.carried p.carries c.2.2) base true =
      .ok R)
    (hS : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    (hFv : S.foldVars = p₀.foldVars)
    {M : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) M c₀.1 = .ok V)
    {q : Nat} (hq : q + 1 = (switchSent p₀.sizes p₀.others).size)
    (hm : ((switchSent p₀.sizes p₀.others).getD q default).shape.mainRows = 0) (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[base + q]? =
      some e)
    (t1 : e.owner = ⟨p₀.place, 0⟩)
    (t2 : e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) q)
    (t3 : e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD q default).shape
      (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) q)) :
    R.fresh = some (V q) := by
  have eq : (switchSent p₀.sizes p₀.others).size - 1 = q := by omega
  obtain ⟨r, hr, hg⟩ := segmentRows_mask hR
  have hc := copy_carried ch p₀ p k c₀ h₀ c h hV (n := q) (by omega) (base + q) e he t1 t2 t3
  have hfold : foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) q = some p₀.foldVars := by
    show (if ((switchSent p₀.sizes p₀.others).size - 1 == q) = true then some p₀.foldVars
      else none) = _
    rw [eq, if_pos (beq_self_eq_true _)]
  rw [hfold] at hc
  obtain ⟨s, hs, hms⟩ := bind_ok' hc
  have hz := messageRows_noMain hm (fun _ _ => zeroG) hms
  rw [hS, hSent, hFv, eq, hs] at hg
  have hg' : messageRows freshTable p₀.sizes.codes
      ((switchSent p₀.sizes p₀.others).getD q default).shape (some p₀.foldVars)
      (fun _ _ => zeroG) s = .ok r := hg
  rw [hz] at hg'
  rw [hr, Except.ok.inj hg']

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.laidRows_noMain
#print axioms ProofFile.Honest.K2.Law.messageRows_noMain
#print axioms ProofFile.Honest.K2.Law.copyMask_at_segment
