-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeyOfLots.lean: the kind "the code switch" (K2): `key_at_head`
(Honest/K2/Law/KeyAtHead.lean) AT THE KIND's LOT's OWN TEXTS, AT ONE INPUT w: V is what
`switchRowsLaid` (Honest/K2/ScriptLots.lean) returns at the sender: the rows of which the lot's text
`switchMsgTxt` reads its entries. The premises ho, hg and hd are gone: paid out of plainer ones by
Honest/K2/Law/HeardPrefix.lean, Honest/K2/Law/OwnAtSender.lean and
Honest/K2/Law/ReadyOfClosing.lean. One statement with its proof: a join; no definition.

  `key_of_lots`   R.rows[n]? = some (V n) in front of the sending's last message; at that one, q:
                  R.fresh = some (V q)

WHAT IS LEFT, BY KIND. RETURNS: both switches are handed their stretches; `switchRowsLaid` returns V
at the sender; the later switch's walk over the segments in front of the sender returns y';
`segmentGroupRows` returns each R that the conclusion speaks of. THE TWO TESTS ON THE BOOK SAY YES: hs,
hf. ON A RUN: hpre: what the sender has heard is a beginning of what the later switch has heard ·
hgam: the numbers of the folds' challenges of the segments in front lie below the length of what the
sender has heard. ON THE FILLING D, AT w's INSTANCE: hn: what the own data of the segments in front
hang on was heard in front of the sender. (That the sender's own messages of moment 0 hang on no
challenge is no premise: the sender's return says so: `h0_of_closing`.)

Limits. The Limits of KeyAtHead.lean, HeardPrefix.lean, OwnAtSender.lean and ReadyOfClosing.lean
stand: among them: ROWS AGAINST ROWS: the conclusion names the sender's rows V, not a witness's
words; THE TESTS ARE EVALUATED AT NO REAL BOOK HERE; closed facts by Lean's kernel, replayed by no
independent checker; THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, under the head. What is left
is paid nowhere here, nor proved met together. Nothing on the later sendings of a segment, nor on
the first segment. An equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeyAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.HeardPrefix
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnAtSender
import Johnson.Desc.ProofFile.Honest.K2.Law.ReadyOfClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {rn : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **THE KEY AT THE LOT's OWN TEXTS.** p₀: the sender. p: a later switch. hd₀, hd: what each has
heard in front of its part. -/
theorem key_of_lots (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀)
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p₀.link < p.link) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    (w : Local W₀ Rc Xi Tr) {hd₀ hd : List Fmt.Drawn} (hpre : hd₀ <+: hd)
    (hgam : ∀ Sg ∈ (segmentsOf Zp Bs.G₀).take p₀.link, ∀ g ∈ Sg.gamma, g < hd₀.length)
    (hn : ∀ s m a, s < p₀.link → p.addrs s m = some a → (D w.x).heardAt a ≤ hd₀.length)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w hd₀ = .ok V)
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hd) hd
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take p₀.link) 0 0 none = .ok y') :
    ∃ Sg, (segmentsOf Zp Bs.G₀)[p₀.link]? = some Sg ∧
      ∀ R : GroupRows,
        segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
          (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hd (0 + p₀.link))
          (Stretch.carried p.carries c.2.2) y'.2 true = .ok R →
        (∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 → R.rows[n]? = some (V n)) ∧
        R.fresh = some (V ((switchSent p₀.sizes p₀.others).size - 1)) := by
  obtain ⟨Wl, hWl, hV'⟩ := rowsLaid_inv hV
  have et : hd₀.take (hd₀.length - 0) = hd₀ := by simp
  rw [et] at hWl
  obtain ⟨Sg, hSg, key⟩ := key_at_head h O ch hp₀ hp hl k c₀ h₀ c hc hs hf hWl
    (lotOwn_of_prefix hp₀ hp _ _ _ hpre hn) (heard_of_prefix hpre hgam) hy' hV'
  refine ⟨Sg, hSg, fun R hR => ?_⟩
  obtain ⟨k1, k2⟩ := key _ R hR
  refine ⟨fun n hn' => k1 n hn' ?_, k2⟩
  rw [Nat.zero_add]
  exact hd_at_head h O hp₀ hp hl _ _ _ (h0_of_closing hWl) Wl n hn'

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.key_of_lots
