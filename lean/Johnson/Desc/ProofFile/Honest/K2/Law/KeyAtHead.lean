-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeyAtHead.lean: the kind "the code switch" (K2): `key_at_walk`
(Honest/K2/Law/KeyAtWalk.lean) AT THE LIBRARY's HEAD, WITH ITS PUBLIC PREMISES ON THE PLACES, THE
SEGMENTS AND OUR OWN LISTS PAID: by `switchTies_at_head` (Honest/K2/Law/TiesWritten.lean), and by
one more closed fact at the written places: a sending's last message has no main row. Statements
with their proofs; no definition.

  `lastNoMainW`            THE CLOSED FACT: at each written place the sending is not empty, and
                           its last message has no main row
  `lastNoMainW_can_fail`   a control: the sending's first message has a main row, at each written
                           place
  `key_at_head`            THE END, at two places of the lot with p₀.link < p.link

WHAT IS LEFT, BY KIND. RETURNS: both switches are handed their stretches; the sender's closing
returns W₀; the later walk returns y'; the sender's laying returns V; and `segmentGroupRows` returns each
R that the conclusion speaks of. THE TWO TESTS ON THE BOOK SAY YES: hs, hf. ON THE DATA AND THE
CHALLENGES: ho, hg; at each message in front of the last: hd.

Limits. The Limits of KeyAtWalk.lean and TiesWritten.lean stand, but one: that p comes later than p₀
is a premise here (hl). Among them: ROWS AGAINST ROWS: the conclusion names the sender's rows V, not
a witness's words; THE TESTS ARE EVALUATED AT NO REAL BOOK HERE; closed facts by Lean's kernel,
replayed by no independent checker. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, under the
head. What is left is paid nowhere here, nor proved met together. Nothing on the later sendings of a
segment, nor on the first segment. An equation at each run's coins: what is WRITTEN where. NO LOT IS
LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeyAtWalk
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left mainRows)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

theorem lastNoMainW :
    (placesW.all fun p => decide (0 < (switchSent p.sizes p.others).size) &&
      ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1)
        default).shape.mainRows == 0) = true := by
  decide +kernel

/-- A control: the same question at the sending's first message: no, at each written place. -/
theorem lastNoMainW_can_fail :
    (placesW.all fun p =>
      !(((switchSent p.sizes p.others).getD 0 default).shape.mainRows == 0)) = true := by
  decide +kernel

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {rn : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bk : ProverCoinCounts}

/-- **THE KEY AT THE HEAD.** p₀: the sender. p: a later switch. y': what p's own walk returns over
the segments in front of p₀. V: the rows that p₀ laid. -/
theorem key_at_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀)
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p₀.link < p.link) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    {lay : OnBytes.Params.ReqLayout} {D : RowData} {Rd : Readers}
    {heard₀ heard : List Fmt.Drawn} {W₀ : Left}
    (hW₀ : lotClosingAt lay (segmentsOf Zp Bs.G₀) p₀ D Rd heard₀
      (Stretch.carried p₀.carries c₀.2.2) = .ok W₀)
    (ho : ∀ i, i < ((segmentsOf Zp Bs.G₀).take p₀.link).length →
      lotOwn (segmentsOf Zp Bs.G₀) p₀ D Rd heard₀ (0 + i) =
        lotOwn (segmentsOf Zp Bs.G₀) p D Rd heard (0 + i))
    (hg : ∀ Sg ∈ (segmentsOf Zp Bs.G₀).take p₀.link,
      challengesOr0 heard₀ Sg.gamma = challengesOr0 heard Sg.gamma)
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p D Rd heard) heard
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take p₀.link) 0 0 none = .ok y')
    {own₀ : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) (mainRows p₀.sizes W₀ own₀) c₀.1 = .ok V) :
    ∃ Sg, (segmentsOf Zp Bs.G₀)[p₀.link]? = some Sg ∧
      ∀ (own' : Nat → Nat → Nat → Cb.Gl.E) (R : GroupRows),
        segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) own'
          (Stretch.carried p.carries c.2.2) y'.2 true = .ok R →
        (∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 →
          mainRows p₀.sizes W₀ own' n = mainRows p₀.sizes W₀ own₀ n → R.rows[n]? = some (V n)) ∧
        R.fresh = some (V ((switchSent p₀.sizes p₀.others).size - 1)) := by
  obtain ⟨⟨Sg, rest, hSg, -, hSz, hSent, hFv⟩, hfind, hF⟩ := switchTies_at_head h O hp₀ hp hl
  have hpW : p₀ ∈ placesW := by
    rw [← places_at_head h O]
    exact hp₀
  have hlast := List.all_eq_true.1 lastNoMainW p₀ hpW
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hlast
  refine ⟨Sg, hSg, fun own' R hR => ?_⟩
  obtain ⟨k1, k2⟩ := key_at_walk ch p₀ p k c₀ h₀ c hc hs hf hfind hW₀ ho hg hy' hSz hSent hFv hV hR
  refine ⟨fun n hn hd => ?_, ?_⟩
  · obtain ⟨ct, hct⟩ := hF n (by omega)
    exact k1 n hn hd ct hct
  · obtain ⟨ct, hct⟩ := hF ((switchSent p₀.sizes p₀.others).size - 1) (by omega)
    exact k2 _ (by omega) hlast.2 ct hct

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lastNoMainW
#print axioms ProofFile.Honest.K2.Law.lastNoMainW_can_fail
#print axioms ProofFile.Honest.K2.Law.key_at_head
