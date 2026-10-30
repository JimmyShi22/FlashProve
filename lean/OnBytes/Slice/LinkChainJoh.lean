-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkChainJoh.lean: UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove): the written link with records, its batching and its
chain of stages, round-by-round sound record by record below the Johnson radius, FROM CONDITIONS ON
SIZES, RADII AND THE ROUNDS' FORMS, AND A TIE TO THE DECISION.

`link_chain_rec` (OnBytes/Slice/LinkRecBchks.lean) still asks facts on codes: the blocks' statements
of the chain, a bound on the lists of the group's code, bounds on the lists of the two folded rows'
oracle messages, and that their samples tell two members of a list apart. This file fills them. The
chain: `Chain.holds_joh` (OnBytes/Slice/ManyHoldsJoh.lean). The group's lists and the members'
lists: the Johnson bound, which is proved. The samples: `memb_evades_of`
(OnBytes/Slice/MembFacts.lean), which asks no radius: a folded row's message is over the extension
field and has one pad entry.

Main theorems: `memb_list_joh` (nothing assumed), `link_chain_joh`. "Nothing assumed" means here:
not the statement on codes; the hypotheses that stand in the statement itself are assumed.

WHAT `link_chain_joh` STILL ASKS. (1) Of sizes and radii: `Sz.RadJ` of the tables' code;
`Chain.JohAt` of the chain's stages; the members' radius eU is below the Johnson radius of the
members' code, which is the first stage's main code; the chain's first radius is at most eU. (2) Of
the rounds' forms: `DrawsOK`, `SendsDraws` of the batching's round, and what `Chain.JohAt` holds of
the chain's. (3) Of the error counts: the chain's are those of the letters (`Chain.PlainAt`). (4)
That corners are different (`hpl`, `hplc`). (5) THE TIE TO THE DECISION: the readings are the rows,
the record's rows among them (`IsRowsR`), and the word (`WordTie`); a yes of the written decision
gives the chain's yes in the field (`hsem`); all at the letters N for the rows' numbers and t₀ for
the first stage's number of positions. (6) `S.P.cut = cut`: cut is a free letter, so this costs
nothing; what is owed by whoever uses the language is that the format's s is the number of answers
of Z.

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHAIN AT ANY SETTING: (1) to (5) are
shown of no setting, program or file here, but for `Sz.RadJ` at two sets of numbers (`Sz.radJ_full`,
`Sz.radJ_small`). `link_chain_joh` is applied in OnBytes/Slice/SmallRecLink.lean and
OnBytes/Slice/FullRecLink.lean, which show (1) to (4), (6) and the first two parts of (5) together,
at a record with one answer. No number is stated: with large counts the statement is true for free.
The language (`Sz.LangE2T`) has three ways out: the first table does not decode with its record, and
at each table a collision at its record's seed; where one is open the theorem says nothing. How
often a collision occurs, and where a seed comes from, is not said. All that the heads of
OnBytes/Slice/LinkSoundRec.lean, BatSemRec.lean, LinkRecBchks.lean and ManyHoldsJoh.lean do not
claim.

-/
import OnBytes.Slice.LinkRecBchks
import OnBytes.Slice.ManyHoldsJoh
import OnBytes.Slice.MembFacts

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks

/-- The Johnson bound for a folded row's oracle message: below the Johnson radius of the code C
every word has at most `listMax` messages near it. -/
theorem memb_list_joh (S : Sz) (ha : S.P.C.a ≤ 32) (hk : S.P.C.r + S.P.C.l ≤ 2 ^ S.P.C.a)
    (hJ : InJohnson (2 ^ S.P.C.a) (2 ^ S.P.C.a - (S.P.C.r + S.P.C.l) + 1) S.eU) :
    S.memb.om.ListLE (listMax (2 ^ S.P.C.a) (2 ^ S.P.C.a - (S.P.C.r + S.P.C.l) + 1) S.eU) := by
  have h := ld_list_johnson GE (Fin (2 ^ S.P.C.a)) S.memb.Cm _ S.eU (memb_laws S ha hk)
    (memb_dist S ha hk) (by rw [Fintype.card_fin]; exact hJ)
  rw [Fintype.card_fin] at h
  exact sig_list_of_code GE S.memb.om _ h

/-- **Under `Cb.BCHKS46At`, and under conditions on sizes, radii and the rounds' forms and a tie to
the decision that are shown of no setting, program or file: link, batching and chain are
round-by-round sound at the pair of records r for `Sz.LangE2T`**, which has three ways out, below
the Johnson radius. The head lists what is asked. -/
theorem link_chain_joh (S : Sz) (Z : Sample GE S.En) (hA : BCHKS46At GF GE) (hR : S.RadJ)
    (N : RowNo S Z) {t₀ : ℕ} (d1 d2 d3 d4 d5 dA : PQ.RD) (xs : List PQ.XO)
    (dec : PQ.View → Bool) (cut : ℕ) (hcut : S.P.cut = cut)
    (hpl : Function.Injective (S.lkR Z).D.pl) (hplc : Function.Injective S.memb.plc)
    (hJU : InJohnson (2 ^ S.P.C.a) (2 ^ S.P.C.a - (S.P.C.r + S.P.C.l) + 1) S.eU)
    (hd : DrawsOK S d1 d2 d3 d4 d5) (c : Chain (S.sg t₀))
    (hp : c.PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ) (hJ : c.JohAt) (hU : c.rad ≤ S.eU)
    (hdA : SendsDraws dA 0 1 0 0)
    (rows : (S.lkR Z).X4 → (ℕ → GE) × (ℕ → (S.sg t₀).cIn.J → GE))
    (w1 : (wRound d2).Orc → (S.sg t₀).cIn.Word) (z1 : (wRound d2).Orc → (S.sg t₀).cFr.Word)
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (hrows : ∀ x, IsRowsR S Z t₀ N x (rows x).1 (rows x).2)
    (hw1 : ∀ o, WordTie S t₀ d2 o (w1 o)) (r : (S.lkR Z).X0)
    (hsem : ∀ (y : (S.lkR Z).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true →
      c.Acc (sumStmR N t₀ (rows (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rows (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        (w1 m2.1) (z1 m2.1) (g1 m2.1) b) :
    (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).Sound (fun _ y => S.LangE2T Z cut r y)
      (0, coreErrR S Z d1 d2 d3 d4 d5 (S.badJ S.e0) (S.badJ S.e1)
        (fun _ => listMax (2 ^ S.P.C.a) (2 ^ S.P.C.a - (S.P.C.r + S.P.C.l) + 1) S.eU)
        (batErrR N ((S.sg t₀).lstJ c.rad) dA, c.errL)) := by
  have hs := hJ.first.sized
  have haC : S.P.C.a ≤ 32 := hs.small
  have hkC : S.P.C.r + S.P.C.l ≤ 2 ^ S.P.C.a := hs.roomC
  have hlt : c.rad < 2 ^ S.P.C.a - (S.P.C.r + S.P.C.l) + 1 :=
    lt_of_lt_of_le hJ.first.joh.1 (Nat.min_le_left _ _)
  exact link_chain_rec S Z hA hR N d1 d2 d3 d4 d5 dA xs dec cut _ hcut hpl
    (fun _ => memb_list_joh S haC hkC hJU) (fun _ => memb_evades_of S hplc) hd c _ _
    ⟨hU, ldOf_dist S.P.C haC hkC, hlt⟩
    (Sg.listJ_of (Sg.fit_cIn hJ.first.sized) hJ.first.joh) hdA (c.holds_joh hA hp hJ) rows w1 z1 g1
    hrows hw1 r hsem

end OnBytes.Slice
