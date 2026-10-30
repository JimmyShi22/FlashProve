-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkRecBchks.lean: UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis of the theorems here, which this file does not prove): the written link with records,
with the counts of exceptional fold points and the lists of tables filled in below the Johnson
radius; and link, batching and chain joined in one statement.

OnBytes/Slice/LinkSoundRec.lean has, under its hypotheses, the written link sound record by record,
with four letters on the tables' code: at each of the two radii e0, e1 a count of exceptional fold
points (`LdIx.MCAeq`) and a bound on the lists of tables. This file fills them. The lists: the
Johnson bound for tables, which is proved (the library's `ldFc_list_johnson`). The counts: the
library bounds the exceptional points of the fold by the sum, over the fold's v steps, of the counts
for lines of tables, times q^(v - 1) (`ldFc_mca_prox`), and under that hypothesis a line of tables
of any number of rows has at most the integer part of `bchksBound` exceptional points (`rsAt_prox`;
rows cost nothing). OnBytes/Slice/BatSemRec.lean gives the hypothesis on the rounds after the fifth
from the blocks' statements. `link_chain_rec` puts the three together.

Main theorems.
 `mcaEq_bchksAt`      the count of exceptional fold points, under the hypothesis.
 `list_johnson`       the lists of tables, by the Johnson bound. Nothing assumed. "Nothing assumed"
                      means here: not the statement on codes; the hypotheses that stand in the
                      statement itself are assumed.
 `link_sound_bchks`   `link_sound_at` with the four letters filled in, for the wider language
                      `Sz.LangE2T`.
 `link_chain_rec`     the same with `ClosesR` from the batching's and the chain's statements.
 `Sz.radJ_full`, `Sz.radJ_small`   guards: the conditions on the tables' code and the radii
                      (`Sz.RadJ`) are met together beyond half the distance, at two sets of numbers.

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHAIN AT ANY SETTING. All that
OnBytes/Slice/LinkSoundRec.lean and OnBytes/Slice/BatSemRec.lean do not claim: above all that
`written` is the shape of an entry's chain, that Z is the programs' sample map, and that this is a
statement on an interactive protocol. `Cb.BCHKS46At` is a hypothesis of `mcaEq_bchksAt`,
`link_sound_bchks` and `link_chain_rec`. It speaks of all lengths, degree bounds, radii and sets of
points in GF: one false instance would empty every theorem under it. That the Lean text says what
its source's theorem says rests on a reading, not ours. `link_chain_rec` asks besides: the chain's
blocks' statements (`Chain.Holds`; below the Johnson radius OnBytes/Slice/ManyHoldsJoh.lean has them
under the same hypothesis, from conditions stage by stage, for chains that this file does not build
(OnBytes/Slice/SmallRecChain.lean and OnBytes/Slice/FullRecChain.lean build two)); that the readings
are the rows with the record's rows among them (`IsRowsR`) and the word (`WordTie`); that a yes of
the written decision gives the chain's yes in the field (`hsem`); bounds on the lists of the two
folded rows' oracle messages, and that their samples tell members apart (`Evades`); `DrawsOK`; that
the chain's first radius is at most the members' own and below the main code's distance (`SemOK`); a
bound on the lists of the group's code there; what the batching's round draws; that the compared
entries have different vertices; that cut is the format's. `Sz.RadJ` is shown of no setting here:
the two guards are at numbers typed by hand (OnBytes/Slice/SmallRecCodes.lean and
OnBytes/Slice/FullRecCodes.lean call them at two records of sizes). None of these is shown here of
any decision, program, file or setting. `bchksBound` is a real number that is evaluated nowhere
here: no number is stated, and with large counts the statements are true for free. The language
(`Sz.LangE2T`) has three ways out: the first table does not decode with its record (the key's
matter), and at each table a collision at its record's seed. Where one is open the theorems say
nothing. How often a collision occurs, and where a seed comes from, is not said.

-/
import Cb.Gen.CodeListRSAtProofs
import Cb.Ld.LdFoldEqCodeProofs
import OnBytes.Slice.BatSemRec
import OnBytes.Slice.CodeFacts

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks

/-- Under the hypothesis: a table format with the format's generator matrix, a ≤ 32, at a radius e
other than 0 with n K < (n - e)^2, where n = 2^a and K, the number of coefficients less one, is not
0. Every table has at most v b q^(v - 1) exceptional points of the fold, b the integer part of
`bchksBound n K e`. -/
theorem mcaEq_bchksAt (hA : BCHKS46At GF GE) (C : Fmt.M1.Code) (ha : C.a ≤ 32)
    (hk : 0 < C.r + C.l - 1) {J : Type} [Fintype J]
    (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J) (hG : X.G = genOf C) (e : ℕ) (he : 0 < e)
    (hj : 2 ^ C.a * (C.r + C.l - 1) < (2 ^ C.a - e) ^ 2) :
    X.MCAeq e (X.v * ⌊bchksBound (2 ^ C.a) (C.r + C.l - 1) e⌋₊ *
      Fintype.card GE ^ (X.v - 1)) := by
  have hP := rsAt_prox GF GE hA (2 ^ C.a) (C.r + C.l - 1) (C.r + C.l) 0 0 0 (ptOf C.a)
    (ptOf_inj C.a ha) hk
  rw [show C.r + C.l - 1 + 1 = C.r + C.l from by omega] at hP
  have h := ldFc_mca_prox GF GE (rsCode C) (Nat.le_refl (C.r + C.l)) J X.pl X.v X.Z X.eM X.rank _ _
    _ e hP ⟨he, hj⟩
  rw [← eq_ofEnc C X hG, Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  exact h

/-- The Johnson bound for the tables of a format with the format's generator matrix. -/
theorem list_johnson (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) {J : Type}
    (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J) (hG : X.G = genOf C) (e : ℕ)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) e) (f : X.Row → Fin (2 ^ C.a) → GE) :
    ListLE (DecodesTo X.G e f) (listMax (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) e) := by
  rw [hG, genOf_eq_GE]
  exact ldFc_list_johnson GF GE (rsCode C) e (hasDist_rsCode C ha hk) hJ X.Row f

section
variable (S : Sz) (Z : Sample GE S.En)

/-- The tables' code's distance. -/
abbrev Sz.dT : ℕ := 2 ^ S.P.T.a - (S.P.T.r + S.P.T.l) + 1

/-- The bound on the bad fold points at the radius e: v b q^(v - 1) exceptional points, b the
integer part of `bchksBound`, and L v q^(v - 1), L the Johnson bound's list. -/
noncomputable def Sz.badJ (e : ℕ) : ℕ :=
  S.P.v * ⌊bchksBound (2 ^ S.P.T.a) (S.P.T.r + S.P.T.l - 1) e⌋₊ * Fintype.card GE ^ (S.P.v - 1) +
    listMax (2 ^ S.P.T.a) S.dT e * (S.P.v * Fintype.card GE ^ (S.P.v - 1))

/-- What is asked of the tables' code and the three radii: a ≤ 32, at least two and at most 2^a
coefficients; the decoder's radius is below the distance; the two folds' radii are not 0, at most
the decoder's, and below the Johnson radius. NOT asked: that twice a radius be below the distance,
nor that the decoder's radius be below the Johnson radius. -/
structure Sz.RadJ : Prop where
  small : S.P.T.a ≤ 32
  room : S.P.T.r + S.P.T.l ≤ 2 ^ S.P.T.a
  two : 0 < S.P.T.r + S.P.T.l - 1
  dec : S.eM < S.dT
  pos0 : 0 < S.e0
  pos1 : 0 < S.e1
  le0 : S.e0 ≤ S.eM
  le1 : S.e1 ≤ S.eM
  joh0 : InJohnson (2 ^ S.P.T.a) S.dT S.e0
  joh1 : InJohnson (2 ^ S.P.T.a) S.dT S.e1

variable {S}

/-- Below the Johnson radius for the distance n - (K + 1) + 1, the hypothesis' condition holds: n K
< (n - e)^2. -/
theorem Sz.RadJ.cond (h : S.RadJ) {e : ℕ} (hJ : InJohnson (2 ^ S.P.T.a) S.dT e) :
    2 ^ S.P.T.a * (S.P.T.r + S.P.T.l - 1) < (2 ^ S.P.T.a - e) ^ 2 := by
  have h1 := h.room
  have h2 := h.two
  have h3 : S.P.T.r + S.P.T.l - 1 = 2 ^ S.P.T.a - S.dT := by
    unfold Sz.dT
    omega
  rw [h3]
  exact hJ

/-- **A guard: the conditions are met together beyond half the distance, at numbers of a full
size**: a code of 2^32 positions with 44,040,191 + 402,653,184 coefficients and the one radius
2,852,142,980 for the decoder and both folds. Twice that radius is above the distance 3,848,273,922.
By arithmetic outside Lean the code's sizes are the planner's at the full-size lines of the
setting "record with work", and the radius is the one reckoned for the one-time test; no
theorem here says so. An implication: no S is shown here (OnBytes/Slice/FullRecCodes.lean has one).
-/
theorem Sz.radJ_full (ha : S.P.T.a = 32) (hr : S.P.T.r = 44040191) (hl : S.P.T.l = 402653184)
    (hM : S.eM = 2852142980) (h0 : S.e0 = 2852142980) (h1 : S.e1 = 2852142980) :
    S.RadJ ∧ S.dT < 2 * S.eM := by
  have hd : S.dT = 3848273922 := by
    unfold Sz.dT
    rw [ha, hr, hl]
    norm_num
  have hJ : InJohnson (2 ^ S.P.T.a) S.dT 2852142980 := by
    rw [hd, ha]
    unfold InJohnson
    norm_num
  refine ⟨⟨by omega, by rw [ha, hr, hl]; norm_num, by omega, by omega, by omega, by omega,
    by omega, by omega, by rw [h0]; exact hJ, by rw [h1]; exact hJ⟩, by omega⟩

/-- The like at numbers of a small size: 2^23 positions, 65,535 + 524,288 coefficients, the radius
6,137,119, the distance 7,798,786. -/
theorem Sz.radJ_small (ha : S.P.T.a = 23) (hr : S.P.T.r = 65535) (hl : S.P.T.l = 524288)
    (hM : S.eM = 6137119) (h0 : S.e0 = 6137119) (h1 : S.e1 = 6137119) :
    S.RadJ ∧ S.dT < 2 * S.eM := by
  have hd : S.dT = 7798786 := by
    unfold Sz.dT
    rw [ha, hr, hl]
    norm_num
  have hJ : InJohnson (2 ^ S.P.T.a) S.dT 6137119 := by
    rw [hd, ha]
    unfold InJohnson
    norm_num
  refine ⟨⟨by omega, by rw [ha, hr, hl]; norm_num, by omega, by omega, by omega, by omega,
    by omega, by omega, by rw [h0]; exact hJ, by rw [h1]; exact hJ⟩, by omega⟩

variable (S)

/-- **Under `Cb.BCHKS46At`, and if at the pair of records r the rounds after the fifth close it
(`ClosesR`: shown of no decision here; `closes_manyR`, OnBytes/Slice/BatSemRec.lean, has it, for the
batching's round and a chain's rounds, from the batching's and the chain's statements, `IsRowsR`,
`WordTie` and a tie to the decision, `hsem`; of which decisions `hsem` is shown: the end of the next
docstring), the written link is round-by-round sound at r for `Sz.LangE2T`**, which has three ways
out, at radii below the Johnson radius (`Sz.RadJ`). The other hypotheses: (a) and (b) of
OnBytes/Slice/LinkSound.lean's head. -/
theorem link_sound_bchks (hA : BCHKS46At GF GE) (hR : S.RadJ) (d1 d2 d3 d4 d5 : PQ.RD)
    (tl : List PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool) (cut : ℕ)
    (L : Bool → ℕ) (hcut : S.P.cut = cut) (hpl : Function.Injective (S.lkR Z).D.pl)
    (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a)) (hev : ∀ a, ((S.lkR Z).N.om a).Evades)
    (hd : DrawsOK S d1 d2 d3 d4 d5) (εt : Err (PQ.uL (ckP .two) tl))
    (r : (S.lkR Z).X0) (hc : ClosesR S Z r d1 d2 d3 d4 d5 tl xs dec εt) :
    (written S d1 d2 d3 d4 d5 tl xs dec).Sound (fun _ y => S.LangE2T Z cut r y)
      (0, coreErrR S Z d1 d2 d3 d4 d5 (S.badJ S.e0) (S.badJ S.e1) L εt) :=
  fun x y hy => link_sound_at S Z r d1 d2 d3 d4 d5 tl xs dec cut S.dT _ _ _ _ L hcut
    (hasDist_genOf S.P.T hR.small hR.room) hR.dec hR.le0 hR.le1
    (mcaEq_bchksAt hA S.P.T hR.small hR.two (S.ixR Z) rfl S.e0 hR.pos0 (hR.cond hR.joh0))
    (list_johnson S.P.T hR.small hR.room (S.ixR Z) rfl S.e0 hR.joh0)
    (mcaEq_bchksAt hA S.P.T hR.small hR.two (S.ixR Z) rfl S.e1 hR.pos1 (hR.cond hR.joh1))
    (list_johnson S.P.T hR.small hR.room (S.ixR Z) rfl S.e1 hR.joh1) hpl hlist hev hd εt hc x y
    fun h => hy (Or.inr h)

/-- **LINK, BATCHING AND CHAIN IN ONE, UNDER THE HYPOTHESIS.** The rounds after the fifth are the
batching's round dA and the rounds of a chain c from the link's first stage on. All is at one pair
of records r; the rows are read off the statement after the five rounds, which holds the pair.
Chain, numbers and readings may be chosen for r. Lb: a bound on the lists of the group's code at the
chain's first radius. Concluded: what `link_sound_bchks` concludes, with the batching's and the
chain's counts behind the five rounds'. Asked besides, and shown of no decision, chain or setting
here: `Chain.Holds`, `IsRowsR`, `WordTie`, `hsem`, `SemOK`, the list Lb. At the two sizes of the
setting "record with work" OnBytes/Slice/FullRecLink.lean and OnBytes/Slice/SmallRecLink.lean leave
`hsem` alone of these (through `link_chain_joh`, OnBytes/Slice/LinkChainJoh.lean);
OnBytes/Slice/FullRecYes.lean and OnBytes/Slice/SmallRecYes.lean show `hsem` of every decision whose
yes gives the yes of the program's link at two keys with the items 0 and 1, each of which holds its
record of r if it passes the program's two tests. -/
theorem link_chain_rec (hA : BCHKS46At GF GE) (hR : S.RadJ) (N : RowNo S Z) {t₀ : ℕ}
    (d1 d2 d3 d4 d5 dA : PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool) (cut : ℕ)
    (L : Bool → ℕ) (hcut : S.P.cut = cut) (hpl : Function.Injective (S.lkR Z).D.pl)
    (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a)) (hev : ∀ a, ((S.lkR Z).N.om a).Evades)
    (hd : DrawsOK S d1 d2 d3 d4 d5) (c : Chain (S.sg t₀)) (dG Lb : ℕ) (hk : SemOK S c.rad dG)
    (hLb : (S.sg t₀).cIn.ListAt c.rad Lb) (hdA : SendsDraws dA 0 1 0 0) (hc : c.Holds)
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
      (0, coreErrR S Z d1 d2 d3 d4 d5 (S.badJ S.e0) (S.badJ S.e1) L
        (batErrR N Lb dA, c.errL)) :=
  link_sound_bchks S Z hA hR d1 d2 d3 d4 d5 (dA :: c.rds) xs dec cut L hcut hpl hlist hev hd _ r
    (closes_manyR N r d1 d2 d3 d4 d5 dA xs dec c _ rows w1 z1 g1
      (batSemR_of S Z N t₀ c.rad dG Lb hk hLb d2 dA hdA) hc hrows hw1 hsem)

end

end OnBytes.Slice
