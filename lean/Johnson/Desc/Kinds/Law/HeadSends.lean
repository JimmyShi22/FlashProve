-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadSends.lean.
What it does not show. A toy: an honest prover's tape built in Lean,
at the kind's own hearing text, for cells that hold: no file in scope, no stored proof, not what the
prover's program sends. NOT K06_law's MEMBER: it is the HEARING's half: that the 35 forms and
the claim on the weights are worth 0 needs true reads and honest cells of the head (
Law/OpenedNorm.lean, Law/OpenedHead.lean, from the letters that are paid here); that no draw is bad
under the block's ONE rule is row_true (RowTrue.lean), from NormTruth and the two SumTrueG that are
paid here; the block's decide, its seat and its record: not here. Premises: (dataOf c).Holds; the
ledger in front is WellLaid and Fresh. The head's own two tables are whatever the cells give:
nothing is asked of them. beta may be 0. c and mask are bare letters. No soundness, no probability,
nothing on hiding.
WHAT IT IS. THE SENDER OF ALL OF K6's ROUNDS, BESIDE THE TEXT (Head.lean: hear = the norm's hearing,
"normed", the head's own sumcheck).
  norm_glue       the five parts' returns make up the norm's hearing.
  same_front      a hearing that returns on two fronts of one list returns the same on both.
  normTruth_more  NormTruth looks at the norm's own rounds alone.
  smN_eq, smP_eq, tqP_eq   BY rfl: the two summands are Law/ProductEnds.lean's SmAB; the head's own
                  true round polynomial is Law/SumLaw.lean's at the head's point.
  logits_form     SumTrueG at the head's own sumcheck, in Law/Lemma2b.lean's letters.
  rounds_eq       Head.lean's table of rounds, bracketed as the sender lays its rounds.
  head_sendsC     head_sends with one clause more in front: where zt has lt
                  coordinates: Shaped D rs rounds (Law/HonestHear.lean): rs is, one for one, of the
                  make that Head.lean's table of rounds says: each round is rvOf of scalars and
                  drawn elements (no position, no matrix entry, no digest is drawn), as many as its
                  entry says; all that is drawn is among the given draws D: for the decision's test
                  on the rounds' shape.
  head_sends      FOR EVERY draw of all its rounds (canonical writings, the right lengths): rounds
                  rs, canonical, with hear F rs = some (H, G, []); NormTruth at rs; at whichever
                  stretches the hearing falls into: SumTrueG for "normed" and for the head's own;
                  the draws are the given; G is Fresh and WellLaid; AND IN EVERY WORLD WHOSE SLOTS
                  ARE THE HIDDEN SCALARS OF A LATER LEDGER: the norm's eight clauses
                  (Law/NormEnds.lean); for "normed" and for the head's own sumcheck: the claimed
                  sum's variable is worth the true sum (sigN; sigP), the sumcheck's own form on the
                  end values as shown is worth 0, the two end values' variables are worth the two
                  tables' extensions at the challenges (AtN, BtN; AtP, UtP).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ProductEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open Norm (lt ls d lPd T S2)
open Came (val bind_eq Consumes)
open OnBytes.PscRun (Later)
open Part.MaskedSum (rvOf readAll leadScalars movesOf ownSlots)
open OnBytes.Desc.First.P1 (mle)
open Came (vsG kG cvG tqG sEndG SmN sigN hSN AtN BtN)

variable [Sizes] [Policy] [Request] [Token]

/-- The five parts' returns, each on its own rounds, make up the norm's hearing. -/
theorem norm_glue {F Fa Fb Fc G : Fork} {r0 r1 r2 : Fmt.RoundView} {tS tP : List Fmt.RoundView} {pV : Point}
    {W P : Array Hid} {gam om : E} {S Sp : Sum}
    (h0 : drawPoint lt F [r0] = some (pV, F, []))
    (h1 : sendThenBatch 9 9 F [r1] = some ((W, gam), Fa, []))
    (h3 : level (zS pV) (Norm.squaresStart W gam #[]) Fa tS = some (S, Fb, []))
    (h4 : sendThenBatch 7 7 Fb [r2] = some ((P, om), Fc, []))
    (h5 : sumcheck pV 4 Fc tP = some (Sp, G, [])) :
    Norm.hear F ([r0] ++ ([r1] ++ (tS ++ ([r2] ++ (tP ++ []))))) =
      some ({ pV := pV, W := W, gam := gam, rhoI := #[], squares := S, P := P, om := om,
              products := Sp }, G, []) := by
  unfold Norm.hear Norm.hearPoint
  refine (bind_eq (all_rests (Came.consumes_drawPoint lt) h0 _)).trans ?_
  unfold Norm.hearRest
  refine (bind_eq (all_rests (Came.consumes_sendThenBatch 9 9) h1 _)).trans ?_
  dsimp only
  refine (bind_eq (show (if Norm.lNI == 0 then (pure #[] : Hear Point)
    else drawJoin Norm.lNI) Fa _ = some (#[], Fa, _) from rfl)).trans ?_
  refine (bind_eq (all_rests (Came.consumes_level _ _) h3 _)).trans ?_
  refine (bind_eq (all_rests (Came.consumes_sendThenBatch 7 7) h4 _)).trans ?_
  dsimp only
  refine (bind_eq (all_rests (Came.consumes_sumcheck pV 4) h5 _)).trans ?_
  rfl

/-- A hearing that returns on two fronts of one list of rounds returns the same on both. -/
theorem same_front {α : Type} {x : Hear α} (hx : Consumes x) {F G G' : Fork}
    {p p' q q' : List Fmt.RoundView} {a a' : α} (h : x F p = some (a, G, []))
    (h' : x F p' = some (a', G', [])) (e : p ++ q = p' ++ q') :
    a = a' ∧ G = G' ∧ p = p' ∧ q = q' := by
  have u := all_rests hx h q
  have u' := all_rests hx h' q'
  rw [e] at u
  have w := Option.some.inj (u.symm.trans u')
  simp only [Prod.mk.injEq] at w
  obtain ⟨w1, w2, w3⟩ := w
  subst w3
  exact ⟨w1, w2, List.append_cancel_right e, rfl⟩

variable [FinalNorm.In]

/-- NormTruth looks at the norm's own rounds alone. -/
theorem normTruth_more (c : NCells) (mask : Nat → E) (F : Fork) {rs : List Fmt.RoundView}
    {H : Norm.Heard} {G : Fork} (hh : Norm.hear F rs = some (H, G, []))
    (ht : NormTruth c mask F rs) (rest : List Fmt.RoundView) : NormTruth c mask F (rs ++ rest) := by
  refine ⟨ht.1, ?_⟩
  intro r0 r1 r2 tS tP left pV W P gam om Tt Fa Fb Fc G' S Sp hrs e0 e1 e3 e4 e5 eT
  have hg := norm_glue e0 e1 e3 e4 e5
  have e : rs ++ rest = ([r0] ++ ([r1] ++ (tS ++ ([r2] ++ (tP ++ []))))) ++ left := by
    rw [hrs]
    simp
  obtain ⟨_, _, hp, _⟩ := same_front Came.consumes_norm hh hg e
  exact ht.2 r0 r1 r2 tS tP [] pV W P gam om Tt Fa Fb Fc G' S Sp hp e0 e1 e3 e4 e5 eT

/-- Law/Normed.lean's summand is the product's. -/
theorem smN_eq (c : NCells) (mask : Nat → E) (F0 : Fork) :
    SmN c mask F0 = SmAB FinalNorm.zt (AtN c) (BtN c) mask F0 := rfl

variable [In]

/-- Law/Lemma2b.lean's summand is the product's; its true round polynomial is Law/SumLaw.lean's. -/
theorem smP_eq (c : Cells) (mask : Nat → E) (F0 : Fork) :
    SmP c mask F0 = SmAB zP (AtP c) (UtP c) mask F0 := rfl

theorem tqP_eq (c : Cells) (mask : Nat → E) (F0 : Fork) (Tv Cv : K) :
    tqP c mask F0 Tv Cv =
      tqG zP 2 (by omega) (SmP c mask F0) (sigP c) (hSP c mask F0) mask F0 Tv Cv := rfl

/-- The table of K6's rounds (Head.lean: rounds), bracketed as the sender lays its rounds. -/
theorem rounds_eq (pV : Point) (hz : pV.size = lt) (hzt : (FinalNorm.zt).size = lt) :
    rounds = (drawPoint.rounds lt ++ (sendThenBatch.rounds 9 9 ++ (level.rounds (zS pV).size ++
      (sendThenBatch.rounds 7 7 ++ (sumcheck.rounds pV.size 4 ++ []))))) ++
      (sumcheck.rounds (FinalNorm.zt).size 2 ++ (sumcheck.rounds zP.size 2 ++ [])) := by
  have hzP : zP.size = lt + lPd := by
    unfold zP halves
    simp [hzt]
  rw [zS_size pV hz, hz, hzt, hzP]
  unfold rounds Norm.rounds FinalNorm.rounds
  show drawPoint.rounds lt ++ sendThenBatch.rounds 9 9 ++ [] ++ level.rounds (0 + lPd + lt) ++
    sendThenBatch.rounds 7 7 ++ sumcheck.rounds lt 4 ++ sumcheck.rounds lt 2 ++
    sumcheck.rounds (lt + lPd) 2 = _
  rw [Nat.zero_add]
  simp only [List.append_assoc, List.append_nil, List.nil_append]

/-- SumTrueG at the head's own sumcheck, in Law/Lemma2b.lean's letters (LogitsTrue
has just this text). -/
theorem logits_form (c : Cells) (mask : Nat → E) (Fb : Fork) (tL : List Fmt.RoundView)
    (h : SumTrueG zP 2 (by omega) (SmP c mask Fb) (sigP c) (hSP c mask Fb) mask Fb tL) :
    ∀ R c0, readAll kP tL = some R → leadScalars kP tL = some [c0] →
      cvP mask Fb c0 = sigP c ∧
      ∀ i m, (movesOf Reading.gl kP.all R.rounds
          (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
        m.1 = tqP c mask Fb (rd (tgt c0)) (cvP mask Fb c0) (rd R.mu) (rd R.eps)
          (((movesOf Reading.gl kP.all R.rounds (addE R.mu (mulE R.eps (tgt c0)))).take i).map
            (·.2)) := by
  intro R c0 hR hl
  obtain ⟨hC, hq⟩ := h R c0 hR hl
  have hC' : cvP mask Fb c0 = sigP c := hC
  refine ⟨hC', fun i m hm => ?_⟩
  rw [hC']
  exact hq i m hm

/-- **K6's WHOLE HEARING, SENT HONESTLY, WITH THE HONEST END VALUES, FOR ALL DRAWS.** With
Shaped: the rounds are, one for one, of the make that Head.lean's table of rounds says. -/
theorem head_sendsC (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (pts : List E) (hpts : pts.length = lt)
    (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E)
    (hrS : rsS.length = (zS pts.toArray).size + 1) (hrP : rsP.length = pts.toArray.size + 1)
    (hrN : rsN.length = (FinalNorm.zt).size + 1) (hrL : rsL.length = zP.size + 1)
    (okp : ∀ x ∈ pts, okE x = true) (okg : okE gam = true) (okeS : okE epsS = true)
    (okd : okE down = true) (oko : okE om = true) (okeP : okE epsP = true)
    (okeN : okE epsN = true) (okeL : okE epsL = true)
    (okrS : ∀ x ∈ rsS, okE x = true) (okrP : ∀ x ∈ rsP, okE x = true)
    (okrN : ∀ x ∈ rsN, okE x = true) (okrL : ∀ x ∈ rsL, okE x = true) {m : Nat}
    (hF : Fresh F (9 + (ownSlots (callOf 0 (zS pts.toArray) 2).all + 2 +
      (7 + (1 + (ownSlots (callOf 1 pts.toArray 4).all + 4 +
        (1 + (ownSlots (callOf 1 FinalNorm.zt 2).all + 2 +
          (1 + (ownSlots (callOf 1 zP 2).all + 2 + m)))))))))) :
    ∃ (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork),
      ((FinalNorm.zt).size = lt →
        Shaped (pts ++ (gam :: down :: epsS :: rsS) ++ (om :: epsP :: rsP) ++ (epsN :: rsN) ++
          (epsL :: rsL)) rs rounds) ∧
      Canonical rs ∧ hear F rs = some (H, G, []) ∧ NormTruth c mask F rs ∧
      (∀ (pre tN tL : List Fmt.RoundView) (Hn : Norm.Heard) (Fa Fb F1 : Fork) (SN SL : Sum),
        rs = pre ++ tN ++ tL → Norm.hear F pre = some (Hn, Fa, []) →
        sumcheck FinalNorm.zt 2 Fa tN = some (SN, Fb, []) →
        sumcheck (FinalNorm.zt ++ halves lPd) 2 Fb tL = some (SL, F1, []) →
        SumTrueG FinalNorm.zt 2 (by omega) (SmN c mask Fa) (sigN c) (hSN c mask Fa) mask Fa tN ∧
        SumTrueG zP 2 (by omega) (SmP c.toCells mask Fb) (sigP c.toCells)
          (hSP c.toCells mask Fb) mask Fb tL) ∧
      Fresh G m ∧ WellLaid G ∧ H.1.pV = pts.toArray ∧ H.1.gam = gam ∧ H.1.om = om ∧
      H.1.squares.r = (rsS.take (zS pts.toArray).size).toArray ∧
      H.1.products.r = (rsP.take pts.toArray.size).toArray ∧
      H.2.1.normed.r = (rsN.take (FinalNorm.zt).size).toArray ∧
      H.2.2.logits.r = (rsL.take zP.size).toArray ∧
      ∀ (G' : Fork) (Wd : World K), Later G G' →
        (∀ j, F.next ≤ j → j < G.next → Wd.slot j = rd (hidden G' mask j)) →
        ((∀ s, s < 9 → val Wd (H.1.W.getD s {}).var = (dataOf c).sumWAt (ptK H.1.pV) 0 s) ∧
        (∀ n, n < 7 → val Wd (H.1.P.getD n {}).var = (dataOf c).prodRAt (ptK H.1.pV) 0 n) ∧
        val Wd (H.1.squares.left ((H.1.squares.end_ 0).shown * (H.1.squares.end_ 1).shown)) = 0 ∧
        (∀ j, j < 2 → val Wd (H.1.squares.end_ j).var =
          Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd H.1.gam)) (ptK H.1.squares.r)) ∧
        val Wd H.1.products.claimed.var = (Finset.range 7).sum (fun n =>
          rd H.1.om ^ n * (dataOf c).prodRAt (ptK H.1.pV) 0 n) ∧
        val Wd (H.1.products.left (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
          (fun n => H.1.om ^ (7 * i + n)) fun j => (H.1.products.end_ (4 * i + j)).shown)) = 0 ∧
        ∀ q, q < 4 → val Wd (H.1.products.end_ q).var =
          Blocks.ext lt (fieldK c q) (ptK H.1.products.r)) ∧
        (val Wd H.2.1.normed.claimed.var = sigN c ∧
        val Wd (H.2.1.normed.left
          ((H.2.1.normed.end_ 0).shown * (H.2.1.normed.end_ 1).shown)) = 0 ∧
        val Wd (H.2.1.normed.end_ 0).var =
          mle (vsG FinalNorm.zt).length (AtN c) (H.2.1.normed.r.toList.map rd) ∧
        val Wd (H.2.1.normed.end_ 1).var =
          mle (vsG FinalNorm.zt).length (BtN c) (H.2.1.normed.r.toList.map rd)) ∧
        (val Wd H.2.2.logits.claimed.var = sigP c.toCells ∧
        val Wd (H.2.2.logits.left
          ((H.2.2.logits.end_ 0).shown * (H.2.2.logits.end_ 1).shown)) = 0 ∧
        val Wd (H.2.2.logits.end_ 0).var =
          mle (vsG zP).length (AtP c.toCells) (H.2.2.logits.r.toList.map rd) ∧
        val Wd (H.2.2.logits.end_ 1).var =
          mle (vsG zP).length (UtP c.toCells) (H.2.2.logits.r.toList.map rd)) := by
  obtain ⟨rsA, Hn, G1, n0, n1, n2, n3, _, n5, n6, n7, n8, n9, n10, n11, n12⟩ := norm_sendsE c mask
    hW hH
    pts hpts gam epsS down om epsP rsS rsP hrS hrP okp okg okeS okd oko okeP okrS okrP hF
  obtain ⟨tN, SN, Gb, a0, a1, a2, a3, a4, _, a6, a7, _, a9, a10⟩ := product_sends FinalNorm.zt
    (AtN c) (BtN c) mask n6 (sigN c) (hSN c mask G1) n5 epsN rsN hrN okeN okrN
  have Wb : WellLaid Gb := Came.wl_sumcheck _ _ _ _ _ _ _ n6 a3
  obtain ⟨tL, SL, G, b0, b1, b2, b3, b4, _, b6, b7, _, b9, b10⟩ := product_sends zP (AtP c.toCells)
    (UtP c.toCells) mask Wb (sigP c.toCells) (hSP c.toCells mask Gb) a6 epsL rsL hrL okeL okrL
  have Wg : WellLaid G := Came.wl_sumcheck _ _ _ _ _ _ _ Wb b3
  have hhear : hear F (rsA ++ (tN ++ (tL ++ []))) =
      some ((Hn, { normed := SN }, { logits := SL }), G, []) := by
    unfold hear
    refine (bind_eq (all_rests Came.consumes_norm n2 _)).trans ?_
    refine (bind_eq (show FinalNorm.hear G1 (tN ++ (tL ++ [])) =
      some ({ normed := SN }, Gb, tL ++ []) from by
        unfold FinalNorm.hear
        rw [bind_eq (all_rests (Came.consumes_sumcheck _ _) a3 _)]
        rfl)).trans ?_
    refine (bind_eq (all_rests (Came.consumes_sumcheck _ _) b3 _)).trans ?_
    rfl
  refine ⟨_, _, G, ?_, ?_, hhear, normTruth_more c mask F n2 n3 _, ?_, b6, Wg, n7, n8, n9, n10, n11,
    a9, b9, ?_⟩
  · intro hzt
    rw [rounds_eq pts.toArray (by rw [List.size_toArray, hpts]) hzt]
    exact (n0.mono (in_first _ _ _)).append ((a0.mono (in_second _ _ _)).append
      ((b0.mono (in_third _ _ _)).append (shaped_nil _)))
  · exact canonical_append n1 (canonical_append a2 (canonical_append b2
      (by intro r hr; simp at hr)))
  · intro pre tN' tL' Hn' Fa Fb F1 SN' SL' hrs e1 e2 e3
    have e : rsA ++ (tN ++ (tL ++ [])) = pre ++ (tN' ++ tL') := by
      rw [hrs, List.append_assoc]
    obtain ⟨_, x2, _, x4⟩ := same_front Came.consumes_norm n2 e1 e
    subst x2
    obtain ⟨_, y2, y3, y4⟩ := same_front (Came.consumes_sumcheck _ _) a3 e2 x4
    subst y2 y3
    have y5 : tL = tL' := by simpa using y4
    subst y5
    exact ⟨a7, b7⟩
  · intro G' Wd hL hWs
    have L01 : Later F G1 := keeps_norm _ _ _ _ _ n2
    have L1b : Later G1 Gb := keeps_sumcheck _ _ _ _ _ _ _ a3
    have Lbg : Later Gb G := keeps_sumcheck _ _ _ _ _ _ _ b3
    have k01 := L01.next
    have k1b := L1b.next
    have kbg := Lbg.next
    have fN := Came.filled_rangeG FinalNorm.zt 2 n6 a3
    have fL := Came.filled_rangeG zP 2 Wb b3
    have hsN : sEndG FinalNorm.zt 2 G1 + 2 = Gb.next := by
      rw [a4]
      rfl
    have hsL : sEndG zP 2 Gb + 2 = G.next := by
      rw [b4]
      rfl
    refine ⟨n12 G' Wd ((L1b.trans Lbg).trans hL) fun j j1 j2 => hWs j j1 (by omega), ?_, ?_⟩
    · exact a10 Wd fun j j1 j2 => by
        rw [hWs j (by omega) (by omega), hidden_later mask (Lbg.trans hL) (fN j j1 (by omega))]
    · exact b10 Wd fun j j1 j2 => by
        rw [hWs j (by omega) j2, hidden_later mask hL (fL j j1 (by omega))]

/-- The same without Shaped. -/
theorem head_sends (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (pts : List E) (hpts : pts.length = lt)
    (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E)
    (hrS : rsS.length = (zS pts.toArray).size + 1) (hrP : rsP.length = pts.toArray.size + 1)
    (hrN : rsN.length = (FinalNorm.zt).size + 1) (hrL : rsL.length = zP.size + 1)
    (okp : ∀ x ∈ pts, okE x = true) (okg : okE gam = true) (okeS : okE epsS = true)
    (okd : okE down = true) (oko : okE om = true) (okeP : okE epsP = true)
    (okeN : okE epsN = true) (okeL : okE epsL = true)
    (okrS : ∀ x ∈ rsS, okE x = true) (okrP : ∀ x ∈ rsP, okE x = true)
    (okrN : ∀ x ∈ rsN, okE x = true) (okrL : ∀ x ∈ rsL, okE x = true) {m : Nat}
    (hF : Fresh F (9 + (ownSlots (callOf 0 (zS pts.toArray) 2).all + 2 +
      (7 + (1 + (ownSlots (callOf 1 pts.toArray 4).all + 4 +
        (1 + (ownSlots (callOf 1 FinalNorm.zt 2).all + 2 +
          (1 + (ownSlots (callOf 1 zP 2).all + 2 + m)))))))))) :
    ∃ (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork),
      Canonical rs ∧ hear F rs = some (H, G, []) ∧ NormTruth c mask F rs ∧
      (∀ (pre tN tL : List Fmt.RoundView) (Hn : Norm.Heard) (Fa Fb F1 : Fork) (SN SL : Sum),
        rs = pre ++ tN ++ tL → Norm.hear F pre = some (Hn, Fa, []) →
        sumcheck FinalNorm.zt 2 Fa tN = some (SN, Fb, []) →
        sumcheck (FinalNorm.zt ++ halves lPd) 2 Fb tL = some (SL, F1, []) →
        SumTrueG FinalNorm.zt 2 (by omega) (SmN c mask Fa) (sigN c) (hSN c mask Fa) mask Fa tN ∧
        SumTrueG zP 2 (by omega) (SmP c.toCells mask Fb) (sigP c.toCells)
          (hSP c.toCells mask Fb) mask Fb tL) ∧
      Fresh G m ∧ WellLaid G ∧ H.1.pV = pts.toArray ∧ H.1.gam = gam ∧ H.1.om = om ∧
      H.1.squares.r = (rsS.take (zS pts.toArray).size).toArray ∧
      H.1.products.r = (rsP.take pts.toArray.size).toArray ∧
      H.2.1.normed.r = (rsN.take (FinalNorm.zt).size).toArray ∧
      H.2.2.logits.r = (rsL.take zP.size).toArray ∧
      ∀ (G' : Fork) (Wd : World K), Later G G' →
        (∀ j, F.next ≤ j → j < G.next → Wd.slot j = rd (hidden G' mask j)) →
        ((∀ s, s < 9 → val Wd (H.1.W.getD s {}).var = (dataOf c).sumWAt (ptK H.1.pV) 0 s) ∧
        (∀ n, n < 7 → val Wd (H.1.P.getD n {}).var = (dataOf c).prodRAt (ptK H.1.pV) 0 n) ∧
        val Wd (H.1.squares.left ((H.1.squares.end_ 0).shown * (H.1.squares.end_ 1).shown)) = 0 ∧
        (∀ j, j < 2 → val Wd (H.1.squares.end_ j).var =
          Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd H.1.gam)) (ptK H.1.squares.r)) ∧
        val Wd H.1.products.claimed.var = (Finset.range 7).sum (fun n =>
          rd H.1.om ^ n * (dataOf c).prodRAt (ptK H.1.pV) 0 n) ∧
        val Wd (H.1.products.left (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
          (fun n => H.1.om ^ (7 * i + n)) fun j => (H.1.products.end_ (4 * i + j)).shown)) = 0 ∧
        ∀ q, q < 4 → val Wd (H.1.products.end_ q).var =
          Blocks.ext lt (fieldK c q) (ptK H.1.products.r)) ∧
        (val Wd H.2.1.normed.claimed.var = sigN c ∧
        val Wd (H.2.1.normed.left
          ((H.2.1.normed.end_ 0).shown * (H.2.1.normed.end_ 1).shown)) = 0 ∧
        val Wd (H.2.1.normed.end_ 0).var =
          mle (vsG FinalNorm.zt).length (AtN c) (H.2.1.normed.r.toList.map rd) ∧
        val Wd (H.2.1.normed.end_ 1).var =
          mle (vsG FinalNorm.zt).length (BtN c) (H.2.1.normed.r.toList.map rd)) ∧
        (val Wd H.2.2.logits.claimed.var = sigP c.toCells ∧
        val Wd (H.2.2.logits.left
          ((H.2.2.logits.end_ 0).shown * (H.2.2.logits.end_ 1).shown)) = 0 ∧
        val Wd (H.2.2.logits.end_ 0).var =
          mle (vsG zP).length (AtP c.toCells) (H.2.2.logits.r.toList.map rd) ∧
        val Wd (H.2.2.logits.end_ 1).var =
          mle (vsG zP).length (UtP c.toCells) (H.2.2.logits.r.toList.map rd)) := by
  obtain ⟨rs, H, G, _, h⟩ := head_sendsC c mask hW hH pts hpts gam epsS down om epsP epsN epsL rsS
    rsP rsN rsL hrS hrP hrN hrL okp okg okeS okd oko okeP okeN okeL okrS okrP okrN okrL hF
  exact ⟨rs, H, G, h⟩

end VerifiableInference.Desc.Kinds.Head.Law
