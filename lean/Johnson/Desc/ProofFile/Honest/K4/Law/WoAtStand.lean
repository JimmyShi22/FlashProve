-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoAtStand.lean

What is here. Three of the seven clauses that the pending row's item asks (`K4WoAsks`,
Law/WoOf.lean: recs · value · point) at a state behind the step of the member of the layers' own
rounds (kind K4), from a stand (`K4Stand`, Law/SlotsTrue.lean); and so `K4WoAsks` there from the
two ties on the witness (Law/WoTies.lean). Statements with their proofs: calls of other writers'
statements, after the proof of `merge_stand` (Law/OwnAtStand.lean).

  `wo_left_stand`: there is a list cr such that recs, value and point hold of o.wo, at the matrix
      of the honest input's weights and at the reading of the first end coin of whatever the lent
      row hands the merge's part.
  `k4WoAsks_stand`: K4WoAsks at every continuation of the challenges.

Limits. CONDITIONAL. No example of K4Stand is known; at a thread none of whose steps accepts all
holds emptily. HYPOTHESES BESIDE THE STAND AND THE THREAD's SENTENCE: two of the ties of
Law/ScriptAt.lean (what the lookup has sampled; the tokens) · that the run "back" returns from
some ledger later than the one that the step leaves (Law/RunsAtStand.lean draws that from the
library's seven tests) · hU: a public test on every unit of the weights' layout (the library's
`unitOK_of_layout`, Johnson/Road/FormsKeysWLay.lean, has it of every layout that wsLayOf returns:
Law/WoShare.lean takes it so) · for the second statement: the two ties on the witness, the first
at the coin that the book lends the merge's part for its end value; that the data's layout is the
public data's; that what is left at the seat's state is o.wo. THE FIRST STATEMENT SAYS «THERE IS A
LIST cr» AND NOTHING OF WHAT cr IS: in its proof cr is the honest parts' claims, each with its
coefficient, but no clause says so. Equations between machine words and their readings. THE READER
rw OF THE PILE OF PENDING ROWS IS TYPED HERE AT d.lay.lk COLUMN BITS; the library's own reader at
its full-size structure is typed at another term for that number, equal to it by a public fact
alone: SO THESE STATEMENTS CANNOT BE CALLED AT THAT READER AS THEY STAND: the forms to call are
Law/WoShareK.lean (general in the number of column bits) and, at the first chain's thread,
Law/WoHead.lean and Law/WoTop.lean. Nothing on soundness, on completeness or on any other
property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.MergeLed
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE)
open OnBytes.Model (Reading Aff Fork WsClaim WsUnit wsRowPart wsEpsT)
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Sized Later)
open OnBytes.Road (Wm fmAt UnitOK)
open OnBytes.Desc.First.K4 (Par k0 formsBack seatS)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt sumAt_some own_ground)
open Johnson.Desc.First.Walk.Law (leftOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **recs · value · point AT A STAND.** CONDITIONAL on the named hypotheses. -/
theorem wo_left_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (hTk : K4TokensTieAt tokens s m)
    {F₁ F₂ : Fork} {fs₂ : Array Aff} (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂))
    (hU : ∀ (i : ℕ) (u : WsUnit), Q.P.wsLay.U[i]? = some u → UnitOK Q.P.wsLay.lk u) :
    ∃ (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
      (name endName : String) (cp : SumCoins name endName (mergeSum Q))
      (cr : List (WsClaim × OnBytes.E)),
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c ∧
      SumAt c (k0 Q.g + 15) name endName (mergeSum Q) cp ∧
      o.wo.recs = cr.map (fun z =>
        wsRowPart Q.P.wsLay z.1 (mulE z.2 (wsEpsT Q.P.wsLay z.1 o.wo.rm))) ∧
      Reading.gl.val o.wo.fvp =
        fmAt Reading.gl Q.P.wsLay (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) cr
            o.wo.rm +
          Reading.gl.val ((endRun cp).getD 0 zeroE) * Reading.gl.val o.wo.beta ∧
      o.wo.rm.size = Q.P.wsLay.lk := by
  obtain ⟨a, a₀, fo, _, ha0, haF, _, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  have hSd : Sized a.F := by
    rw [haF]
    exact Z.sized a₀ ha0
  have h' : OnBytes.Desc.First.K4.hear OnBytes.Desc.First.K4.engFl { Q.P with tokv := s.tokv } Q.hp
      Q.g fo a.F (OnBytes.K.Kc.paired (roundsOf y.1) (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)) =
      some (o, A.F, []) := hh
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ :=
    OnBytes.Road.K4.own_ledG hSd h'
  obtain rfl : o.H.fo = fo := led_fo L
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hp := k4RowIn_at Q 15
  obtain ⟨cp, hcp⟩ := sumAt_some c (k0 Q.g + 15) _ _ (mergeSum Q) hp
  have ha := k4_alone (V := Unit) Pl (k0 Q.g + 15) _ _ (mergeSum Q) hp cp hcp
  have hn : ∀ a b : String, (SumLaw.sumGs a b (mergeSum Q)).length = Q.P.wsLay.lk + 3 :=
    fun a b => by
      rw [SumLaw.sumGs_count]
      show (List.replicate (Q.P.wsLay.lk) _).length + 3 = _
      rw [List.length_replicate]
  have hdr := k4_draws (stand_elems Z) 15 (Q.P.wsLay.lk) rfl
    ((mergeSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (SumLaw.frontOf (entryAt Q cells weights tokens look m ds (rE Q.P Q.hp Q.g + 1))
        (seenAt m y (rE Q.P Q.hp Q.g + 1))))
    (by
      show (withPoints (List.replicate (Q.P.wsLay.lk) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn, k4_moves_merge] at ha
  rw [k4_moves_merge] at hdr
  have e6 := (k4StartAt_eq Q).2.2.2.2.2.2
  obtain ⟨F1, _, hW, _⟩ := OnBytes.Desc.First.K4.formsBack_some hb
  obtain ⟨_, _, hO, _, _⟩ := own_ground Z
  obtain ⟨g, _, h2, _, hzk, _⟩ := hLk
  obtain rfl : g = o.H.fo := Option.some.inj (h2.symm.trans (stand_look Z))
  obtain ⟨cls, _, hr, hv, hq⟩ := merge_value_led m.st.heard h' hSd L ds (stand_drawn hy _)
    (stand_reach Z) (k4_heard_front Z.seat hT) _ _ cp
    (entryAt Q cells weights tokens look m ds (rE Q.P Q.hp Q.g + 1))
    (seenAt m y (rE Q.P Q.hp Q.g + 1)) _ _ (by rw [e6]; rfl) hzk hTk.symm
    (stand_fits Z.seat hT) (stand_own_fits Z hT _) hdr ha
    (by rw [e6]; exact tapeIs_paired_drop _ _ _ _) F₁ F1
    (OnBytes.Desc.First.K4.later_fo h1) (h1.sized hO.sized) hW hU
  exact ⟨c, _, _, cp, _, Pl.lent, hcp, hr, hv, hq⟩

/-- **`K4WoAsks` AT A STAND, AT EVERY CONTINUATION.** CONDITIONAL on the named hypotheses. Ix: the
first tie, at the reading of the first end coin of whatever the lent row hands the merge's part. -/
theorem k4WoAsks_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (hTk : K4TokensTieAt tokens s m)
    {F₁ F₂ : Fork} {fs₂ : Array Aff} (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂))
    (hU : ∀ (i : ℕ) (u : WsUnit), Q.P.wsLay.U[i]? = some u → UnitOK Q.P.wsLay.lk u)
    {d : PubData} {nR : Nat} {rw : T.P × First.S → T.Wt → PileWit nR d.lay.lk}
    (hlay : d.lay = Q.P.wsLay) (hleft : leftOf (T.seat k y.2 s').2 = some o.wo)
    (Ix : ∀ c name endName (cp : SumCoins name endName (mergeSum Q)),
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c →
      SumAt c (k0 Q.g + 15) name endName (mergeSum Q) cp →
      K4IndexTieAt T rw k y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (Wt : K4WeightsTieAt T d rw k y.2 s'
      (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w)) (ds' : List Fmt.Drawn) :
    K4WoAsks d (T.seat k y.2 s').2
      (rw (T.seat k y.2 s') (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) := by
  obtain ⟨c, name, endName, cp, cr, hc, hcp, hr, hv, hq⟩ := wo_left_stand Z hT hLk hTk h1 hb hU
  exact k4WoAsks_of_ties hleft _ cr _ (by rw [hlay]; exact hr) (by rw [hlay]; exact hv)
    (by rw [hlay]; exact hq) (Ix c name endName cp hc hcp) Wt ds'

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.wo_left_stand
#print axioms ProofFile.Honest.K4.k4WoAsks_stand
