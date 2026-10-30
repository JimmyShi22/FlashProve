-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/HeldBehind.lean: the kind "the code switch" (K2): UNDER THE
HEAD ALONE, AT EVERY PLACE OF THE KIND ON THE FIRST CHAIN: BEHIND A YES OF THE PLACE's BLOCK THE
STATE STILL HOLDS THE SAMPLE OF EVERY TENANT WHOSE PIN IS OPEN THERE (`samplesHeld`,
Johnson/Desc/First/Borders.lean), from the like and the promise's six tests in front, at a reached
state. Statements with their proofs; no definition. A joining of the library's theorems.

  `way_book`        the way in leaves the book, at each of the three sorts of place
  `fence_at`        at a reached state in front of a place of the kind: what the front of the
                    switch's own step announces is the library's written list `sentW`, at the first
                    chain's codes, and passes the test `noticesFitB`
  `hnew_at_yes`     the library's `hnew_of_fence` (Johnson/P1K2R/TieTwoPays.lean) AT A YES OF THE
                    BLOCK's OWN STEP: its proof without the line that draws the yes out of an accept
                    of the reduction: that yes is a premise here
  `k2_held_behind`  THE END, at the letters `P5J.At.N`, `P5J.At.links`, `P5J.At.ps`, `P5J.mgAtAll`:
                    by the library's `K2.held_at_place` (Johnson/Top/H0/Tw/K2C/HeldAtPlace.lean)

Limits. The chain's first tree is 0: the yes is taken there. No example of the head is shown here;
the library's `head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one
under four premises on the three public files.


The line that strikes an instance below stands in the
imported file too. Nothing on any property.
-/
import Johnson.P1K2R.LastLineOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K2 (noticesFitB sentFitB sent_of_test hall_of_test)
open VerifiableInference.Desc.First.K2Hands (sentW)
open VerifiableInference.Desc.First.K2Caller
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open H2K.JointK (Sits)
open IM (openAt)
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

theorem way_book {m : Nat} {enter : S → Except String S} {p : K2.P2} (w : WayAt m enter p) :
    ∀ s t, enter s = .ok t → t.book = s.book := by
  rcases w with ⟨-, -, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩
  · exact P1K2.hbk_id e
  · exact P1K2.hbk_id e
  · exact P1K2.hbk_fin e

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

theorem fence_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B')
    (hsh : Z.first.shape = K2Hands.shW) {m k : Nat} (ek : k2NoAt m = k)
    {enter : S → Except String S} {p : K2.P2} (w : WayAt m enter p) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) :
    ∀ t, enter s = .ok t → ∀ x, K2.frontAt p t = some x →
      switchNotices x.T x.others = (sentW (m + 1)).toArray ∧ x.st.codes = Z.first.codes ∧
        noticesFitB (switchNotices x.T x.others) = true := by
  subst ek
  intro t he x hx
  rcases w with ⟨h23, hq, hent⟩ | ⟨rfl, hq, hent⟩ | ⟨rfl, hq, hent⟩
  · obtain rfl := hent _ _ he
    have e : k2NoAt m = 14 * (m + 1) + 2 := by
      unfold k2NoAt
      rw [if_pos h23]
    rw [e] at hr
    obtain ⟨h1, h2⟩ := P1K2.noticesW_link hS hR O hsh h23 hr hq hx
    exact ⟨by rw [← h2], h1, P1K2.noticesFit_of_written (by omega) (by omega) h2⟩
  · obtain rfl := hent _ _ he
    obtain ⟨h1, h2⟩ := P1K2.noticesW_head hS hR O hsh hr hq hx
    exact ⟨by rw [← h2], h1, P1K2.noticesFit_of_written (by omega) (by omega) h2⟩
  · obtain ⟨h1, h2⟩ := P1K2.noticesW_fin hS hR O hsh hr (hent _ _ he) hq hx
    exact ⟨by rw [← h2], h1, P1K2.noticesFit_of_written (by omega) (by omega) h2⟩

end

theorem hnew_at_yes {N : Numbers} {ps : List VerifiableInference.Desc.Place} {k g : Nat}
    {codes : Codes}
    {sent : Array OracleNotice} (hT : sentFitB N g ps[k]? codes sent = true) {p : K2.P2}
    {enter : S → Except String S} {leave : S → S → Except String S} {B : Block S Cl}
    (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hbk : ∀ s t, enter s = .ok t → t.book = s.book) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn} {n₁ : Nat}
    (hy : B.step ft s rs cols = .ok (s', n₁))
    (hbook : bookAt N ps[k]? s = true)
    (hfence : ∀ t, enter s = .ok t → ∀ x, K2.frontAt p t = some x →
      switchNotices x.T x.others = sent ∧ x.st.codes = codes ∧
        noticesFitB (switchNotices x.T x.others) = true) :
    ∀ t, enter s = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
      K2.frontAt p t = some x ∧
      layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
      sameMembers ((List.range n).map fun i =>
        (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent g 0) = true ∧
      ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
        nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows := by
  intro t he
  obtain ⟨t₁, t', e1, e2, -⟩ := hSit.step ft s s' rs cols n₁ hy
  obtain rfl : t₁ = t := Except.ok.inj (e1.symm.trans he)
  obtain ⟨r₁, r₂, gs, -, hd⟩ := K2.k2_step_two e2
  obtain ⟨x, lay, f, hl, -, -⟩ := K2.yes_seated hd
  have hx := K2.frontAt_of f
  obtain ⟨h1, h2, h3⟩ := hfence t₁ he x hx
  refine ⟨x, lay, (switchNotices x.T x.others).size - 1, hx, hl, ?_, hall_of_test h3 rfl rfl⟩
  rw [hbk _ _ he]
  exact sent_of_test hT hbook h1 h2 hl rfl

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SAMPLES ARE STILL HELD BEHIND.** -/
theorem k2_held_behind (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place}
    (ha : P5J.At.ps[k]? = some pl) (hk : pl.kind = KindName.K2) {B : Block S Cl}
    (hB : cF.blocksInOrder[k]? = some B) {z : ProofFile.InstPub} {s s' : S}
    (hf : Meaning.K2.FkR Zp cF z k s) (hy : IM.Yes 0 B s s')
    (hx : IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (P1K2.EQ (P5J.mgAtAll Hd) P5J.At.links P5J.At.ps z) k s = true)
    (hH : samplesHeld (P5J.At.N Zp cF) (P5J.mgAtAll Hd) (openAt P5J.At.links P5J.At.ps k)
      (z, s) = true) :
    samplesHeld (P5J.At.N Zp cF) (P5J.mgAtAll Hd) (openAt P5J.At.links P5J.At.ps (k + 1))
      (z, s') = true := by
  have hp := P5J.pins_of_laid Hd.toAtMg.scope Hd.toAtMg.laid
  obtain ⟨B₀, enter, leave, hB₀, hS, hL, -, -, hW, -, -⟩ := P1K2.k02_sits7_pAt_at Hd.toAtMg
    (H2K12.spots_atAll Hd hp.2) (P1K2.links25_atAll Hd) k pl ha hk
  obtain rfl : B₀ = B := Option.some.inj (hB₀.symm.trans hB)
  obtain ⟨Bs, base, O⟩ := Hd.toAtMg.laid.opened
  have Aw := K2Ties.at_written Hd.toAtMg.scope Hd.toAtMg.laid hp.1
  have At' := K2Ties.at_told hp.2 Aw
  have ek := P1K2.k2No_mOf ha hk
  have hT := t23_fit Aw At' hW
  rw [ek] at hT
  have r := reach_raw hf
  have r' := IM.reach_next r hB hy
  have hpl := P1K2.plan_of O Hd.toAtMg.laid.planOk
  obtain ⟨-, -, -, c4, -⟩ := IM.xk_parts hx
  obtain ⟨rs, cols, n₁, hy⟩ := hy
  have hI : smpHeld s.st s.book (P5J.At.N Zp cF).index.1 (P5J.At.N Zp cF).index.2 = true :=
    (K2Ties.hheld_paid (dC Hd) mgBase _ _ (z, s)).symm.trans
      (List.all_eq_true.1 hH _ (P1K2.hidx_at _ ha hk))
  have hall := K2.held_at_place hS hL.1 hL.2 (way_book hW) hy
    ((bookFitsB_iff _).1 (Meaning.K2.atFirstFits_all O hpl r))
    ((bookFitsB_iff _).1 (Meaning.K2.atFirstFits_all O hpl r')) P1K2.seedReads
    (hnew_at_yes hT hS (way_book hW) hy c4
      (fence_at Hd.toAtMg.scope Hd.toAtMg.reads O
        (P1K2.written3 Hd.toAtMg.scope O.pub hp.1).2.1 ek hW hf)) hI
  unfold samplesHeld
  rw [show sampledIn (P5J.At.N Zp cF) (openAt P5J.At.links P5J.At.ps (k + 1)) = _ from
    P1K2.hsam_at _ ha hk]
  exact List.all_eq_true.2 fun q hq =>
    (K2Ties.hheld_paid (dC Hd) mgBase q.1 q.2 (z, s')).trans (hall q hq)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.way_book
#print axioms ProofFile.Honest.K2.Law.fence_at
#print axioms ProofFile.Honest.K2.Law.hnew_at_yes
#print axioms ProofFile.Honest.K2.Law.k2_held_behind
