-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/HeadValsReach.lean: THE LOOKUP ON THE HEAD's OWN DIGITS (member 345 of the
proof file's own first chain): THE TABLE's OWN TEST ON VALUES, headVals
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ClaimReturns.lean), ACCEPTS AT EVERY STATE THAT IS
REACHED AT BORDER 345; and so, at the first chain's thread at the full size, the rule for
acceptance's premise on values holds at 345. Under the head P5J.AtMgA. A joining of laws; nothing is
evaluated.

What the test asks (headVals_of, .../Thread/HeadValsOf.lean): the chain stands in the head's link;
what the head heard and its tables are laid; the covered positions can be made; a public test on the
layout; THE CHECKED TOKEN OF EVERY COVERED POSITION IS AN ENTRY OF THE VOCABULARY.

By what. The library has every piece at the chain's own members (Johnson/P4R/WaK6At346.lean): a yes
at 341 is a yes of the head's own block (P4.yes_341); behind it what the head heard is heardOf at
the letters in front (Came.x_behind, Came.given_ok, Johnson/Desc/Kinds/Law/); heardOf lays at a
checked position the token under test and 0 elsewhere (Johnson/Stored/HeadSeat.lean); that token is
below V where the request passes its test and the reply's token is below V (win_lt,
Kinds/Law/Ints.lean; StartPays.start_pays; tokSmall_pays); 342, 343 and 344 leave what the head
heard (P4.kept_342, kept_343, kept_344). The request's test and the covered positions at a reached
state: ReqReplyReach.lean. The public test: layoutOk_at (HeadDigitsFree.lean).

  `peel_raw`: one step back along "reached" (P4.reach_last, P4.step_yes).
  `tokSmall_reach`: from border 339 on every element in the reply's seat is a token of V.
  **`win_behind_block`**: GENERAL IN THE PUBLIC RECORD: behind a yes of the head's own block, where
    the request's test holds in front and the reply's seat holds tokens alone: the chain stands in
    the head's link, what the head heard is laid, and EVERY entry of its list of checked tokens is
    below V.
  `tables_342`, `t_kept_343`, `t_kept_344`: the head's tables are laid behind 342 and left by 343
    and 344: the library's own roads to these three seats, walked once more for the field t, of
    which its KeptW does not speak.
  **`heard_at_345`**: at every state reached at border 345 (THE RAW FAMILY): the four facts on the
    head's record.
  **`headVals_reach`**: so headVals at the public part's record accepts there.
  `tab_345_vals`; **`vals_345_reach`**: so does the table's own test at 345.
  **`valuesJ_345`**: ValuesJ ‹lettersHead's thread› Said J ‹the table› fall 345: at every "what is
    said", every family and every fall.

Limits. ONE OF 358 MEMBERS; ONE PREMISE OF THE RULE THERE. Of every reached state, whoever plays: so
that anything is reached is not said. The thread's laws and the test headVals are not of the
library. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed`
accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named
sets of public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.

-/
import Johnson.AtFull.Shape.ValuesAtThread
import Johnson.AtFull.Shape.TableSites
import Johnson.P4R.WaK6At346
import Johnson.Desc.Kinds.Law.TokenSmall
import Johnson.Desc.Kinds.Law.StartPays
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.Desc.Kinds.Law.ReadsLaidAlike
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadValsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM)
open ProofFile.Honest (ProverCoinCounts Prover Local Coins Mid ValuesJ)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr (headVals headVals_of)
open Johnson.Desc.First.Walk.Tied (Reach)

/-! ## 1 Tools -/

/-- One step back along "reached". -/
theorem peel_raw {C XP : Type} {bs : List (Block S C)} {start : XP → S} {k : Nat} {z : XP} {t : S}
    (h : Reach 0 bs start (k + 1) (z, t)) :
    ∃ (s : S) (B : Block S C) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      Reach 0 bs start k (z, s) ∧ bs[k]? = some B ∧ B.decide s rs gs = .ok t := by
  obtain ⟨s, b, hr, hb, hy⟩ := P4.reach_last h
  obtain ⟨rs, gs, hd⟩ := P4.step_yes hy
  exact ⟨s, b, rs, gs, hr, hb, hd⟩

/-- **Behind a yes of the head's own block every entry of the list of checked tokens is below
V.** -/
theorem win_behind_block (W : Verify.Public) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) 24).decide s rs gs = .ok s')
    (hq : s.reqOk (2 ^ W.hS.lt) W.hS.V = true) (hT : TokSmall W.hS.V s) :
    ∃ a x, s'.here = .head a ∧ a.x = some x ∧ ∀ t, x.win.getD t 0 < W.hS.V := by
  obtain ⟨g, H, F1, a, gk, Q, hg, -, -, -, rfl⟩ := Came.x_behind W.hS (readsOf W) (workOf W) 24 hd
  obtain ⟨z, y, -, hy, -, rfl⟩ := Came.given_ok _ _ _ _ hg
  have hyV : y < (parOf W.hS (workOf W)).sizes.V := tokSmall_pays W s hT y hy
  have hreq : (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true :=
    StartPays.start_pays W.hS (workOf W) (readsOf W) s s hq rfl
  refine ⟨_, _, rfl, rfl, fun t => ?_⟩
  letI : Sizes := (parOf W.hS (workOf W)).sizes
  letI : Policy := (parOf W.hS (workOf W)).policy
  letI : Request := (seatAt W.hS (readsOf W)).request s
  letI : Token := ⟨y⟩
  have key : (((Array.range VerifiableInference.Desc.Kinds.Norm.T).map fun t =>
      if checked t then win t else 0).getD t 0) < V := by
    by_cases ht : t < VerifiableInference.Desc.Kinds.Norm.T
    · have e : (((Array.range VerifiableInference.Desc.Kinds.Norm.T).map fun t =>
          if checked t then win t else 0).getD t 0) = if checked t then win t else 0 := by
        simp [Array.getD, ht]
      rw [e]
      split
      · exact win_lt hreq hyV t
      · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hyV
    · have e : (((Array.range VerifiableInference.Desc.Kinds.Norm.T).map fun t =>
          if checked t then win t else 0).getD t 0) = 0 := by
        simp [Array.getD, ht]
      rw [e]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hyV
  exact key

/-! ## 2 The head's tables -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Behind a yes at 342 the head's tables are laid. -/
theorem tables_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S ProofFile.Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hB : c.blocksInOrder[342]? = some b0)
    (hd : b0.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ o tt, t.here = .head o ∧ o.t = some tt := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, h1, h2, hX, -, hla⟩ :=
    IM.k1_reads_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have hd2 : (IM.k1Reads Z Bs.G₀ 24 Xl (IM.k1Ix 24 false + 1) reads).decide s rs gs = .ok t :=
    ((IM.yes_alone hla (by decide) s t rs gs).1 hd).1
  obtain ⟨-, l, hl, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : l = Xl := Option.some.inj (hl.symm.trans hX)
  have hp : (if l.kind == 0 || l.kind == 1 then 4 else 5) = 5 := by
    rw [hk]
    rfl
  have hq : IM.k1Quiet Bs.G₀ 24 l = VerifiableInference.Desc.K8.ReadsQuiet.head
      ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ := by
    unfold IM.k1Quiet
    simp only [hp]
    exact VerifiableInference.Reads.AtSeat.quiet_is Bs.G₀ 24 l _ _ _ hk (g := l.g) (by
      rw [List.getElem?_map, Array.getElem?_toList, hl]
      show some (l.kind, l.g) = some (2, l.g)
      rw [hk])
  unfold IM.k1Reads at hd2
  rw [hq] at hd2
  obtain ⟨_, _, tt, _, -, -, -, -, -, al, -, -, -⟩ := reads_laid_later ha hd2
  obtain ⟨o, o', ho, ho', -, -, et, -⟩ := al
  obtain rfl : ({ a with t := some tt } : HeadOwn) = o :=
    VerifiableInference.Desc.First.Here.head.inj ho
  exact ⟨o', tt, ho', et⟩

/-- A yes at 343 leaves the head's tables. -/
theorem t_kept_343 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S ProofFile.Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hB : c.blocksInOrder[343]? = some b0)
    (hd : b0.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ o, t.here = .head o ∧ o.t = a.t := by
  obtain ⟨Lk, b, Xl, h1, h2, -, hla, -⟩ := IM.k8_of_head hS hR O
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  obtain ⟨tl, rfl⟩ := VerifiableInference.Desc.First.K8.decide_atS _ s t rs gs
    ((IM.k8_yes hla s t rs gs).1 hd).1
  unfold S.putTl
  rw [ha]
  dsimp only
  split
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨a, ha, rfl⟩

/-- A yes at 344 leaves the head's tables. -/
theorem t_kept_344 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S ProofFile.Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hB : c.blocksInOrder[344]? = some b0)
    (hd : b0.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ o, t.here = .head o ∧ o.t = a.t := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, h1, h2, -, -, hla⟩ :=
    IM.k1_digits_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have hd2 : (VerifiableInference.Desc.K1.laterAt Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z)
      24 (IM.k1Ix 24 true + 1) 2 digits : Block S Unit).decide s rs gs = .ok t :=
    ((IM.yes_alone hla (by decide) s t rs gs).1 hd).1
  obtain ⟨o, o', ho, ho', -, -, et, -⟩ := sending_alike ha hd2
  obtain rfl : a = o := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ho)
  exact ⟨o', ho', et⟩

end

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- From border 339 on every element in the reply's seat is a token of V. -/
theorem tokSmall_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat}
    {a : ProofFile.InstPub × S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (hk : 339 ≤ k) :
    TokSmall Zp.p.X.hS.V a.2 := by
  induction hr with
  | zero z => exact absurd hk (by omega)
  | @succ k z s s' b hr' hb hy ih =>
    obtain ⟨R, c, -, hs⟩ := hy
    show TokSmall _ s'
    by_cases e : k = 338
    · subst e
      obtain ⟨Bs, hB, hW, -, -, -⟩ := nums_at h
      obtain ⟨Bs', hB', hl⟩ := reply_laid_at h
      obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
      obtain ⟨g, hg, ht⟩ := hl b hb 0 s R c s' _ hs
      rw [hW] at ht
      intro y hy'
      rw [hg] at hy'
      obtain rfl := Option.some.inj hy'
      exact ht
    · exact tokSmall_rides _ (ih (by omega)) (reply_kept_but h k e b hb 0 s R c s' _ hs)

/-- **At every state reached at border 345: the four facts on the head's record.** -/
theorem heard_at_345 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {a : ProofFile.InstPub × S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 345 a) :
    ∃ hd y tt, a.2.here = .head hd ∧ hd.x = some y ∧ hd.t = some tt ∧
      ∀ t, y.win.getD t 0 < Zp.p.X.hS.V := by
  obtain ⟨z, s345⟩ := a
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨s344, B4, r4, g4, h344, hB4, d4⟩ := peel_raw hr
  obtain ⟨s343, B3, r3, g3, h343, hB3, d3⟩ := peel_raw h344
  obtain ⟨s342, B2, r2, g2, h342, hB2, d2⟩ := peel_raw h343
  obtain ⟨s341, B1, r1, g1, h341, hB1, d1⟩ := peel_raw h342
  have c1 := P4.yes_341 h.scope h.reads O hB1 d1
  rw [O.W] at c1
  obtain ⟨a2, y, ho2, hx2, hw⟩ := win_behind_block Zp.p.X c1
    (reqOk_reach_head h h341 (hq_reach h h341 (by omega))) (tokSmall_reach h h341 (by omega))
  obtain ⟨p2, p3, e2, e3, ex3, -⟩ := P4.kept_342 h.scope h.reads O hB2 d2 ho2
  obtain rfl : a2 = p2 := VerifiableInference.Desc.First.Here.head.inj (ho2.symm.trans e2)
  obtain ⟨q3, tt, f3, ht3⟩ := tables_342 h.scope h.reads O hB2 d2 ho2
  obtain rfl : p3 = q3 := VerifiableInference.Desc.First.Here.head.inj (e3.symm.trans f3)
  obtain ⟨p3', p4, e3', e4, ex4, -⟩ := P4.kept_343 h.scope h.reads O hB3 d3 e3
  obtain rfl : p3 = p3' := VerifiableInference.Desc.First.Here.head.inj (e3.symm.trans e3')
  obtain ⟨q4, f4, ht4⟩ := t_kept_343 h.scope h.reads O hB3 d3 e3
  obtain rfl : p4 = q4 := VerifiableInference.Desc.First.Here.head.inj (e4.symm.trans f4)
  obtain ⟨p4', p5, e4', e5, ex5, -⟩ := P4.kept_344 h.scope h.reads O hB4 d4 e4
  obtain rfl : p4 = p4' := VerifiableInference.Desc.First.Here.head.inj (e4.symm.trans e4')
  obtain ⟨q5, f5, ht5⟩ := t_kept_344 h.scope h.reads O hB4 d4 e4
  obtain rfl : p5 = q5 := VerifiableInference.Desc.First.Here.head.inj (e5.symm.trans f5)
  exact ⟨p5, y, tt, e5, by rw [ex5, ex4, ex3, hx2], by rw [ht5, ht4, ht3], hw⟩

/-- **So the test on values of the lookup on the head's own digits accepts there.** -/
theorem headVals_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {a : ProofFile.InstPub × S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 345 a) : headVals Zp.p.X a.2 = true := by
  obtain ⟨hd, y, tt, e1, e2, e3, hw⟩ := heard_at_345 h hr
  obtain ⟨cov, hc⟩ := covered_reach h hr (hq_reach h hr (by omega)) (by omega)
  exact headVals_of e1 e2 e3 hc (layoutOk_at h) fun t _ _ => hw t

/-- The table's own test at 345. -/
theorem tab_345_vals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (s : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    Tab.vals Zp G 345 s rs gs = headVals Zp.p.X s := by
  obtain ⟨st, hs, -, -, -⟩ := site_found h 24 (by omega) true
  have hc : Tab.cells Zp G 345 = Tab.lookHead Zp := cells_head Zp G 8 (by omega) rfl
  unfold Tab.lookHead at hc
  rw [hs] at hc
  rw [cell_v hc]

/-- **At every state reached at border 345 the table's own test accepts.** -/
theorem vals_345_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    {a : ProofFile.InstPub × S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 345 a) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) : Tab.vals Zp G 345 a.2 rs gs = true := by
  rw [tab_345_vals h]
  exact headVals_reach h hr

/-- **THE RULE's PREMISE ON VALUES AT 345, AT THE TABLE's OWN TEST.** -/
theorem valuesJ_345 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → S → Option String)
    (carryX : Nat → ProofFile.InstPub × S → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → S → Prop)
    (Kp : Place → S → S → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (J : Nat → S → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) :
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall 345 :=
  valuesJ_lighter H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said J fall h
    (V' := fun _ _ _ _ => true) (by omega) (fun _ rs gs hr _ => vals_345_reach h G hr rs gs)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.peel_raw
#print axioms Johnson.AtFull.Shape.win_behind_block
#print axioms Johnson.AtFull.Shape.tables_342
#print axioms Johnson.AtFull.Shape.t_kept_343
#print axioms Johnson.AtFull.Shape.t_kept_344
#print axioms Johnson.AtFull.Shape.tokSmall_reach
#print axioms Johnson.AtFull.Shape.heard_at_345
#print axioms Johnson.AtFull.Shape.headVals_reach
#print axioms Johnson.AtFull.Shape.tab_345_vals
#print axioms Johnson.AtFull.Shape.vals_345_reach
#print axioms Johnson.AtFull.Shape.valuesJ_345
