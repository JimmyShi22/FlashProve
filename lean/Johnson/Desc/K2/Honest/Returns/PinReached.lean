-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/PinReached.lean: AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH
INTO A LATER GROUP, IN THE GOALS' SCOPE AND UNDER THREE NAMED TESTS ON THE PUBLIC PART, EIGHT
CLAUSES OF THE LAW "THE KIND's OWN DECISION SAYS YES AT A SEGMENT's FIRST PLACE" (`LinkPlain`,
Returns/LinkSent.lean) HOLD AT THE FRONT THAT THE TEXT RETURNS THERE, IF IT RETURNS ONE: the test on
the target (`FrontCore.check`) · six of `OldFits` (mainVars · d0 · d1 · rows · once · keptCode) ·
`TablesFit.bitsKept`. SO TWO MORE FOLLOW: `FrontCore.reads` AND, WHERE EACH COPY HAS A MAIN ROW,
`TablesFit.stored`. Statements with their proofs: calls.

HOW. The library has: at such a state the text's front has the public side of the written front of
its place (`hT1_link_plain`, Johnson/P1K2R/HT1Plain.lean: the test `frontB2` accepts). At the
written front four of the clauses hold by Lean's kernel's yes at the table's five different entries
(`decide +kernel`: Returns/WrittenFronts.lean); they pass to every front with the same public side
(Returns/TargetPin.lean). Of the other four, three are read off `frontB2` itself (its part
`carriedB`); `once` wants, beside its part `numsB`, that the written numbers are without a double
(`olds_once`, over the library's `olds_nodup`, itself closed by `decide +kernel`).

  `ShapeFits x` THE EIGHT at a front x, each field in the letters of the structure that asks it
  `placeQ w` a place's numbers of which the word "stands" alone is read
  `row_at` the table has an entry at each number below 25
  `olds_once` the written numbers of the kept old messages are without a double, at each of the 25
                    groups
  `carried_at` the three clauses on the carried claim's sizes, led from the written frame's two
                    codes to the front's own lists of codes
  `shape_of_test` `ShapeFits x` wherever `frontB2` accepts x at a written front of the table, its
                    frame, and numbers without a double: no state, no plan
  `ShapeFits.reads`, `ShapeFits.tables` the two that follow, where the front's statement has
                    `SampleGoodS`
  `link_front_at` with "the frame's next call is a first one": the text's front returns `frontAt s L
                    Q` at THE FRAME's OWN segment L and group Q: so the clauses here and the
                    thirteen of Returns/LinkReached.lean meet at one front
  `link_pinned_reached` `frontB2` accepts the text's front, at the written front of the place and
                    its frame; and the front's statement has `SampleGoodS`
  `link_shape_reached` `ShapeFits` at the text's front
  `link_reads_paid`, `link_tables_paid` the two that follow, there
  `link_tables_at` `TablesFit.stored` at `frontAt s L Q`: "each copy has a main row" is paid by
                    `link_fields_reached` (Returns/LinkReached.lean)

AT WHICH TERMS THE LIBRARY's STATEMENT IS TAKEN: its "reached" is the walk over the wrapped list
itself · its way in lets the state in as it is · its place's numbers are `placeQ .link` · its second
component is `Unit`.

By, all the library's: `hT1_link_plain` (which leans on `msgShapes_field`,
Johnson/IMR/SeatsField.lean) · `front_tests_full` (Johnson/G/SwitchFrontTests.lean) · `frontAt_link`
(Johnson/Top/H0/Walk/FrameCarryReads.lean) · `pin_facts`, `nums_of_test`
(Johnson/Top/H0/K2Hands/FrameOne.lean) · `carried_of_test` (K2Hands/FrontB2.lean) · `frame_fields`
(Johnson/Top/H/SwitchMapsCheck.lean) · `olds_nodup` (Johnson/Top/H0/K2Hears/PlaceNums.lean) ·
`full_is` (Johnson/Top/H0/K2Caller/LitRows.lean). Near relatives, not called: `front_twelve`
(K2Hands/FrontB2.lean): twelve public clauses from the same test, in the frame's letters; no test on
the target among them · `t14_nodup` (Johnson/P1K2R/TiesOneFour.lean): `olds_once` at m + 1 ·
`link_front_reached` (Returns/LinkReached.lean): `link_front_at` under "there are L and Q".

Limits. THE THREE TESTS (hy: what the planner configured is the written value · hcut: the chain's
sub-protocols have the written cut · hB: the sendings are those of the written list of places) READ
THE PUBLIC PART ALONE. Johnson/P1K2R/HT1Plain.lean's HEAD SAYS THAT THE SEALED VERIFIER ASKS NEITHER
hy NOR hcut, THAT WHETHER IT ASKS hB WAS NOT READ, AND THAT THE THREE ARE NOT SHOWN MET TOGETHER
WITH THE PREMISES IN FRONT. NOR IS THAT SHOWN HERE: NO MEMBER. The opening stands at the public
files' own layout file: narrower than in Returns/LinkReached.lean. THAT THE TEXT RETURNS A FRONT
asks "the frame's next call is a first one", itself a clause of the law: Returns/FirstReached.lean
pays it. Not reached: eight clauses of `ReadFits` on the layout, `OldFits.named`, the two clauses on
the carried claim's and the kept forms' tensors. The head's and the finish's switch:
Returns/PinArms.lean. The full size alone. This file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.StoredTables
import Johnson.Desc.K2.Honest.Returns.TargetPin
import Johnson.Desc.K2.Honest.Returns.WrittenFronts
import Johnson.P1K2R.HT1Plain
import Johnson.G.SwitchFrontTests
import Johnson.Top.H0.Walk.FrameCarryReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 SampleGoodS frameAt n0At oldsAt olds_nodup)
open VerifiableInference.Desc.First.K2Hands (Pinned carriedB frontB2 pin_facts nums_of_test
  carried_of_test)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit full_is)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach frontAt_link)
open Johnson.G (fxAt front_tests_full)
open Johnson.Top.H (frame_fields)
open P1K2 (Prep Nums numsAt prepOf hT1_link_plain)
open _root_.Tw.K2 (Front firstFront readsMainOf)
open ProofFile (Cl)

/-- **THE EIGHT**, at a front: `check` is `FrontCore`'s; `bitsKept` is `TablesFit`'s; the six
between are `OldFits`'. -/
structure ShapeFits (x : Front) : Prop where
  check : switchTargetCheck x.st x.f.rows x.T = true
  mainVars : ∀ v ∈ x.f.rows.c.tensors,
    v.vars = (x.st.codes.base.getD x.f.rows.code default).logEll
  d0 : (x.f.rows.d.getD 0 #[]).size ≤ (x.st.codes.mask.getD x.f.rows.maskCode default).ell
  d1 : (x.f.rows.d.getD 1 #[]).size ≤ (x.st.codes.mask.getD x.f.rows.maskCode default).ell
  rows : x.f.rows.keptRows =
    ((switchKept x.f.rows).toList.map fun o => (x.st.oracles.getD o default).shape.mainRows).sum
  once : (switchKept x.f.rows).toList.Nodup
  keptCode : ∀ o ∈ (switchKept x.f.rows).toList,
    (x.st.oracles.getD o default).shape.code = x.f.rows.code
  bitsKept : ∀ t ∈ (sizesAt x.st x.f.rows x.T).kept,
    ceilLog2 t.mainRows + (x.st.codes.base.getD x.f.rows.code default).logEll ≤ 63

/-- A place's numbers of which the word "stands" alone is read. -/
def placeQ (w : First.K2.At) : P2 :=
  { name := "", place := default, stands := w, grp := 0, firstTree := 0, samples := 0,
    work₁ := 0, roots := 0, seeds := 0, nonZero := 0, work₂ := 0, answers := 0, positions := 0,
    logN := 0, sent := [], read := [] }

theorem row_at {m : Nat} (h : m < 25) : ∃ r, tableFullLit[m]? = some r := by
  have hlen : tableFullLit.length = 25 := by
    rw [full_is]
    rfl
  exact ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact h)⟩

theorem olds_once {l : Nat} (h1 : 1 ≤ l) (h25 : l ≤ 25) : (oldsAt l).Nodup :=
  of_decide_eq_true (List.all_eq_true.1 olds_nodup l (by simp [List.mem_range'_1]; omega))

/-- The carried claim's sizes: from the written frame's two codes to the front's own lists. -/
theorem carried_at {x₀ x : Front} {W : SwitchFrame} (h0 : frameAt x₀ = some W) (P : Pinned x₀ x)
    (h : carriedB W x = true) :
    (∀ v ∈ x.f.rows.c.tensors, v.vars = (x.st.codes.base.getD x.f.rows.code default).logEll) ∧
      (x.f.rows.d.getD 0 #[]).size ≤ (x.st.codes.mask.getD x.f.rows.maskCode default).ell ∧
      (x.f.rows.d.getD 1 #[]).size ≤ (x.st.codes.mask.getD x.f.rows.maskCode default).ell := by
  obtain ⟨f1, f2, -⟩ := frame_fields _ _ _ _ _ W h0
  have e1 : x.st.codes.base.getD x.f.rows.code default = W.code := by
    rw [P.codes, P.code, Array.getD_eq_getD_getElem?]
    exact congrArg (·.getD default) f1
  have e2 : x.st.codes.mask.getD x.f.rows.maskCode default = W.zk := by
    rw [P.codes, P.maskCode, Array.getD_eq_getD_getElem?]
    exact congrArg (·.getD default) f2
  rw [e1, e2]
  exact carried_of_test h

/-- **The eight, wherever the library's test accepts a front at a written front of the table.** -/
theorem shape_of_test {r : SwRow} (hr : r ∈ tableFullLit) {W : SwitchFrame}
    (hW : frameAt (fxAt r) = some W) {grp n0 : Nat} {olds : List Nat} (hnd : olds.Nodup)
    {x : Front} (hb : frontB2 (fxAt r) W grp 0 n0 olds x = true) : ShapeFits x := by
  simp only [frontB2, Bool.and_eq_true] at hb
  obtain ⟨⟨hp, hnum⟩, hcar⟩ := hb
  have Pn := pin_facts hp
  obtain ⟨w1, w2, w3, w4⟩ := written_at hr
  obtain ⟨c1, c2, c3⟩ := carried_at hW Pn hcar
  refine ⟨check_pin Pn w1, c1, c2, c3, rows_pin Pn w3, ?_, keptCode_pin Pn w2, bitsKept_pin Pn w4⟩
  rw [(nums_of_test hnum).2.2.2]
  exact hnd

theorem ShapeFits.reads {x : Front} (H : ShapeFits x) (hG : SampleGoodS x.st) :
    ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList,
      readsMainOf o r = true :=
  reads_stored hG.good H.check

theorem ShapeFits.tables {x : Front} (H : ShapeFits x) (hG : SampleGoodS x.st)
    (keptPos : ∀ k ∈ x.T.kept.toList, 0 < k.shape.mainRows) :
    ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList,
      (∀ t ∈ r.terms.toList, t.v.pairs.length = x.st.tableBits o .main ∧ Own.InOrder t.v) ∧
        ∀ u ∈ r.units.toList, u.index < 2 ^ x.st.tableBits o .main :=
  tables_stored hG H.check keptPos H.keptCode H.bitsKept

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- The text's front at the frame's own segment and group. -/
theorem link_front_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (first : s.check.frame.next = .first) {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    firstFront s.st s.check.frame = .ok (frontAt s L Q) := by
  obtain ⟨L', Q', c₀, z₀, -, -, h0, h2, h3, hc, hz, hle, -⟩ :=
    link_fields_reached hS hR O hF hpl h23 hP hn hr default ""
  obtain rfl : L' = L := Option.some.inj (h2.symm.trans hL)
  obtain rfl : Q' = Q := Option.some.inj (h3.symm.trans hQ)
  exact firstFront_returns s.st s.check.frame _ _ c₀ z₀ first h0 h2 h3 hc hz hle

/-- **The text's front has the public side of its place's written front.** -/
theorem link_pinned_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {x : Front} (hx : firstFront s.st s.check.frame = .ok x)
    {r : SwRow} (hrw : tableFullLit[m]? = some r) :
    ∃ W, frameAt (fxAt r) = some W ∧
      frontB2 (fxAt r) W (m + 1) 0 (n0At (m + 1)) (oldsAt (m + 1)) x = true ∧
      SampleGoodS x.st := by
  obtain ⟨W, hW, -⟩ := front_tests_full (List.mem_of_getElem? hrw)
  have hfx : First.K2.frontAt (placeQ .link) s = some x := by
    rw [frontAt_link (p := placeQ .link) rfl s, hx]
    rfl
  have H := hT1_link_plain (Str := Unit)
    (Rch := fun k y => Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k y.1) hS hR O hF hpl hy hcut hB
    (fun _ _ h => h) h23 (enter := fun t => .ok t) (fun _ _ h => (Except.ok.inj h).symm)
    (q := placeQ .link) rfl hrw hW z (s, ()) hr s rfl x hfx
  exact ⟨W, hW, H.1, H.2.2.1⟩

/-- **THE EIGHT at the text's front.** -/
theorem link_shape_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {x : Front} (hx : firstFront s.st s.check.frame = .ok x) : ShapeFits x := by
  obtain ⟨r, hrw⟩ := row_at (m := m) (by omega)
  obtain ⟨W, hW, hb, -⟩ := link_pinned_reached hS hR O hF hpl hy hcut hB h23 hr hx hrw
  exact shape_of_test (List.mem_of_getElem? hrw) hW (olds_once (by omega) (by omega)) hb

/-- **`FrontCore.reads` at the text's front.** -/
theorem link_reads_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {x : Front} (hx : firstFront s.st s.check.frame = .ok x) :
    ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList,
      readsMainOf o r = true := by
  obtain ⟨r, hrw⟩ := row_at (m := m) (by omega)
  obtain ⟨-, -, -, hG⟩ := link_pinned_reached hS hR O hF hpl hy hcut hB h23 hr hx hrw
  exact (link_shape_reached hS hR O hF hpl hy hcut hB h23 hr hx).reads hG

/-- **`TablesFit.stored` at the text's front, where each copy has a main row.** -/
theorem link_tables_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {x : Front} (hx : firstFront s.st s.check.frame = .ok x)
    (keptPos : ∀ k ∈ x.T.kept.toList, 0 < k.shape.mainRows) :
    ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList,
      (∀ t ∈ r.terms.toList, t.v.pairs.length = x.st.tableBits o .main ∧ Own.InOrder t.v) ∧
        ∀ u ∈ r.units.toList, u.index < 2 ^ x.st.tableBits o .main := by
  obtain ⟨r, hrw⟩ := row_at (m := m) (by omega)
  obtain ⟨-, -, -, hG⟩ := link_pinned_reached hS hR O hF hpl hy hcut hB h23 hr hx hrw
  exact (link_shape_reached hS hR O hF hpl hy hcut hB h23 hr hx).tables hG keptPos

/-- **`TablesFit.stored` at the frame's own segment and group.** -/
theorem link_tables_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (first : s.check.frame.next = .first) {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    ∀ o ∈ (switchKept (frontAt s L Q).f.rows).toList,
      ∀ r ∈ ((frontAt s L Q).st.oracles.getD o default).sampleRows.toList,
        (∀ t ∈ r.terms.toList,
          t.v.pairs.length = (frontAt s L Q).st.tableBits o .main ∧ Own.InOrder t.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (frontAt s L Q).st.tableBits o .main := by
  obtain ⟨L', Q', -, -, -, -, -, h2, h3, -, -, -, -, -, -, -, hk⟩ :=
    link_fields_reached hS hR O hF hpl h23 hP hn hr default ""
  obtain rfl : L' = L := Option.some.inj (h2.symm.trans hL)
  obtain rfl : Q' = Q := Option.some.inj (h3.symm.trans hQ)
  exact link_tables_paid hS hR O hF hpl hy hcut hB h23 hr
    (link_front_at hS hR O hF hpl h23 hP hn hr first h2 h3) hk

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.row_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.olds_once
#print axioms VerifiableInference.Desc.K2.Honest.Returns.carried_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.shape_of_test
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ShapeFits.reads
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ShapeFits.tables
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_front_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_pinned_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_shape_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_reads_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_tables_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_tables_at
