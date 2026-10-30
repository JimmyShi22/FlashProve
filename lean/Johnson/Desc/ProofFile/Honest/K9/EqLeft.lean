-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqLeft.lean: THE VERIFIER ACCEPTS AT THE SUB-PROTOCOL "THE ONE EQUATION", in all 25
segments of the first chain, at the first chain's thread under the library's hypothesis `AtMgA`, FROM WHAT IS LEFT WHEN
THE YESES OF THE TWO SUB-PROTOCOLS IN FRONT HAVE PAID THEIR SHARE (Honest/K9/EqTrace.lean).

The sub-protocol's function `door` (Johnson/Desc/First/Batch/Text.lean) has some twenty-five tests. PAID HERE, from
`BehindBoth`: a part of the state is read ("K9.in-a-segment") · the list is a link's (first clause of "K9.door-once") ·
"K9.draw-has-run" · "K9.claims-all-added" (the count by the tests behind the adding; the plan's number by the library's
`planClaims_at_batch`, `planClaims_at_head`) · "K9.weights-all-taken" · "K9.slots-sizes" (two clauses by the draw's tests,
three by the public item "ledger", which is open at this border) · the form of "K9.rows-counted". BROUGHT TO LESS:
"K9.slots-filled" and "K9.slot-with-coefficient-filled" to the one field `filled` (the draw has tested that all slots are
in use) · "K9.no-weight-outside" and "K9.arrays-there" to one equation of two sizes in `named`: so the first is no
test on values at such a state.

  `EqLeft rows n s L F tl`   WHAT IS LEFT, one named field a test or a small group of tests; rows: the rows that the
      batching's entry counts; n: the claims that the public parameters count:
      fresh · named · walk: on the segment's book-keeping L      filled · paid: on the ledger F
      laid: on the smallness test's record tl, and one equation between three numbers
      termsB · termsV: on the ledger's arrays                    made · seats · core · pad: on the statement
  `eqB_of`, `outside_of`   the tests on numbers and marks, from their clauses; no array stands beyond the list
  `tested_plan`, `plan_at_eq`   the ledger's number of planned claims in front of the batching is the public parameters'
  `open_eq`                on the written lists, by Lean's kernel: "ledger m" is open in front of each one equation
  **`door_of_left`**        `BehindBoth`, the plan's number, the three sizes and `EqLeft` ⊢ a part is read and `door`
                          returns at it
  **`accepted_eq_of_left`**   `AcceptedS` at 14 l + `IM.nAt l` + 4, for l < 25, from `EqLeft` at the states at which the
      thread's invariant and `Said` hold and the table of falls is silent

Limits. `EqLeft` is proved here at no state. The full size and the hash function `secondHashFunction` alone: the hypothesis's.
`AcceptedS` is one of the hypotheses on one sub-protocol (Honest/Thread/PaysS.lean); this file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqTrace
import Johnson.Desc.ProofFile.Honest.K9.ShutAccepted
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Law.Rule.OkBridges
import Johnson.Desc.First.Batch.Shape.DoorChain
import Johnson.Desc.First.Link.Law.PlanClaimsAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (coefBody)
open VerifiableInference.Desc.K9 (equation asRow St door)
open VerifiableInference.Desc.K9.Shape (eqB doorB outsideV termsB termsV slotsV madeB seatsB maskB padB doorS coreS
  door_returns made_pays fits_pays part_d all_empty)
open VerifiableInference.Desc.LinkJoin (planClaimsAt planClaims_at_batch planClaims_at_head ledgerOk_iff)
open VerifiableInference.Desc.First (pubSets leavesName)
open H2K5.Door (moreOver9)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **What is left.** rows: the rows that the batching's entry counts. n: the claims that the public parameters count. -/
structure EqLeft (rows n : ℕ) (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : Prop where
  /-- the door has not been walked, and the link is not closed ("K9.door-once") -/
  fresh : L.list.walked = false ∧ L.done = false
  /-- "K9.arrays-named"; the ledger has just the listed arrays (for "K9.arrays-there", "K9.no-weight-outside") -/
  named : L.arrayOf.size = L.list.nt.size ∧ F.trees.size = L.list.nt.size
  /-- "K9.link-is-the-walks", "K9.moments-passed" -/
  walk : L.link = L.check.link ∧ L.check.inLink = true ∧ L.check.moments = L.check.momentsDue
  /-- every slot is filled -/
  filled : ∀ j, j < F.ns → F.gotF.getD j false = true
  /-- "K9.owed-claims-added" -/
  paid : F.owed.all (·.added) = true
  /-- "K9.equations-laid", and the numbers of "K9.rows-counted" -/
  laid : ∃ k, Desc.K9.laidOf tl = some k ∧ rows = n + k
  /-- "K9.array-laid", "K9.weights-sizes", "K9.row-form" -/
  termsB : termsB L { F with doorShutF := true } = true
  /-- "K9.row-form-values" -/
  termsV : termsV L { F with doorShutF := true } = true
  /-- the row is made of the terms -/
  made : madeB L { F with doorShutF := true } s.st = true
  /-- the statement has the link's group; each term's message, and the mask's, is a member with a table -/
  seats : ∃ G, s.st.groups[L.check.group]? = some G ∧ seatsB L { F with doorShutF := true } s.st G = true ∧
    maskB L.check.frame s.st G F.ns = true
  /-- the mask entries are free from 0 on, and the group takes a row: on the shape of the statement -/
  core : ∃ z, doorS L.check.frame F.ns L.check.group (coreS s) = some z
  /-- the row that is made has no coefficient on a pad -/
  pad : ∀ q F' y, equation L F = .ok (q, F') →
    asRow L.check.rows L.check.frame q
      ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } : St Unit) = .ok y →
    padB y.2.st L.check.group y.1 = true

/-- The tests on numbers and marks, from their clauses. -/
theorem eqB_of (L : LinkCtx) (F : Fork) (c1 : L.list.link = true) (c2 : L.list.walked = false) (c3 : L.done = false)
    (c4 : L.handed = true) (c5 : F.planClaimsF ≠ 0) (c6 : F.nClaim = F.planClaimsF)
    (c7 : F.kapMapF.size = F.planClaimsF) (c8 : F.kapMapF.all id = true) (c9 : L.arrayOf.size = L.list.nt.size)
    (c10 : L.list.nt.size ≤ F.trees.size) (c11 : L.list.used ≤ F.ns) (c12 : F.gotF.size = F.ns)
    (c13 : F.LS.size = F.ns) (c14 : F.vp.size = F.ns) (c15 : F.mf.size = F.ns)
    (c16 : F.owed.all (·.added) = true) (c17 : F.gotF.all id 0 L.list.used = true) : eqB L F = true := by
  unfold eqB
  rw [c1, c2, c3, c4, c8, c16, c17, bne_iff_ne.2 c5, beq_iff_eq.2 c6, beq_iff_eq.2 c7, beq_iff_eq.2 c9,
    decide_eq_true c10, decide_eq_true c11, beq_iff_eq.2 c12, beq_iff_eq.2 c13, beq_iff_eq.2 c14, beq_iff_eq.2 c15]
  rfl

/-- No array stands beyond the list: so none there bears a weight. -/
theorem outside_of (L : LinkCtx) (F : Fork) (h : F.trees.size = L.list.nt.size) : outsideV L F = true := by
  unfold outsideV
  exact all_empty _ _ (Array.eq_empty_of_size_eq_zero (by rw [Array.size_extract]; omega))

/-- The number of claims that the tests behind the adding count is the plan's. -/
theorem tested_plan {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (ht : Desc.K9.testsWhere X l 0 = some w) :
    (l = 24 → w.2.1 = X.H.nLin) ∧ (l < 24 → planClaimsAt X l = some w.2.1) := by
  unfold Desc.K9.testsWhere at ht
  simp only [h4, hN, if_true] at ht
  refine ⟨fun e => ?_, fun hl => ?_⟩
  · subst e
    have e : w = (.head, X.H.nLin, ⟨1, 24, 0, X.H.nMsg, X.H.nU⟩) := (Option.some.inj ht).symm
    rw [e]
  · have e1 : (l == 2 * 12) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    rw [e1] at ht
    unfold planClaimsAt
    by_cases he : l % 2 = 0
    · have e2 : (l % 2 == 0) = true := by
        rw [beq_iff_eq]
        exact he
      rw [e2] at ht
      obtain ⟨hp, e0, e⟩ := Option.map_eq_some_iff.1 ht
      rw [if_pos he, e0, ← e]
      rfl
    · have e2 : (l % 2 == 0) = false := by
        rw [beq_eq_false_iff_ne]
        exact he
      rw [e2] at ht
      obtain ⟨a, e0, e⟩ := Option.map_eq_some_iff.1 ht
      rw [if_neg he, e0, ← e]
      rfl

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- On the written lists: "ledger m" is open in front of each one equation. -/
theorem open_eq : ∀ m, m < 25 →
    VerifiableInference.Desc.First.Pub.ledger m ∈ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[14 * m + IM.nAt m + 4]?.getD [] := by
  decide +kernel

/-- **A part is read, and `door` returns at it.** -/
theorem door_of_left {p : Desc.K9.Where} {n : ℕ} {s : S} {a : Desc.K9.Part} {χ : E} {G : Fork} {tl : HTailF2}
    {g : Forest.Heard} (B : BehindBoth p n s a χ G tl g) (hplan : a.F.planClaimsF = n)
    (hsized : OnBytes.PscRun.Sized (coefBody tl g G))
    (E₀ : EqLeft p.rows n s (drawnPart p a χ).L (coefBody tl g G) tl) :
    ∃ P o, Desc.K9.atS.get? s = some P ∧ door P.owed P.laid P.L P.F P.d = .ok o := by
  obtain ⟨u, hP⟩ := part_of_all B.link B.fork B.tail B.used
  have hb : ({ coefBody tl g G with trees := G.trees } : Fork) = G := butTrees_coefBody tl g G
  have f_ns : (coefBody tl g G).ns = G.ns := by
    have := congrArg Fork.ns hb
    exact this
  have f_plan : (coefBody tl g G).planClaimsF = G.planClaimsF := by
    have := congrArg Fork.planClaimsF hb
    exact this
  have f_count : (coefBody tl g G).nClaim = G.nClaim := by
    have := congrArg Fork.nClaim hb
    exact this
  have f_marks : (coefBody tl g G).kapMapF = G.kapMapF := by
    have := congrArg Fork.kapMapF hb
    exact this
  have f_LS : (coefBody tl g G).LS = G.LS := by
    have := congrArg Fork.LS hb
    exact this
  obtain ⟨sz_vp, sz_mf, sz_got⟩ := hsized
  have hr := B.ready
  unfold drawReady at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -, hused⟩, ⟨hlink, -⟩, -⟩, -⟩, hplan0⟩, -⟩, -⟩, -⟩ := hr
  have hused' : a.used = a.F.ns := beq_iff_eq.1 hused
  have hplan0' : a.F.planClaimsF ≠ 0 := bne_iff_ne.1 hplan0
  have hn : G.nClaim = G.planClaimsF := by rw [B.count, B.plan, hplan]
  have usedIs : (drawnPart p a χ).L.list.used = (coefBody tl g G).ns := by
    rw [f_ns, B.ns]
    exact hused'
  obtain ⟨k, hk, hrows⟩ := E₀.laid
  obtain ⟨Gr, hGr, hseats, hmask⟩ := E₀.seats
  obtain ⟨z, hz⟩ := E₀.core
  have b1 : eqB (drawnPart p a χ).L (coefBody tl g G) = true := by
    refine eqB_of _ _ hlink E₀.fresh.1 E₀.fresh.2 rfl (by rw [f_plan, B.plan]; exact hplan0')
      (by rw [f_count, f_plan]; exact hn) (by rw [f_marks, f_plan, B.marks, B.plan])
      (by rw [f_marks]; exact marks_full G B.marked hn (by rw [B.marks, B.plan])) E₀.named.1
      (Nat.le_of_eq E₀.named.2.symm) (Nat.le_of_eq usedIs) sz_got (by rw [f_LS, f_ns, B.coefs, B.ns]) sz_vp sz_mf
      E₀.paid ?_
    refine Array.all_iff_forall.2 fun i hi hk => ?_
    have := E₀.filled i (by rw [← usedIs]; exact hk.2)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at this
    exact this
  have v3 : slotsV { coefBody tl g G with doorShutF := true } = true := by
    unfold slotsV
    refine List.all_eq_true.2 fun j hj => ?_
    rw [Bool.or_eq_true]
    refine Or.inr (E₀.filled j ?_)
    have hj' : j < (coefBody tl g G).LS.size := List.mem_range.1 hj
    rw [f_LS, B.coefs, ← B.ns, ← f_ns] at hj'
    exact hj'
  have b3 : doorB (Desc.K9.owedOf s) k (drawnPart p a χ).L { coefBody tl g G with doorShutF := true } = true := by
    have e1 : Desc.K9.owedOf s = some ((coefBody tl g G).nClaim + k) := by
      rw [B.owed, f_count, B.count, ← hrows]
      have hn0 : n ≠ 0 := by
        rw [← hplan]
        exact hplan0'
      obtain ⟨m, hm⟩ : ∃ m, p.rows = m + 1 := ⟨p.rows - 1, by omega⟩
      rw [hm]
      rfl
    unfold doorB
    rw [e1, E₀.walk.2.1, beq_iff_eq.2 E₀.walk.1, beq_iff_eq.2 E₀.walk.2.2]
    simp
  obtain ⟨o, ho⟩ := door_returns (Desc.K9.owedOf s) k (drawnPart p a χ).L (coefBody tl g G)
    ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } : St Unit) z b1 E₀.termsB b3
    (by rw [← part_d hP] at hz; exact hz) (outside_of _ _ E₀.named.2) E₀.termsV v3
    (fun q F' hq => made_pays _ _ s.st E₀.made q F' hq)
    (fun q F' y hq hy => fits_pays _ _ _ Gr hGr hseats hmask E₀.pad q F' y hq hy)
  refine ⟨_, o, hP, ?_⟩
  show door (Desc.K9.owedOf s) (Desc.K9.laidOf tl) _ _ _ = _
  rw [hk]
  exact ho

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

include h in
/-- The ledger's number of planned claims in front of the batching is the public parameters'. -/
theorem plan_at_eq {l : ℕ} (hl : l < 25) {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (ht : Desc.K9.testsWhere Zp.p.X l 0 = some w) {Q₀ : Type} {start : Q₀ → TS} {pub : Q₀} {s₂ : TS}
    {a : Desc.K9.Part} (hr : Reach 0 cF.blocksInOrder start (14 * l + IM.nAt l + 2) (pub, s₂))
    (ha : Desc.K9.atS.get? s₂ = some a) : a.F.planClaimsF = w.2.1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  obtain ⟨t24, tlt⟩ := tested_plan (X := Zp.p.X) h4 hN ht
  have hF := (Desc.K9.Shape.part_reads ha).2
  by_cases e24 : l = 24
  · subst e24
    obtain ⟨G, hG, e⟩ := planClaims_at_head h.scope h.reads O (z := pub) (s' := s₂) hr
    obtain rfl : G = a.F := Option.some.inj (hG.symm.trans hF)
    rw [e, O.W, t24 rfl]
  · have hl' : l < 24 := by omega
    have en : 14 * l + IM.nAt l + 2 = 14 * l + 9 := by
      unfold IM.nAt
      rw [if_neg e24]
    rw [en] at hr
    obtain ⟨G, n, hG, hn, e⟩ := planClaims_at_batch h.scope h.reads O hl' hr
    obtain rfl : G = a.F := Option.some.inj (hG.symm.trans hF)
    rw [O.W, tlt hl'] at hn
    rw [e, ← Option.some.inj hn]

/-- **The verifier accepts at "the one equation", from what is left.** -/
theorem accepted_eq_of_left (l : ℕ) (hl : l < 25)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : ℕ → TS → List Fmt.Drawn → Option String)
    (left : ∀ κ s m En, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said
      (14 * l + IM.nAt l + 4) κ s m En → fall (14 * l + IM.nAt l + 4) s [] = none →
      ∀ p w L F tl, IM.k9At Zp l = some p → Desc.K9.testsWhere Zp.p.X l 0 = some w → s.link? = some L →
        s.fork? = some F → s.tl? = some tl → EqLeft p.rows w.2.1 s L F tl) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said fall
      (14 * l + IM.nAt l + 4) := by
  obtain ⟨Lk, p, Qc, bE, bS, He⟩ := k9Ends_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ l hl
  refine He.acceptedE fall (fun _ _ hf => Option.isNone_iff_eq_none.1 hf) fun κ s m En hT hq => ?_
  have hlen : 14 * l + IM.nAt l + 4 ≤ cF.blocksInOrder.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 He.bsE
    exact Nat.le_of_lt hlt
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hlen hT.1
  obtain ⟨Lk', p', w, s₂, a, χ, G, tl, g, Sd, hr2, ha, B⟩ := eq_trace h l hl hr
  obtain ⟨F', hF', hS⟩ := (ledgerOk_iff s).1 (head_ledger h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hT.1 (m := l)
    (by rw [head_sets]; exact open_eq l hl))
  obtain rfl : F' = coefBody tl g G := Option.some.inj (hF'.symm.trans B.fork)
  exact door_of_left B (plan_at_eq h hl Sd.tested hr2 ha) hS
    (left κ s m En hT hq p' w _ _ tl Sd.numbers Sd.tested B.link B.fork B.tail)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eqB_of
#print axioms ProofFile.Honest.K9.outside_of
#print axioms ProofFile.Honest.K9.tested_plan
#print axioms ProofFile.Honest.K9.open_eq
#print axioms ProofFile.Honest.K9.plan_at_eq
#print axioms ProofFile.Honest.K9.door_of_left
#print axioms ProofFile.Honest.K9.accepted_eq_of_left
