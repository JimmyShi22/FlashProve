-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqValues.lean: THREE OF THE FOUR TESTS ON VALUES THAT THE SUB-PROTOCOL "THE ONE EQUATION" ASKS
OF THE STATE IN FRONT (`outsideV`, `slotsV`, `termsV`: three clauses of `oneV`, Johnson/AtFull/Shape/ValsBool.lean) ACCEPT AT
EVERY STATE THAT IS REACHED THERE: at each of the 25 segments of the first chain, under the library's hypothesis `AtMgA`;
whoever plays. None of the three hangs on a drawn element: no fall is owed for them.

What each is, and how it is paid.
  "No array beyond the list bears a weight" (`outsideV`). No test on values at such a state: the ledger has just the listed
  arrays. The plans end their lists so; the opening lays the plan's arrays and list; nothing in between adds an array. "A slot
  with a coefficient is filled" (`slotsV`). The adding of a claim never asks whether a slot is filled. But the draw has tested
  that all slots are in use, and the step on the state's shape at this sub-protocol (`oneGS`,
  Johnson/AtFull/Shape/EquationStepAtHead.lean) tests that the slots in use are all filled. So it follows FROM A RETURN OF THAT
  STEP, which is a premise here. "The written-out weights of a virtual row are its product form's" (`termsV`). The library has
  it behind a yes of the step "behind the batching", from three sentences on the state in front of that step (`FrontOfTests`,
  `termsV_scope`: Johnson/AtFull/Shape/RowFormTested.lean, RowFormSeat.lean). Here the three are paid at every state reached
  there: the arrays of the vectors have one row (the library's static clauses in front of the batching); the smallness test's
  record holds the powers of the drawn element (its own run of claims lays them, and the runs behind leave the record); no
  virtual row has a form or lists of factors (Honest/K9/FrontIs.lean; the draw, the runs and the adding turn the weights on
  columns alone).

  `ran_then`            along the thread of the runs that the batching gathers: a sentence that one run lays, and the runs
                        behind hand on, holds behind the last
  `eqB_of_oneG`, `slotsV_of_eqB`   from the step on the shape to the tests on numbers and marks; from these, where all slots are
                        in use, to `slotsV`
  `rowClean_of_bareL`   rows that are empty but for the weights on columns are clean
  **`frontOfTests_at`**   `FrontOfTests` at every state reached at 14 l + `IM.nAt l` + 3
  **`outsideV_at`**, **`slotsV_at`**, **`termsV_at`**   at every state reached at 14 l + `IM.nAt l` + 4
  **`values_at`**         the field `values` of `OneRest` (Johnson/Desc/First/Batch/Shape/DoorChain.lean) there

Limits. Of reached states: that any state is reached is not proved here. `slotsV_at` and `values_at` have the return of the step
on the shape as a premise. The fourth test on values (no coefficient on a pad) is not treated. The full size and the hash
function `secondHashFunction` alone: the hypothesis's. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.FrontIs
import Johnson.Desc.ProofFile.Honest.K9.EqLeft
import Johnson.Desc.ProofFile.Honest.K9.RunCores
import Johnson.AtFull.Shape.RowFormSeat
import Johnson.AtFull.Shape.ValsBool
import Johnson.P1K8R.StaticAtBatch
import Johnson.P5T.StaticWholeAtMg
import Johnson.Desc.K8.Honest.PoweredOfYes
import Johnson.Desc.K8.Honest.AddTheta
import Johnson.Desc.First.TailClaims.EquationsBlank
import Johnson.Desc.First.Batch.Law.KeepsTl

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (Powered uOf)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (coefBody equations)
open VerifiableInference.Desc.First.TailClaims.Law (partOf sits_equations partOf_some part_set blank eq_blank)
open VerifiableInference.Desc.First.K8.Honest (powered_of_yes addList_theta)
open VerifiableInference.Desc.First.Shape (chainSh linkSh ledSh ChainSh)
open VerifiableInference.Desc.K9.Shape (eqB eqB_sh eqSh oneG laidSh outsideV slotsV termsV OneRest)
open VerifiableInference.Desc.LinkJoin (LooksAre looks_frame looks_fill shape_at)
open Johnson.AtFull.Shape (FrontOfTests TestsFront EachRow RowClean rowClean_of_fresh termsV_scope oneGS)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 General -/

/-- **A sentence that one run of the order lays holds behind the last.** I: what every run hands on; J: what the run at o₀
lays under I, and the runs behind hand on under I. -/
theorem ran_then (bs : List (Block S Claim)) (I J : S → Prop) (o₀ : ℕ × String) (post : List (ℕ × String))
    (hJ : ∀ o ∈ post, ∀ run, claimsRunOf bs o = some run → ∀ n t z, I t → J t → run n t = .ok z → J z.2)
    (hL : ∀ run, claimsRunOf bs o₀ = some run → ∀ n t z, I t → run n t = .ok z → J z.2) :
    ∀ (pre : List (ℕ × String)) (n : ℕ) (t : S) (ls : List (List Claim)) (e : S),
    (∀ o ∈ pre ++ o₀ :: post, ∀ run, claimsRunOf bs o = some run → ∀ n t z, I t → run n t = .ok z → I z.2) →
    I t → Ran bs (pre ++ o₀ :: post) n t ls e → I e ∧ J e
  | [], _, _, [], _, _, _, h => h.elim
  | [], n, t, l :: ls, e, hI, h0, h => by
    obtain ⟨run, u, hr, hz, hrest⟩ := h
    have hu : I u := hI o₀ List.mem_cons_self run hr n t (l, u) h0 hz
    have ju : J u := hL run hr n t (l, u) h0 hz
    exact (ran_inv bs (fun x => I x ∧ J x) post (n + l.length) u ls e
      (fun o' ho' run' hr' n' t' z' hIJ hz' =>
        ⟨hI o' (List.mem_cons_of_mem _ ho') run' hr' n' t' z' hIJ.1 hz',
          hJ o' ho' run' hr' n' t' z' hIJ.1 hIJ.2 hz'⟩)
      ⟨hu, ju⟩ hrest).2
  | _ :: _, _, _, [], _, _, _, h => h.elim
  | o :: pre, n, t, l :: ls, e, hI, h0, h => by
    obtain ⟨run, u, hr, hz, hrest⟩ := h
    have hu : I u := hI o List.mem_cons_self run hr n t (l, u) h0 hz
    exact ran_then bs I J o₀ post hJ hL pre (n + l.length) u ls e
      (fun o' ho' => hI o' (List.mem_cons_of_mem _ ho')) hu hrest

/-- From a return of the step on the shape to the tests on numbers and marks. -/
theorem eqB_of_oneG {s : S} {u : ChainSh} {L : LinkCtx} {F : Fork} (hL : s.link? = some L)
    (hF : s.fork? = some F) (hg : oneG (chainSh s) = .ok u) : eqB L F = true := by
  unfold oneG at hg
  have l1 : (chainSh s).link = some (linkSh L) := by
    show s.link?.map linkSh = _
    rw [hL]
    rfl
  have l2 : (chainSh s).led = some (ledSh F) := by
    show s.fork?.map ledSh = _
    rw [hF]
    rfl
  rw [l1, l2] at hg
  cases l3 : (chainSh s).tl with
  | none => rw [l3] at hg; exact nomatch hg
  | some tsh =>
    rw [l3] at hg
    simp only at hg
    cases l4 : laidSh tsh with
    | none => rw [l4] at hg; exact nomatch hg
    | some n =>
      rw [l4] at hg
      simp only at hg
      split at hg
      · rename_i hc
        rw [Bool.and_eq_true] at hc
        rw [eqB_sh]
        exact hc.1
      · exact nomatch hg

/-- Where all slots are in use, the tests on numbers and marks give: a slot with a coefficient is filled. -/
theorem slotsV_of_eqB {L : LinkCtx} {F : Fork} (h : eqB L F = true) (hu : L.list.used = F.ns) :
    slotsV { F with doorShutF := true } = true := by
  unfold eqB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, ⟨⟨⟨⟨-, s1⟩, s2⟩, -⟩, -⟩⟩, -⟩, hall⟩ := h
  unfold slotsV
  rw [List.all_eq_true]
  intro j hj
  have hj' : j < F.LS.size := List.mem_range.1 hj
  have hjg : j < F.gotF.size := by omega
  have k := (Array.all_iff_forall.1 hall) j hjg ⟨Nat.zero_le _, by omega⟩
  rw [Bool.or_eq_true]
  refine Or.inr ?_
  show F.gotF.getD j false = true
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjg]
  exact k

/-- Rows that are empty but for the weights on columns are clean. -/
theorem rowClean_of_bareL {G : Fork} (h : BareL G.trees) : EachRow RowClean G := by
  refine rowClean_of_fresh G fun t e hr => ?_
  obtain ⟨h1, h2⟩ := hr
  have e1 : G.trees.getD t {} = G.trees[t] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1]
    rfl
  rw [e1] at h2
  have e2 : _root_.Fo.rowAt G t e = (G.trees[t]).rows[e] := by
    unfold _root_.Fo.rowAt
    rw [e1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
    rfl
  have k := h _ (Array.getElem_mem h1) _ (Array.getElem_mem h2)
  rw [e2]
  exact ⟨congrArg (·.rowForm) k, congrArg (·.rowLo) k, congrArg (·.rowHi) k⟩

/-! ## 2 Under the hypothesis -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The three sentences in front of the step "behind the batching", at every state reached there.** -/
theorem frontOfTests_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {z : ProofFile.InstPub}
    {s₁ : TS} (hr1 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 3) (z, s₁)) : FrontOfTests s₁ := by
  obtain ⟨Lk, p, w, Sd₀⟩ := seated_at_head h l hl
  have Sd : SeatedFree cF Zp l (IM.nAt l) Lk p w := Sd₀
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨z2, s₂, s'', b2, e2, hr2, hb2, hy2⟩ := reach_pred (k := 14 * l + IM.nAt l + 2) hr1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
  obtain rfl : Lk.batch (claimsInBy Lk.each Lk.hear Lk.order) = b2 := Option.some.inj (Sd.batching.symm.trans hb2)
  obtain ⟨R, c, -, hstep⟩ := hy2
  obtain ⟨r0, tw, -, -, -, y, G, hB, -, -⟩ := behind_of_step Sd 0 s₂ s₁ R c c.length hstep
  obtain ⟨t₁, hdraw, hg, he⟩ := gathered_split p _ s₂ _ y hB.gathered
  obtain ⟨a, ha, hready⟩ := (draw_iff p s₂ _).1 ⟨t₁, hdraw⟩
  have et := draw_is p s₂ t₁ _ a ha hdraw
  obtain ⟨a₁, h1, hl1⟩ := draw_facts p s₂ t₁ _ a ha hdraw
  obtain ⟨a', ha', hcore⟩ := Sd.keeps t₁ y.1 y.2.2 a₁ hg h1
  obtain rfl : a' = y.2.1 := Option.some.inj (ha'.symm.trans he)
  obtain ⟨tl₂, u₂, hL₂, hF₂, ht₂, -⟩ := part_all ha
  have hframe : treesFrame G.trees = treesFrame (t2FillL a.F a.L.list).trees := by
    rw [hB.all.frame, hcore.frame, hl1.trees]
  -- the link's order, cut at the smallness test's run
  obtain ⟨Lk', Xl, eLk, eX, K, -⟩ := TocK8.k08_scope h.scope h.reads O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (eLk.symm.trans Sd.link)
  obtain ⟨ls, -, hran⟩ := gather_ran Lk'.each Lk'.hear Lk'.order t₁ (y.2.2, y.1) hg
  have hmem : ∀ o ∈ Lk'.order, ∀ run, claimsRunOf Lk'.hear o = some run → RunKeeps run := by
    intro o ho run hrun
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
    exact cores_at_head h hl Sd j o run hj hrun
  rw [K.order] at hran hmem
  have ht₁ : t₁.tl? = some tl₂ := by
    rw [et, K9L.tl_set]
    exact ht₂
  -- what every run hands on: the lens answers, the batching element is the drawn one, the record's map is as in front
  obtain ⟨⟨⟨aE, hE1, hE2⟩, tlE, hE3, hE4⟩, tlP, hP1, hP2⟩ := ran_then Lk'.hear
    (fun t => (∃ q, Desc.K9.atS.get? t = some q ∧ q.F.theta = E.ofTriple tw) ∧
      ∃ tl, t.tl? = some tl ∧ tl.ix = tl₂.ix)
    (fun t => ∃ tl, t.tl? = some tl ∧ Powered tl (E.ofTriple tw))
    _ _
    (fun o ho run hrun n t zz _ hJt hz => by
      obtain ⟨tl, e1, e3⟩ := hJt
      have k := congrArg Prod.fst (K.hpost o ho run hrun n t zz.1 zz.2 hz)
      exact ⟨tl, (show zz.2.tl? = t.tl? from k).trans e1, e3⟩)
    (fun run hrun n t zz hIt hz => by
      obtain ⟨⟨q0, g1, g2⟩, -⟩ := hIt
      obtain ⟨rK, h8, hu⟩ := K.hE run hrun
      obtain ⟨q, tl', F1, hq, heq, e⟩ := (sits_equations _ rK h8 n t zz.2 zz.1).1 (hu n t zz hz)
      obtain ⟨-, qF, -⟩ := partOf_some.1 hq
      have eF : q0.F = q.F := Option.some.inj ((Desc.K9.get_fork t q0 g1).symm.trans qF)
      obtain ⟨c1, -, -⟩ := partOf_some.1 (part_set hq { q with tl := tl', F := F1 })
      refine ⟨tl', ?_, ?_⟩
      · rw [e]
        exact c1
      · rw [← g2, eF]
        exact powered_of_yes heq)
    _ 0 t₁ ls y.1
    (fun o ho run hrun n t zz hIt hz => by
      obtain ⟨⟨q0, g1, g2⟩, tl, g3, g4⟩ := hIt
      obtain ⟨q1, k1, k2⟩ := hmem o ho run hrun n t zz hz q0 g1
      refine ⟨⟨q1, k1, k2.theta.trans g2⟩, ?_⟩
      rcases List.mem_append.1 ho with hp | hp
      · have k := congrArg Prod.fst (K.hpre o hp run hrun n t zz.1 zz.2 hz)
        exact ⟨tl, (show zz.2.tl? = t.tl? from k).trans g3, g4⟩
      · rcases List.mem_cons.1 hp with rfl | hp
        · obtain ⟨rK, h8, hu⟩ := K.hE run hrun
          obtain ⟨q, tl', F1, hq, heq, e⟩ := (sits_equations _ rK h8 n t zz.2 zz.1).1 (hu n t zz hz)
          obtain ⟨qT, -, -⟩ := partOf_some.1 hq
          obtain rfl : tl = q.tl := Option.some.inj (g3.symm.trans qT)
          obtain ⟨c1, -, -⟩ := partOf_some.1 (part_set hq { q with tl := tl', F := F1 })
          refine ⟨tl', ?_, ?_⟩
          · rw [e]
            exact c1
          · exact (congrArg (·.ix) (eq_blank {} heq) : tl'.ix = q.tl.ix).trans g4
        · have k := congrArg Prod.fst (K.hpost o hp run hrun n t zz.1 zz.2 hz)
          exact ⟨tl, (show zz.2.tl? = t.tl? from k).trans g3, g4⟩)
    ⟨⟨a₁, h1, hl1.chi⟩, tl₂, ht₁, rfl⟩ hran
  obtain rfl : tlE = tlP := Option.some.inj (hE3.symm.trans hP1)
  obtain rfl : aE = y.2.1 := Option.some.inj (hE1.symm.trans he)
  have hθ : G.theta = E.ofTriple tw := (addList_theta _ _ _ hB.added).trans hE2
  have hs₁ : s₁.tl? = some tlE := by
    rw [hB.state, K9L.tl_set]
    exact hE3
  -- the static clauses in front of the batching
  have hr2' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + (if l = 24 then 11 else 9)) (z, s₂) := by
    have e : 14 * l + IM.nAt l + 2 = 14 * l + (if l = 24 then 11 else 9) := by
      unfold IM.nAt
      split <;> rfl
    rw [← e]
    exact hr2
  have St := P1K8.static_at_batch h.scope h.reads O hl eX hr2' ht₂ hF₂
    (h.toAtMg.staticOk_ground O.blank hl eX)
  have hlooks : LooksAre (a.F.trees.toList.map LinkJoin.look) G :=
    looks_frame hframe (looks_fill a.F a.L.list rfl)
  intro F tl hF ht
  obtain rfl : G = F := Option.some.inj (hB.ledger.symm.trans hF)
  obtain rfl : tlE = tl := Option.some.inj (hs₁.symm.trans ht)
  refine ⟨fun n t hU _ => ?_, by rw [hθ]; exact hP2, ?_⟩
  · have hu : uOf tl₂ { tree := n } = t := by
      unfold uOf
      rw [← hE4, hU]
      rfl
    have k := St.units { tree := n }
    rw [hu] at k
    exact (shape_at hlooks t k).2.2
  · exact rowClean_of_bareL (bareL_of_frame hframe
      (bareL_fill a.F a.L.list (bare_at_front h.scope h.reads O hl hr2 hL₂ hF₂)))

/-- **The ledger has just the listed arrays: so no array beyond the list bears a weight.** -/
theorem outsideV_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s)) {L : LinkCtx} {F : Fork}
    (hL : s.link? = some L) (hF : s.fork? = some F) :
    F.trees.size = L.list.nt.size ∧ outsideV L F = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, w, s₂, a, χ, G, tl, g, -, hr2, ha, B⟩ := eq_trace h l hl hr
  obtain ⟨tl₂, u₂, hL₂, hF₂, -⟩ := part_all ha
  obtain rfl := Option.some.inj (B.link.symm.trans hL)
  obtain rfl := Option.some.inj (B.fork.symm.trans hF)
  have a1 : (coefBody tl g G).trees.size = G.trees.size := (_root_.Fo.frame_all tl g G).1
  have a2 : G.trees.size = (t2FillL a.F a.L.list).trees.size := by
    have k := congrArg Array.size B.frame
    simpa [treesFrame] using k
  have a3 : (t2FillL a.F a.L.list).trees.size = a.F.trees.size := by
    have k : LooksAre (a.F.trees.toList.map LinkJoin.look) (t2FillL a.F a.L.list) := looks_fill a.F a.L.list rfl
    have k' := congrArg List.length k
    simpa using k'
  have a4 := sizes_at_front h.scope h.reads O hl hr2 hL₂ hF₂
  have e : (coefBody tl g G).trees.size = (drawnPart p a χ).L.list.nt.size := by
    rw [a1, a2, a3, a4]
    rfl
  exact ⟨e, outside_of _ _ e⟩

/-- **A slot with a coefficient is filled**, where the step on the state's shape returns. -/
theorem slotsV_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s)) {u : ChainSh}
    (hg : oneGS (chainSh s) = .ok u) {L : LinkCtx} {F : Fork} (hL : s.link? = some L) (hF : s.fork? = some F) :
    slotsV { F with doorShutF := true } = true := by
  obtain ⟨Lk, p, w, s₂, a, χ, G, tl, g, -, hr2, ha, B⟩ := eq_trace h l hl hr
  have hg' : oneG (chainSh s) = .ok u := by
    unfold oneGS at hg
    split at hg
    · exact nomatch hg
    · exact hg
  refine slotsV_of_eqB (eqB_of_oneG hL hF hg') ?_
  obtain rfl := Option.some.inj (B.link.symm.trans hL)
  obtain rfl := Option.some.inj (B.fork.symm.trans hF)
  have hrd := B.ready
  unfold drawReady at hrd
  simp only [Bool.and_eq_true, beq_iff_eq] at hrd
  have e1 : a.used = a.F.ns := hrd.1.1.1.1.1.1.2.2
  have e2 : (coefBody tl g G).ns = G.ns := (congrArg (·.ns) (butTrees_coefBody tl g G) : _)
  show a.used = (coefBody tl g G).ns
  rw [e1, e2, B.ns]

/-- **The written-out weights of every virtual row are its product form's.** -/
theorem termsV_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s)) {F : Fork} (hF : s.fork? = some F)
    (L : LinkCtx) : termsV L { F with doorShutF := true } = true := by
  obtain ⟨Lk, p, w, Sd₀⟩ := seated_at_head h l hl
  have Sd : SeatedFree cF Zp l (IM.nAt l) Lk p w := Sd₀
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨z1, s₁, s', b1, e1, hr1, hb1, hy1⟩ := reach_pred (k := 14 * l + IM.nAt l + 3) hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain ⟨bb, hbb, -, hdec⟩ := Sd.behind
  obtain rfl : bb = b1 := Option.some.inj (hbb.symm.trans hb1)
  obtain ⟨rs1, gs1, hd1⟩ := stepYes_decide hy1
  rw [hdec] at hd1
  obtain ⟨Lk', eLk, hT⟩ := termsV_scope h.scope h.reads O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (eLk.symm.trans Sd.link)
  obtain ⟨F₁, hF₁, hv⟩ := hT s₁ s hd1 (frontOfTests_at h l hl hr1)
  obtain rfl : F₁ = F := Option.some.inj (hF₁.symm.trans hF)
  exact hv L

/-- **The three, as `OneRest` asks them.** -/
theorem values_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s)) {u : ChainSh}
    (hg : oneGS (chainSh s) = .ok u) :
    ∀ L F, s.link? = some L → s.fork? = some F →
      outsideV L F = true ∧ termsV L { F with doorShutF := true } = true ∧
        slotsV { F with doorShutF := true } = true :=
  fun L _ hL hF => ⟨(outsideV_at h l hl hr hL hF).2, termsV_at h l hl hr hF L, slotsV_at h l hl hr hg hL hF⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.ran_then
#print axioms ProofFile.Honest.K9.eqB_of_oneG
#print axioms ProofFile.Honest.K9.slotsV_of_eqB
#print axioms ProofFile.Honest.K9.rowClean_of_bareL
#print axioms ProofFile.Honest.K9.frontOfTests_at
#print axioms ProofFile.Honest.K9.outsideV_at
#print axioms ProofFile.Honest.K9.slotsV_at
#print axioms ProofFile.Honest.K9.termsV_at
#print axioms ProofFile.Honest.K9.values_at
