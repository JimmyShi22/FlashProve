-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BehindValues.lean: THE TEST ON VALUES OF THE MEMBER BEHIND THE BATCHING, at each of the 25 segments: what the table of the first
chain asks at number 14 l + 10 (l < 24) and at 348 (`ValuesJ`, Honest/Thread/ShapeJV.lean; the cell: `Tab.behind`, Johnson/AtFull/Shape/TableOfSteps.lean).
The cell's Bool is `behindV`, at a feed-forward segment `behindV₃` (Johnson/AtFull/Shape/ValsBool.lean). Its clauses and who pays each:

  freeB      the free-slot test, from the silence of K9's share of the fall (`freeSlotShare`): a premise on the fall, since the clause hangs on the drawn element
  phiSame    proved here: the yes of the batching one member back holds a yes of "K8.equations", whose text tests that the tables are held; every run and the draw leave
             the reading `numOf` that the test looks at
  freeVH     at a feed-forward segment: at the same number of slots it is K9's own clause, so it comes from the same silence; it needs the feed-forward kind's
             structure at the state, which stays a named premise
  valsS      the smallness test's values behind its first run: a named premise hV, the smallness test's own

  `thr_step_back`     the thread one member back: a yes of the step in front
  `tables_of_k8`, `tablesHeld_ride`, `seat_nums`, **`tables_behind`**   behind the batching the tables are held, and a ledger and the record are there
  `freeB_of_share`, `vTw_behind`   the clause `vTw`
  `share_of_quiet`    where the fall's test at the member behind the batching is silent, K9's share is
  `filled_lay`, `freeVH_of_share`   the feed-forward kind's clause: the numbers of slots agree, and it follows from the same silence
  **`behind_values_att`**, **`behind_values_head`**, **`behind_values_lay`**   `ValuesJ` at the member

Limits. T is any thread with T.bs = cF.blocksInOrder; Said, J and fall are letters. The premises on the fall say what the fall must be silent about, and hV is not paid. No property
of a prover or a protocol is proved here.
-/
import Johnson.AtFull.Shape.TableFramesAll
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.ProofFile.Honest.K9.FromYes
import Johnson.Desc.ProofFile.Honest.K9.DrawNum
import Johnson.Desc.ProofFile.Honest.K9.Quiet
import Johnson.Desc.K8.Honest.EqFront
import Johnson.Desc.First.Link.Law.NumRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First.TailClaims.Law.Tests (valsS bareRun)
open VerifiableInference.Desc.First.TailClaims (k8LsTail k8PartP)
open VerifiableInference.Desc.K9.Shape (vTw phiSame tablesHeld_iff)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Look (placeAt)
open Johnson.AtFull.Shape (firstZA behindV behindV₃ freeVH freeRunH cells_link cells_head cell_v)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_of_fold)
open P5J (AtMgA)

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The thread one member back: a yes of the step in front.** -/
theorem thr_step_back {Cl' : Type} (T : Thread Bk S Cl' V W X Pb) {b : ℕ} {κ : Coins Bk} {s' : S} {m : Mid W X} {E : Env}
    (hb : b + 1 ≤ T.bs.length) (hT : Thr T (b + 1) κ s' m E) :
    ∃ s blk, T.bs[b]? = some blk ∧ StepYes T.ft blk s s' := by
  obtain ⟨-, -, -, -, hM, -⟩ := hT
  obtain ⟨-, -, -, -, s₀, c₀, -, -, hf⟩ := hM
  have hr : Reach T.ft T.bs (fun _ : Unit => s₀) (b + 1) ((), s') := reach_of_fold (b + 1) hb s' _ _ _ _ hf
  cases hr with
  | succ hr' hblk hy => exact ⟨_, _, hblk, hy⟩

end

/-- A yes of "K8.equations" holds the tables. -/
theorem tables_of_k8 {n : ℕ} {e : S} {y : List Claim × S} (h : K9L.k8Run.2 n e = .ok y) :
    Desc.K9.tablesHeld e = true := by
  obtain ⟨c, e₁⟩ := y
  obtain ⟨F, tl, funs, tl', F₂, b2, b3, b4, b5, b6⟩ := K9L.k8Run_ok _ _ _ _ h
  unfold Desc.K9.tablesHeld
  rw [b3, b4]
  exact K8.Honest.held_of_yes b5

/-- What the tables' test reads is in `numOf`. -/
theorem tablesHeld_ride (u : HTailF2) {z s : S} (h : K9L.numOf u z = K9L.numOf u s) :
    Desc.K9.tablesHeld z = Desc.K9.tablesHeld s := by
  have h1 : z.tl?.map (First.TailClaims.Law.blank u) = s.tl?.map (First.TailClaims.Law.blank u) := congrArg (·.1) h
  have h2 : z.funs? = s.funs? := congrArg (·.2.1) h
  unfold Desc.K9.tablesHeld
  rw [h2]
  cases hf : s.funs? with
  | none => cases z.tl? <;> cases s.tl? <;> rfl
  | some funs =>
    have e := congrArg (Option.map fun t => Desc.K9.closedList t funs) h1
    rw [Option.map_map, Option.map_map] at e
    have e2 : ((fun t => Desc.K9.closedList t funs) ∘ First.TailClaims.Law.blank u) = fun t => Desc.K9.closedList t funs := rfl
    rw [e2] at e
    cases hz : z.tl? with
    | none =>
      cases hs : s.tl? with
      | none => rfl
      | some t2 => rw [hz, hs] at e; exact nomatch e
    | some t1 =>
      cases hs : s.tl? with
      | none => rw [hz, hs] at e; exact nomatch e
      | some t2 => rw [hz, hs] at e; exact Option.some.inj e

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At a seated link: "K8.equations" stands in the order at the smallness test's own run, and every run that the order names leaves `numOf`. -/
theorem seat_nums (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25) (Sd : SeatedFree cF Zp l k Lk p w) (u : HTailF2) :
    ∃ i, (i, "K8.equations") ∈ Lk.order ∧ (∀ run, At Lk (i, "K8.equations") run → Under run K9L.k8Run.2) ∧
      ∀ o ∈ Lk.order, ∀ run, At Lk o run → ∀ n e c e₁, run n e = .ok (c, e₁) → K9L.numOf u e₁ = K9L.numOf u e := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hord := Sd.order
  by_cases h24 : l = 24
  · subst h24
    have hs : IM.subAt 24 = .head := rfl
    obtain ⟨X, _, Wh⟩ := LPFK9.headOwesC_24 h O hs Lk p hlk seg drawB kp
    have W := Wh (fun _ => False) (((placeAt (P5J.At.X Zp) 24 false).map (·.lm)).getD 0) 0 0 0
      (fun _ _ _ => 0) u u (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl
    refine ⟨5, by rw [hord, hs]; simp [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts], W.ties.tEq, ?_⟩
    exact (run_head (rests_num u) W.seg (take_of_headOwesC W) W.k3f).1
  · by_cases hev : l % 2 = 0
    · have hs : IM.subAt l = .layers := by
        unfold IM.subAt
        rw [if_neg h24, if_pos hev]
      obtain ⟨p4, X, _, _, Wh⟩ := LPFK9.layersOwesC_whole h O l hl hs Lk p hlk seg drawB kp
      have W := Wh (fun _ => False) 0 0 0 0 (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) u u
        fun _ hq => hq.elim
      refine ⟨4, by rw [hord, hs]; simp [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts], W.ties.tEq, ?_⟩
      exact (run_layers (rests_num u) W.seg (take_of_layersOwesC W) W.k3f).1
    · obtain ⟨q, rfl⟩ : ∃ q, l = 2 * q + 1 := ⟨l / 2, by omega⟩
      have hs := sub_odd q (by omega)
      obtain ⟨A, X, _, _, Wh⟩ := LPFK9.attOwesC_g h O (g := q) (by omega) hs Lk p hlk seg drawB kp
      have W := Wh (fun _ => False) (((placeAt (P5J.At.X Zp) (2 * q + 1) false).map (·.lm)).getD 0) 0 0 0 u u
        (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl
      refine ⟨4, by rw [hord, hs]; simp [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts], W.ties.tEq, ?_⟩
      exact (run_attention (rests_num u) W.seg (take_of_attOwesC W) W.k3f).1

/-- **Behind the batching the tables are held, and a ledger is there.** -/
theorem tables_behind {V W X' Pb : Type} {Bk : ProverCoinCounts} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k b : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) (hb : cF.blocksInOrder[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (T : Thread Bk S Claim V W X' Pb) (hbs : T.bs = cF.blocksInOrder) (hlen : b + 1 ≤ T.bs.length) {κ : Coins Bk} {s : S}
    {m : Mid W X'} {E : Env} (hT : Thr T (b + 1) κ s m E) :
    Desc.K9.tablesHeld s = true ∧ ∃ G, s.fork? = some G := by
  obtain ⟨s₀, blk, hblk, R, c, -, hstep⟩ := thr_step_back T hlen hT
  rw [hbs, hb] at hblk
  obtain rfl := Option.some.inj hblk
  obtain ⟨-, tr, -, -, -, y, G, B, -, -⟩ := behind_of_step Sd T.ft s₀ s R c _ hstep
  obtain ⟨t₁, hd, hg, ha₁⟩ := gathered_split p _ s₀ _ y B.gathered
  have u : HTailF2 := {}
  obtain ⟨i, hmem, tEq, nums⟩ := seat_nums h hl Sd u
  obtain ⟨a₀, ha₀⟩ := draw_open p s₀ t₁ _ hd
  have d0 := draw_num u p s₀ t₁ _ a₀ ha₀ hd
  obtain ⟨ls, -, hR⟩ := gather_ran Lk.each Lk.hear Lk.order t₁ (y.2.2, y.1) hg
  obtain ⟨hAll, hEnd⟩ := ran_inv Lk.hear (fun e => K9L.numOf u e = K9L.numOf u s₀) Lk.order 0 t₁ ls y.1
    (fun o ho run hr n t zz hI hz => (nums o ho run hr n t zz.1 zz.2 hz).trans hI) d0 hR
  obtain ⟨lz, -, run, n, e, zz, hr, hI, hz, -⟩ := forall₂_left hAll _ hmem
  have hT8 : Desc.K9.tablesHeld e = true := by
    have hu := tEq run hr n e zz.1 zz.2 hz
    exact tables_of_k8 hu
  have hE : Desc.K9.tablesHeld y.1 = true := by
    rw [tablesHeld_ride u (hEnd.trans hI.symm)]
    exact hT8
  refine ⟨?_, G, B.ledger⟩
  rw [B.state, tablesHeld_ride u (K9L.num_set u y.1 y.2.1 _ ha₁ B.all.plan)]
  exact hE

/-- From the silence of K9's share to the free-slot test, where the ledger and the record are there. -/
theorem freeB_of_share {n : ℕ} {s : S} {F : Fork} {tl : HTailF2} (hF : s.fork? = some F) (ht : s.tl? = some tl)
    (hS : freeSlotShare n s = none) : Desc.K9.Shape.freeB n s = true := by
  have h1 : slotsFree n s = true := by
    unfold freeSlotShare at hS
    by_cases e : slotsFree n s = true
    · exact e
    · rw [if_neg e] at hS
      exact nomatch hS
  have hg : Desc.K9.tAtS.get? s = some { merge := Desc.K9.mergeOf s, tl := tl, F := F } := by
    simp [Desc.K9.tAtS, hF, ht]
  unfold slotsFree at h1
  rw [hg] at h1
  unfold Desc.K9.Shape.freeB
  rw [hF]
  exact h1

/-- Where the fall's test at the member behind the batching is silent, K9's share is. -/
theorem share_of_quiet {n : ℕ} {k4 : Option ℕ} {other : S → Option String} {s : S} {ds : List Fmt.Drawn}
    (h : quietFallTest n k4 other s ds = none) : freeSlotShare n s = none := by
  unfold quietFallTest at h
  cases e : freeSlotShare n s with
  | none => rfl
  | some y =>
    rw [e] at h
    exact nomatch h

/-- **The clause vTw at the member behind the batching.** -/
theorem vTw_behind {V W X' Pb : Type} {Bk : ProverCoinCounts} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k b : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) (hb : cF.blocksInOrder[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (T : Thread Bk S Claim V W X' Pb) (hbs : T.bs = cF.blocksInOrder) (hlen : b + 1 ≤ T.bs.length) {κ : Coins Bk} {s : S}
    {m : Mid W X'} {E : Env} (hT : Thr T (b + 1) κ s m E) (hS : freeSlotShare w.2.2.filled s = none) :
    vTw w s = true := by
  obtain ⟨hH, G, hG⟩ := tables_behind h hl Sd hb T hbs hlen hT
  obtain ⟨-, hP⟩ := (tablesHeld_iff s).1 hH
  have ⟨tl, ht⟩ : ∃ tl, s.tl? = some tl := by
    unfold Desc.K9.tablesHeld at hH
    cases e : s.tl? with
    | none => rw [e] at hH; exact nomatch hH
    | some tl => exact ⟨tl, rfl⟩
  unfold vTw
  rw [Bool.and_eq_true]
  exact ⟨freeB_of_share hG ht hS, hP⟩

section
variable {V W X' Pb : Type} {Bk : ProverCoinCounts} {Bs : ProofFile.PureBase} {J : ℕ → S → Prop}

/-- **At the attention segment 2 g + 1.** -/
theorem behind_values_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hw : Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some w)
    {Xl : Stages.LinkH} (hX : Bs.G₀.built[2 * g + 1]? = some Xl) (T : Thread Bk S Claim V W X' Pb) (hbs : T.bs = cF.blocksInOrder)
    {Said : ℕ → Coins Bk → Mid W X' → Prop} {fall : ℕ → S → List Fmt.Drawn → Option String}
    (hfall : ∀ s ds, fall (14 * (2 * g + 1) + 10) s ds = none → freeSlotShare w.2.2.filled s = none)
    (hV : ∀ κ s m E ds s₁, ThrS T Said (14 * (2 * g + 1) + 10) κ s m E → fall (14 * (2 * g + 1) + 10) s ds = none →
      bareRun k8LsTail.2 s = .ok s₁ → valsS (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g + 1)).nU s₁ = true) :
    ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (14 * (2 * g + 1) + 10) := by
  intro blk hblk κ s m E ds y cols hT _ _ _ hf _
  have hc : Johnson.AtFull.Shape.Tab.cells Zp Bs.G₀ (14 * (2 * g + 1) + 10) = Johnson.AtFull.Shape.Tab.behind Zp Bs.G₀ (2 * g + 1) :=
    cells_link Zp Bs.G₀ (2 * g + 1) 9 (by omega) (by omega) rfl
  unfold Johnson.AtFull.Shape.Tab.behind at hc
  rw [hX, hw] at hc
  simp only [show ((2 * g + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega),
    Bool.false_and, Bool.false_eq_true, if_false] at hc
  show Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ _ s _ _ = true
  rw [cell_v hc]
  show behindV w _ s = true
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨Lk, p, w', Sd⟩ := seated_at_head h (2 * g + 1) hl
  obtain rfl : w' = w := Option.some.inj (Sd.tested.symm.trans hw)
  rw [if_neg (by omega)] at Sd
  have hlen : 14 * (2 * g + 1) + 9 + 1 + 1 ≤ T.bs.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hv := vTw_behind h hl Sd Sd.batching T hbs (by omega) hT.1 (hfall s ds hf)
  unfold behindV
  rw [Bool.and_eq_true]
  refine ⟨hv, ?_⟩
  split
  · rename_i s₁ h₁
    exact hV κ s m E ds s₁ hT hf h₁
  · rfl

/-- **At the head's segment, number 348.** -/
theorem behind_values_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hw : Desc.K9.testsWhere Zp.p.X 24 0 = some w)
    {Xl : Stages.LinkH} (hX : Bs.G₀.built[24]? = some Xl) (T : Thread Bk S Claim V W X' Pb) (hbs : T.bs = cF.blocksInOrder)
    {Said : ℕ → Coins Bk → Mid W X' → Prop} {fall : ℕ → S → List Fmt.Drawn → Option String}
    (hfall : ∀ s ds, fall 348 s ds = none → freeSlotShare w.2.2.filled s = none)
    (hV : ∀ κ s m E ds s₁, ThrS T Said 348 κ s m E → fall 348 s ds = none →
      bareRun k8LsTail.2 s = .ok s₁ → valsS (ProofFile.k8ParW Zp Bs.G₀ Xl 24).nU s₁ = true) :
    ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall 348 := by
  intro blk hblk κ s m E ds y cols hT _ _ _ hf _
  have hc : Johnson.AtFull.Shape.Tab.cells Zp Bs.G₀ 348 = Johnson.AtFull.Shape.Tab.behind Zp Bs.G₀ 24 :=
    cells_head Zp Bs.G₀ 11 (by omega) rfl
  unfold Johnson.AtFull.Shape.Tab.behind at hc
  rw [hX, hw] at hc
  show Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ _ s _ _ = true
  rw [cell_v hc]
  show behindV w _ s = true
  have hl : 24 < 25 := by omega
  obtain ⟨Lk, p, w', Sd⟩ := seated_at_head h 24 hl
  obtain rfl : w' = w := Option.some.inj (Sd.tested.symm.trans hw)
  rw [if_pos rfl] at Sd
  have hlen : 347 + 1 + 1 ≤ T.bs.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hv := vTw_behind (b := 347) h hl Sd Sd.batching T hbs (by omega) hT.1 (hfall s ds hf)
  unfold behindV
  rw [Bool.and_eq_true]
  refine ⟨hv, ?_⟩
  split
  · rename_i s₁ h₁
    exact hV κ s m E ds s₁ hT hf h₁
  · rfl

/-- At a feed-forward segment the number of slots of the tests behind the adding is the plan's. -/
theorem filled_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hw : Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some w)
    {hp : Layer.HPlan2} (hH : Zp.p.X.G[g]? = some hp) : hp.used = w.2.2.filled := by
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have h4' : Zp.p.X.p4 = true := h4
  have hN' : Zp.p.X.NGr = 12 := hN
  unfold Desc.K9.testsWhere at hw
  simp only [h4', hN', if_true] at hw
  have e1 : (2 * g == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g) % 2 == 0) = true := by
    rw [beq_iff_eq]
    omega
  have e3 : 2 * g / 2 = g := by omega
  rw [e1, e2, e3, hH] at hw
  obtain rfl := Option.some.inj (hw)
  rfl

/-- **Behind the smallness test's first run, the feed-forward kind's free slot, from K9's silence at the same number.** -/
theorem freeVH_of_share {hp : Layer.HPlan2} {s s₁ : S} {a : First.LayOwn} {o : OnBytes.Model.Layer.Own}
    (hh : s.here = .lay a) (ho : a.own = some o) (hS : freeSlotShare hp.used s = none)
    (h₁ : bareRun k8LsTail.2 s = .ok s₁) : freeVH hp s₁ = true := by
  have hk := k4Share_silent hp.used s hS
  have hfree : OnBytes.Desc.First.K4.freeSlotOk hp.used o.wo.sFv a.F = true := by
    unfold k4FreeShare at hk
    rw [hh] at hk
    simp only [ho] at hk
    by_cases e : OnBytes.Desc.First.K4.freeSlotOk hp.used o.wo.sFv a.F = true
    · exact e
    · rw [if_neg e] at hk
      exact nomatch hk
  unfold bareRun K8.atRecord at h₁
  cases hq : k8PartP.get? s with
  | none =>
    rw [hq] at h₁
    exact nomatch h₁
  | some q =>
    rw [hq] at h₁
    have hF : s.fork? = some a.F := by simp [S.fork?, hh]
    have hq' : First.TailClaims.Law.partOf s = some q := hq
    obtain ⟨-, -, h2⟩ := K8.Honest.parts_of hq'
    have eF : q.F = a.F := Option.some.inj (h2.symm.trans hF)
    have e : s₁ = (s.putTl { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB }).putFork q.F := by
      simpa [k8LsTail, Except.map] using (Except.ok.inj h₁).symm
    subst e
    unfold freeVH S.putTl S.putFork
    simp [hh, ho, eF, hfree]

/-- **At the feed-forward segment 2 g.** -/
theorem behind_values_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hw : Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some w)
    {Xl : Stages.LinkH} (hX : Bs.G₀.built[2 * g]? = some Xl) {hp : Layer.HPlan2} (hH : Bs.G₀.W.G[g]? = some hp)
    (hWX : Bs.G₀.W = Zp.p.X) (T : Thread Bk S Claim V W X' Pb) (hbs : T.bs = cF.blocksInOrder)
    {Said : ℕ → Coins Bk → Mid W X' → Prop} {fall : ℕ → S → List Fmt.Drawn → Option String}
    (hfall : ∀ s ds, fall (14 * (2 * g) + 10) s ds = none → freeSlotShare w.2.2.filled s = none)
    (hown : ∀ κ s m E ds, ThrS T Said (14 * (2 * g) + 10) κ s m E → fall (14 * (2 * g) + 10) s ds = none →
      ∃ a o, s.here = .lay a ∧ a.own = some o)
    (hV : ∀ κ s m E ds s₁ s₂, ThrS T Said (14 * (2 * g) + 10) κ s m E → fall (14 * (2 * g) + 10) s ds = none →
      bareRun k8LsTail.2 s = .ok s₁ → freeRunH hp s₁ = .ok s₂ →
      valsS (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU s₂ = true) :
    ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall
      (14 * (2 * g) + 10) := by
  intro blk hblk κ s m E ds y cols hT _ _ _ hf _
  have hc : Johnson.AtFull.Shape.Tab.cells Zp Bs.G₀ (14 * (2 * g) + 10) = Johnson.AtFull.Shape.Tab.behind Zp Bs.G₀ (2 * g) :=
    cells_link Zp Bs.G₀ (2 * g) 9 (by omega) (by omega) rfl
  unfold Johnson.AtFull.Shape.Tab.behind at hc
  rw [hX, hw] at hc
  simp only [show ((2 * g) % 2 == 0) = true from beq_iff_eq.2 (by omega),
    show (2 * g != 24) = true from bne_iff_ne.2 (by omega), Bool.and_self, if_true,
    show 2 * g / 2 = g from by omega, hH] at hc
  show Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ _ s _ _ = true
  rw [cell_v hc]
  show behindV₃ w hp _ s = true
  have hl : 2 * g < 25 := by omega
  obtain ⟨Lk, p, w', Sd⟩ := seated_at_head h (2 * g) hl
  obtain rfl : w' = w := Option.some.inj (Sd.tested.symm.trans hw)
  rw [if_neg (by omega)] at Sd
  have hlen : 14 * (2 * g) + 9 + 1 + 1 ≤ T.bs.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hS := hfall s ds hf
  have hv := vTw_behind h hl Sd Sd.batching T hbs (by omega) hT.1 hS
  have hu : hp.used = w'.2.2.filled := filled_lay h hg hw (hWX ▸ hH)
  obtain ⟨a, o, hh, ho⟩ := hown κ s m E ds hT hf
  unfold behindV₃
  rw [Bool.and_eq_true]
  refine ⟨hv, ?_⟩
  split
  · rename_i s₁ h₁
    rw [Bool.and_eq_true]
    refine ⟨freeVH_of_share hh ho (hu ▸ hS) h₁, ?_⟩
    split
    · rename_i s₂ h₂
      exact hV κ s m E ds s₁ s₂ hT hf h₁ h₂
    · rfl
  · rfl

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.thr_step_back
#print axioms ProofFile.Honest.K9.tables_of_k8
#print axioms ProofFile.Honest.K9.tablesHeld_ride
#print axioms ProofFile.Honest.K9.seat_nums
#print axioms ProofFile.Honest.K9.tables_behind
#print axioms ProofFile.Honest.K9.freeB_of_share
#print axioms ProofFile.Honest.K9.share_of_quiet
#print axioms ProofFile.Honest.K9.vTw_behind
#print axioms ProofFile.Honest.K9.behind_values_att
#print axioms ProofFile.Honest.K9.behind_values_head
#print axioms ProofFile.Honest.K9.filled_lay
#print axioms ProofFile.Honest.K9.freeVH_of_share
#print axioms ProofFile.Honest.K9.behind_values_lay
