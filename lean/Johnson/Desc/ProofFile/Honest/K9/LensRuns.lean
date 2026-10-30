-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/LensRuns.lean: FOR THE ITEM "totalB": THE SORT's OWN RUNS' NUMBERS OF CLAIMS AT EVERY
STAND OF THE BATCHING, AT THE HEAD's SEGMENT AND AT THE FEED-FORWARD SEGMENTS: PAID; AND SO THERE `LensAt` FROM THE YES
OF OUR PUBLIC TEST (`LensEqAsked`) ALONE, BESIDE THE HEAD, AN OPENING O, THE SEAT AND THE READINGS, WHICH THE ASSEMBLIES
ALREADY BIND. THE ATTENTION SEGMENTS: Honest/K9/LensAttPaid.lean. Statements and proofs: calls; no goal is stated.
  **`runs_at_fixed`**   under `SealLaw` (Honest/K9/TotalFront.lean), at a yes of the batching's step at s where the
      promise holds at what is fixed at s: every run that the link's order names has returned at a state that goes on
      from what is fixed at s (`Fx9`). By our `gather_ran` and `ran_inv` (Honest/K9/GatherFold.lean) along the library's
      `RunOk` of each run
  `headRuns_lens`   the premises hruns and hjoin of `lensAt_head` (Honest/K9/LensAtStand.lean), to the letter: 29, 4, 2
      and 1: each run's forms are there because the run has returned (the library's `k6_still`, `join_marks`: the field
      forms; the ties of `take_head`), and then `lenK6_eq`, `lenJoin_eq` (Johnson/Desc/K9/Honest/LensSmall.lean)
  **`lensAt_head_runs`**   `LensAt` at the head's segment, in the very form of the premise hlens of `givesTotalB_head`,
      from hLE (`LensEqAsked Zp`), O, Sd, e3, hd, hC, hD
  `frontRun_lens`   the premise hruns of `lensAt_lay`, to the letter: frontB: at every state reached in front of the
      batching the state holds the feed-forward kind's own structure, at the plan's layout (the library's `layers_root`,
      `own_layout`); that kind's parameters at the segment have k3Runs = true and the group's number
      (`LPFK9.k4ParAt_of_mem`, `IM.k4_of`); then `lenFront_eq`. It needs neither the seat nor the promise: it holds at
      every Lk and p
  **`lensAt_lay_runs`**   `LensAt` at a feed-forward segment, in the very form of the premise hlens of
      `givesTotalB_lay`, from hLE, O, g < 12, Sd, e3, hd, hk, hC, hD
WHAT STAYS OF hlens: at all three sorts hLE: public: a test with code that no verifier asks; evaluated true at the
stored full-size example alone, proved at no public part (Johnson/Desc/K9/Honest/LensEq.lean): OURS. At the attention
segments the number of K5's two runs together (attOwnB), which `lensAt_att_look` (Honest/K9/LensLook.lean) leaves owed,
is paid in Honest/K9/LensAttPaid.lean, by that kind's house's count and `runs_at_fixed`.
GROUND: beside the sealed library, what lies beneath Honest/K9/LensLook.lean. At the full size and the format's second
hash function alone: the head's.
WHAT IS NOT CLAIMED. hLE at any public part; the readings, O or Sd at any public part. That a stand is there: where
there is none all but `runs_at_fixed` say nothing. No member; outside this file `lensAt_head_runs` and `lensAt_lay_runs`
are called by Honest/K9/TotalLens.lean, `runs_at_fixed` by Honest/K9/LensAttPaid.lean, the two others by no line; the
assemblies do not call them. These are numbers of two other houses' runs, typed by us off the library's and the frame's
lemmas: those houses have not read them. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.LensLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun (lenStill)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf fsK6 fsJoin)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)

section
variable {α : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option K9L.Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {π : α → Option HTailF2 × Option (Array HFun)}
  {tmOf : ℕ × String → ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {lenOf : ℕ × String → α × Option K9L.Pub9 → ℕ}

/-- **Behind a yes of the batching's step every run that the order names has returned at a state that goes on from
what is fixed in front.** -/
theorem runs_at_fixed (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (k : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', k))
    (hOk : Ok (K9L.fixed9 φ s)) :
    ∀ o ∈ Lk.order, ∃ run n e c e₁, At Lk o run ∧ K9L.Fx9 φ Ok (K9L.fixed9 φ s) e ∧ run n e = .ok (c, e₁) := by
  have HF := K9L.fitsM_atS (K := Cb.Gl.E) φ A.runs.hφ Ok (LinkJoin.FullAt nU) p
  have hon := K9L.yes_onA p _ _ A.share.hb₁ ft s rs cols s' k hs
  obtain ⟨r, x, a, o, cls, _, _, ha, ho, hy⟩ := A.share.hb₁ ft s rs cols s' k hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, d12⟩ := K9L.drawnClean_ok _ _ _ _ _ _ _ ho
  obtain ⟨f1, g1⟩ := HF.atDraw s a o x ⟨hon, hOk⟩ ha ho
  obtain ⟨a₁, ha₁, hF⟩ := HF.lens s { a with owed := o.owed, L := o.L, F := o.F } (by rw [ha]; rfl)
  have hF' : a₁.F = o.F := hF
  obtain ⟨v, c, c', ⟨e, s₂, G, hg, _, _, _⟩, _, _⟩ := hy
  obtain ⟨ls, _, hran⟩ := gather_ran Lk.each Lk.hear Lk.order _ (c, e) hg
  have hI := ran_inv Lk.hear
    (fun t => K9L.Fx9 φ Ok (K9L.fixed9 φ s) t ∧ K9L.good9 t ∧
      ∃ b, Desc.K9.atS.get? t = some b ∧ b.F.LS.size = b.F.ns)
    Lk.order 0 _ ls e
    (fun o' ho' run hr n t z hIt hz => by
      obtain ⟨hf, hgd, b, hb, hsz⟩ := hIt
      obtain ⟨b₁, hb₁, kc, _, g', _, f', _, _⟩ :=
        A.runs.hpay o' (by rw [← (order_at A.seg).1]; exact ho') run hr (K9L.fixed9 φ s) n t b z.1 z.2 hf hgd hb hsz hz
      obtain ⟨_, _, _, _, k5, k6⟩ := K9L.core_parts kc
      exact ⟨f', g', b₁, hb₁, by rw [k5, k6]; exact hsz⟩)
    ⟨f1, g1, a₁, ha₁, by rw [hF']; exact d12⟩ hran
  intro o' ho'
  obtain ⟨_, _, run, n, t, z, hr, hIt, hz, _⟩ := forall₂_left hI.1 o' ho'
  exact ⟨run, n, t, z.1, z.2, hr, hIt.1, hz⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The head's kind's three numbers and its join's, at every stand.** -/
theorem headRuns_lens {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD) :
    (∀ on ∈ [("norm", 29), ("policy", 4), ("logits", 2)],
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24)
        (lenStill (fsK6 Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll on.1))
        on.2) ∧
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24)
        (lenStill (fsJoin Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll))
        1 := by
  have hm : 24 < 25 := by omega
  have hs : IM.subAt 24 = .head := by decide
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  have seg' : SegAt 24 .head Lk := hs ▸ seg
  obtain ⟨X₁, a2, SL⟩ := seal_head h O hs Lk p hlk seg drawB kp pC pD hC hD xx tlD hd
  have eX₁ : X₁ = Xl := Option.some.inj (a2.symm.trans e3)
  rw [eX₁] at SL
  obtain ⟨X₂, b2, TK⟩ := take_head h O hs Lk p hlk seg drawB kp pC pD hC tlD
  have eX₂ : X₂ = Xl := Option.some.inj (b2.symm.trans e3)
  rw [eX₂] at TK
  have hord : ∀ o, o ∈ First.orderOf .head → o ∈ Lk.order := fun o ho => by
    rw [(order_at seg').1]
    exact ho
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], (3, name) ∈ First.orderOf .head →
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24)
        (lenStill (fsK6 Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll name))
        (Kinds.Head.Law.lenK6 name) := by
    intro name hn ho κ s m En ds y cols s' x' z G St hOk
    obtain ⟨run, n, e, c, e₁, hAt, hFx, hyes⟩ := runs_at_fixed SL _ s s' _ cols _ St.step.2 hOk (3, name) (hord _ ho)
    obtain ⟨r, h0, hu⟩ := TK.ties.tK6 name hn run hAt
    obtain ⟨lf, hl, -⟩ := (Kinds.Head.Law.k6_still Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)
      (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) (phiAll tlD psiAll) _ kapAll TK.hkap TK.okK6 24 4 name r h0).forms _ n e c e₁
      hFx (hu n e c e₁ hyes)
    exact lenK6_eq _ _ _ _ name hl
  refine ⟨fun on hon => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
    rcases hon with rfl | rfl | rfl
    · exact k6 "norm" (List.mem_cons.2 (Or.inl rfl)) (by decide)
    · exact k6 "policy" (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))) (by decide)
    · exact k6 "logits" (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))) (by decide)
  · intro κ s m En ds y cols s' x' z G St hOk
    obtain ⟨run, n, e, c, e₁, hAt, hFx, hyes⟩ :=
      runs_at_fixed SL _ s s' _ cols _ St.step.2 hOk (3, "join") (hord _ (by decide))
    obtain ⟨lf, hl, -⟩ := (Kinds.Head.Law.join_marks Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)
      (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) (phiAll tlD psiAll) _ kapAll TK.hkap TK.okK6).forms _ n e c e₁ hFx
      (TK.ties.tJoin run hAt n e c e₁ hyes)
    exact lenJoin_eq _ _ _ _ hl

/-- **`LensAt` at the head's segment, from our public test's yes alone**, beside the head, an opening, the seat and the
readings. -/
theorem lensAt_head_runs (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD) :
    LensAt Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillHead Bs.G₀.W pC pD)
      (lenFillHead Bs.G₀.W pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) ww :=
  lensAt_head_look h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O Sd e3 hd hC hD
    (headRuns_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD).1
    (headRuns_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD).2

/-- **The feed-forward kind's run "front": its number at every stand.** -/
theorem frontRun_lens {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) (Xl : LinkH) (tlD : HTailF2) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) (pC pD : First.Look.P) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    NumAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) (K4Run.lenFront p4 (·.own)) (K9Asks.frontB Bs.G₀.W.layers.y g) := by
  intro κ s m En ds y cols s' x' z G St _
  have hm : 2 * g < 25 := by omega
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g) (by omega)
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb, show 14 * (2 * g) + 9 = 28 * g + 9 by omega] at hq
  have hB := bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1
  have hp := IM.plan_flat O h.laid.planOk
  obtain ⟨-, -, xm, -, -, hx, -, hl, hxg, -⟩ := IM.k4_of h.scope h.reads O g hg
  have ep : p4 = LPFK9.parOfMember xm := Option.some.inj (hk.symm.trans (LPFK9.k4ParAt_of_mem hx hl))
  obtain ⟨-, -, -, -, -, -, -, o₀, -, -, -, -, ho, -⟩ := layers_root h.scope h.reads O hp hg hq hB
  exact lenFront_eq p4 (by rw [ep]; rfl) (by rw [ep]; exact hxg) (o := o₀) ho
    (own_layout h.scope h.reads O hp hg hq hB tlD psiAll o₀ ho)

/-- **`LensAt` at a feed-forward segment, from our public test's yes alone**, beside the head, an opening, the seat and
the readings. -/
theorem lensAt_lay_runs (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD) :
    LensAt Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillLay p4 pC pD)
      (lenFillLay p4 pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) ww :=
  lensAt_lay_look h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O hg Sd e3 hd p4 hC hD
    (frontRun_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Xl tlD hk pC pD Lk p)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.runs_at_fixed
#print axioms ProofFile.Honest.K9.headRuns_lens
#print axioms ProofFile.Honest.K9.lensAt_head_runs
#print axioms ProofFile.Honest.K9.frontRun_lens
#print axioms ProofFile.Honest.K9.lensAt_lay_runs
