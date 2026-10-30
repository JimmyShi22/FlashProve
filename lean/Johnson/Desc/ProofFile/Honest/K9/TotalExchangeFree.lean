-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalExchangeFree.lean: THE FRAME's DEBT AT THE ITEM totalB (`ExchangeAtS` at
`SaidOk`), AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT THE BATCHING OF EACH OF THE 25 SEGMENTS: from K9's seat
Sd : `SeatedFree`, WHICH THE HEAD HANDS (`seated_at_head`, Honest/K9/AtHead.lean), public readings and the named debts
htst · hLE (· h4 at the twelve feed-forward segments). NO PREMISE NAMES THE PROVER's LIST OF HALVES BUT THROUGH THE
MEMBER's STEP (`BatStand` in h4 and in `GivesTotalB`; so does `ExchangeAtS` itself). IMPLICATIONS STILL: NO MEMBER: that
the thread stands in front of a batching at any run is shown by nobody: where it stands in front of none, these
sentences are idle. This file's text is made by program. No definition is made here (`frontS` is
Honest/K9/FrontBridge.lean's); no prover is made; no goal is stated.
  `reach_behind_seat`, `insideAt_behind_seat`: from Sd, at a stand: the state behind the batching's step is reached by
      the wrapped blocks one border on, without a mark; the part behind what runs behind it is "inside the members'
      ranges" · `bs_at_seat`: the thread's block at the batching's border is the seated batching (`batching_at_table`,
      Honest/K9/SeatTied.lean, in the thread's own letters: its own lemma: left to unification inside a call, it made
      Lean's unfolding run past the usual limit) · `exchange_totalB_head_seat`: general in l < 25, from `GivesTotalB` at
      `seatTab` and `frontS` · `exchange_totalB_att_seat`, `_24_seat`, `_lay_seat`: with hbeh as a premise
  **`exchange_totalB_att_free`**, **`_24_free`**, **`_lay_free`**   hbeh paid: at 2 g + 1, at 24, at 2 g
IS IT IDLE WHERE NO HALF STANDS AT K9's PLACE? These theorems do not ask that a half stands there. FOR WHAT THE
VERIFIER's STEP READS OF THE PLAY IT IS A THEOREM (`steps_noSide`, `moved_noSide`, Honest/K9/BatNoSide.lean); THE REST
BY READING (Honest/Frame.lean: `chainSteps`, `Step.tell`, `Step.hear`, `roundsOf`; the format's `Fmt.Entry`): where the
prover's list has no half at a member's place, the frame lays steps without a move; such a step tells no item and as
many absent tables as the entry has roots (K9's entry names none), and behind the challenge the run's state has heard it
and is else as it was. `batPart` too tells no item and no table and hands on what it was handed. The two differ in the
flag told, which `roundsOf`, and so the verifier's step, does not read. So the member's step is not barred by that lack.
THAT SAYS NOTHING OF A FILLING AT WHICH THE THREAD FAILS FOR ANOTHER MEMBER's SAKE: by the frame's house's letter
(a theorem of another house's on which places lack a half; the rest by reading, three readings agreeing, typed
by nobody): at its filling of that day the closing (K10) states elements and has no side, its step refuses, and WITH A
Said THAT TIES THE PROVER's STATE TO WHAT WAS PLAYED the pair in front holds of nothing behind number 12; "at SaidOk
alone … the argument does not run". These theorems stand at `SaidOk` alone and at a free prover: they are not shown
empty by it; joined at such a Said and that prover, all but the first segment's would be met for nothing.
WHAT IS NOT CLAIMED. htst (a condition on whoever lays the letter test) · hLE (a closed test on the public part;
paid under the head in Honest/K9/TotalExchangeLens.lean) · h4 (`K4Behind`: the feed-forward layers' run behind the batching returns
outside its share; paid in Honest/K9/ExchangeAtHead.lean) at anything HERE. Who opens the two items "worth" in front (the lookups' exchange). `Plays` and `AcceptedS` at the
batching: these do ask more (`plays_noSide`, Honest/K9/BatPlays.lean; `accepted_noSide`,
BatNoSide.lean: where no side stands there). Of the four items that the batching's row owes
(`bat_owes`, Honest/K9/ExchangeByKind.lean) totalB is one: the three pins have no law here. The
three are called by Honest/K9/TotalExchangeLens.lean. At the full size and the format's second hash
function alone. Nothing on any property.
GROUND: beneath this file lie files, of several groups of authors, that are no part of the sealed library.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalExchangeHead
import Johnson.Desc.ProofFile.Honest.K9.InsideBehind
import Johnson.Desc.ProofFile.Honest.K9.TotalExchangeSeat
import Johnson.Desc.ProofFile.Honest.K9.SeatTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The state behind the batching's step at a stand**: reached by the wrapped blocks one border on; and without a
mark. -/
theorem reach_behind_seat {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww :
          Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww) : ∀ κ s m En ds y cols s' x' z G,
    BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps l)
    κ s m En ds y cols s' x' z G → (∃ zp, Johnson.Desc.First.Walk.Tied.Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS
             Zp) (batchAt P5J.fullLinks P5J.At.ps l + 1) (zp, s')) ∧ s'.failed = none := by
  intro κ s m En ds y cols s' x' z G St
  obtain ⟨⟨zp, hw⟩, -⟩ := ProofFile.Honest.K8.wrap_and_mark_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl St
  have hblk : cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps l]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := (batching_at_table h hl Sd)
  have hS1 := saidNext_ok (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps l) _ (batching_at_table h hl Sd) κ s m En ds y cols St.thr.1 St.thr.2 St.fit
    St.step.1
  obtain ⟨⟨lst, -, hp⟩, -⟩ := St.step.1
  have hseen := (play_mid lst ds [] m y hp).2.2
  have hR : viewWordsBelowPrime ⟨roundsOf y.1, []⟩ = true := by
    have e : viewWordsBelowPrime ⟨y.2.seen, []⟩ = true := hS1
    rw [hseen] at e
    exact ((okRounds_append _ _).1 e).2
  obtain ⟨-, -, -, -, hn, -⟩ := behind_of_step Sd 0 s s' (roundsOf y.1) cols cols.length St.step.2
  have hc : ∀ c ∈ cols, ∀ a ∈ c.2.2, a < fieldPrimeWord := by
    rw [List.eq_nil_of_length_eq_zero hn]
    intro c hc
    cases hc
  have hY := stepped_yes St.step
  refine ⟨⟨zp, Johnson.Desc.First.Walk.Tied.Reach.succ
    (b := Sound.below (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))) hw
    (by rw [List.getElem?_map, hblk]; rfl)
    ⟨roundsOf y.1, cols, Sound.roundsFit_len _ _ ((Sound.step_ok_iff 0 _ s s' _ cols _).1 St.step.2).1,
      step_below St.step.2 hR hc⟩⟩,
    (Sd.k9Keeps_yes 0 s s' hY).mark⟩

/-- **"INSIDE THE MEMBERS' RANGES" BEHIND WHAT RUNS BEHIND THE BATCHING, AT A STAND**: at all 25 segments. -/
theorem insideAt_behind_seat {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww :
          Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww) (u : HTailF2) : ∀ κ s m En ds y cols
    s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
    P5J.At.ps l) κ s m En ds y cols s' x' z G → ∀ t a, Lk.runBehind s' = .ok t → Desc.K9.atS.get? t = some a →
    Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) a := by
  intro κ s m En ds y cols s' x' z G St t a hr ha
  obtain ⟨⟨zp, hw⟩, hu⟩ := reach_behind_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl Sd
    κ s m En ds y cols s' x' z G St
  obtain ⟨t₁, -, -, hy1⟩ := gathered_split p _ s x' z St.bat.gathered
  obtain ⟨a₁, h1, -, -⟩ := get_set z.1 z.2.1 { z.2.1 with F := G } hy1
  rw [← St.bat.state] at h1
  exact insideAt_runBehind Lk (insF_kept h hl Sd u) h1
    (insideAt_at_wrap h hl (i := 1) (by omega) hw hu h1) hr ha

/-- The thread's block at the batching's border is the seated batching: `batching_at_table` (Honest/K9/SeatTied.lean) in
the thread's own letters: stated, so that no call has to unfold the thread. -/
theorem bs_at_seat {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[batchAt P5J.At.links P5J.At.ps l]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) :=
  batching_at_table h hl Sd

/-- **THE FRAME's DEBT AT THE ITEM totalB, AT THE FRAME's OWN THREAD AT THE HEAD, GENERAL IN THE SEGMENT**: from K9's
seat at the thread and `GivesTotalB` at the witness's tables by seat and `frontS`: hfront and hmeans are paid. -/
theorem exchange_totalB_head_seat {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww :
          Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww) {xx : First.Look.Place} {tlD :
          HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) l = some (xx, tlD)) (hG : GivesTotalB Lk p (lettersHead h H Q test
          carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps l) (h.𝔇.N.group l) (fun v =>
          Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) (test l) (frontS h l xx tlD)) : ExchangeAtS
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk (batchAt P5J.At.links P5J.At.ps l)
    (Item.totalB l) := by
  obtain ⟨hlk, seg, -, kp⟩ := tied_of_seated h hl Sd
  exact exchange_totalB_seat (T := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread) Sd
    (bs_at_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl Sd) (h.𝔇.N.group l)
    (fun v => Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)
    (Desc.K9.rowsFit p.rows) (test l) (frontS h l xx tlD) (Item.totalB l) hG
    (fun wI a st v hall o ho =>
      ⟨head_hfront_order h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl (links_sub l hl)
        (fun o' ho' => (LinkJoin.items_is_order seg).symm ▸ ho') wI a st v hall o ho,
        fun _ => ProofFile.Honest.K8.worthTwo_of_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hd wI a st v hall⟩)
    (fun wI a st v hh => head_hmeans h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlk wI a st v fun ht => by
      obtain ⟨h1, h2⟩ := hh ht
      exact ⟨h1, by rw [LPFK9.hrw_at h l p kp]; exact h2⟩)

/-- **At an attention segment.** -/
theorem exchange_totalB_att_seat {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction
                Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g
                            < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd :
                                  SeatedFree cF Zp (2 * g + 1) kk Lk p ww) {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt
    (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false
    = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (htst : ∀ e, test (2 * g + 1) e = none →
    freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) (hLE : LensEqAsked Zp) (hbeh : ∀ κ
          s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) κ s m En ds y cols s' x' z G → ∀ t a, Lk.runBehind s' = .ok t →
          Desc.K9.atS.get? t = some a → Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group (2 * g + 1)) a) : ExchangeAtS
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk (batchAt P5J.At.links P5J.At.ps (2 * g +
    1)) (Item.totalB (2 * g + 1)) := by
  have hm : 2 * g + 1 < 25 := by omega
  exact exchange_totalB_head_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd hd
    (givesTotalB_att_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD (test (2 * g + 1))
    htst hLE hbeh)

/-- **At the head's segment.** -/
theorem exchange_totalB_24_seat {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction Z.pol
                Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {kk : ℕ} {Lk : Link S
                            ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt
    (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD :
    placeAt (P5J.At.X Zp) 24 true = some pD) (htst : ∀ e, test 24 e = none → freeSlotShare ww.2.2.filled e = none ∧
    k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) (hLE : LensEqAsked Zp) (hbeh : ∀ κ s m En ds y cols s' x' z G, BatStand Lk
          p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24) κ s m En
          ds y cols s' x' z G → ∀ t a, Lk.runBehind s' = .ok t → Desc.K9.atS.get? t = some a → Sound.InsideAt h.𝔇.cs
          h.𝔇.ms (h.𝔇.N.group 24) a) : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
    (batchAt P5J.At.links P5J.At.ps 24) (Item.totalB 24) := by
  have hm : 24 < 25 := by omega
  exact exchange_totalB_head_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd hd
    (givesTotalB_head_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD (test 24) htst hLE hbeh)

/-- **At a feed-forward segment.** -/
theorem exchange_totalB_lay_seat {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction
                Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g
                            < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd :
                                  SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g) false
    = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD) (share4 : S → Option String) (run4 : S → Except
    String S) (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4) (htst : ∀ e, test (2
    * g) e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧ share4 e = none)
    (hLE : LensEqAsked Zp) (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps (2 * g)) share4 run4) (hbeh : ∀ κ s m En ds y cols s' x' z G, BatStand Lk p
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g)) κ s m
    En ds y cols s' x' z G → ∀ t a, Lk.runBehind s' = .ok t → Desc.K9.atS.get? t = some a → Sound.InsideAt h.𝔇.cs
    h.𝔇.ms (h.𝔇.N.group (2 * g)) a) : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    SaidOk (batchAt P5J.At.links P5J.At.ps (2 * g)) (Item.totalB (2 * g)) := by
  have hm : 2 * g < 25 := by omega
  exact exchange_totalB_head_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd hd
    (givesTotalB_lay_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD (test (2 * g)) share4
    run4 hr4 htst hLE h4 hbeh)

/-- **The frame's debt at the item totalB at an attention segment, hbeh paid.** -/
theorem exchange_totalB_att_free {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction
                Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g
                            < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd :
                                  SeatedFree cF Zp (2 * g + 1) kk Lk p ww) {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt
    (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false
    = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (htst : ∀ e, test (2 * g + 1) e = none →
    freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) (hLE : LensEqAsked Zp) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk (batchAt P5J.At.links
    P5J.At.ps (2 * g + 1)) (Item.totalB (2 * g + 1)) := by
  have hm : 2 * g + 1 < 25 := by omega
  exact exchange_totalB_att_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD htst hLE
    (insideAt_behind_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd tlD)

/-- **At the head's segment, hbeh paid.** -/
theorem exchange_totalB_24_free {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction Z.pol
                Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {kk : ℕ} {Lk : Link S
                            ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt
    (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD :
    placeAt (P5J.At.X Zp) 24 true = some pD) (htst : ∀ e, test 24 e = none → freeSlotShare ww.2.2.filled e = none ∧
    k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) (hLE : LensEqAsked Zp) : ExchangeAtS (lettersHead h H Q test carryX item
          n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk (batchAt P5J.At.links P5J.At.ps 24) (Item.totalB 24) := by
  have hm : 24 < 25 := by omega
  exact exchange_totalB_24_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD htst hLE
    (insideAt_behind_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd tlD)

/-- **At a feed-forward segment, hbeh paid.** -/
theorem exchange_totalB_lay_free {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction
                Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g
                            < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd :
                                  SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g) false
    = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD) (share4 : S → Option String) (run4 : S → Except
    String S) (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4) (htst : ∀ e, test (2
    * g) e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧ share4 e = none)
    (hLE : LensEqAsked Zp) (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps (2 * g)) share4 run4) : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w).thread SaidOk (batchAt P5J.At.links P5J.At.ps (2 * g)) (Item.totalB (2 * g)) := by
  have hm : 2 * g < 25 := by omega
  exact exchange_totalB_lay_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD share4 run4 hr4 htst
    hLE h4 (insideAt_behind_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd tlD)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.reach_behind_seat
#print axioms ProofFile.Honest.K9.insideAt_behind_seat
#print axioms ProofFile.Honest.K9.bs_at_seat
#print axioms ProofFile.Honest.K9.exchange_totalB_head_seat
#print axioms ProofFile.Honest.K9.exchange_totalB_att_seat
#print axioms ProofFile.Honest.K9.exchange_totalB_24_seat
#print axioms ProofFile.Honest.K9.exchange_totalB_lay_seat
#print axioms ProofFile.Honest.K9.exchange_totalB_att_free
#print axioms ProofFile.Honest.K9.exchange_totalB_24_free
#print axioms ProofFile.Honest.K9.exchange_totalB_lay_free
