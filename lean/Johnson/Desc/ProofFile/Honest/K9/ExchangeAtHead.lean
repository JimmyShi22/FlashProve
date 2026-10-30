-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ExchangeAtHead.lean: THE EXCHANGE AT K9's NUMBERS UNDER THE HYPOTHESIS `AtMgA`: the statements of Honest/K9/TotalExchangeLens.lean with the opening, K9's seat and
the public readings struck, since each is there under that hypothesis; and the join over K9's 75 numbers of Honest/K9/ExchangeByKind.lean.

  `run4Of`, `run4_lookup`, `run4_returns`   the feed-forward kind's run "free-slot": it returns where its test passes at a state that holds the kind's structure
  **`k4Behind_paid`**     the premise `K4Behind` at the share `k4FreeShare`, the kind's own named test, at the thread of the hypothesis: paid
  **`exchange_att_at_head`**, **`exchange_24_at_head`**, **`exchange_lay_at_head`**   `ExchangeAtS` at the item totalB at a batching
  **`exchange_k9_at_head`**   `ExchangeAtS` at every number of kind K9 and every item that the row there owes, but a pin that is open in front
  `rests_st`, `read_st`, `bat_st`    the batching leaves the statement
  **`k9_exchangeS_bat`**    `ExchangeS` whole at each batching, with the clauses of "keeps" `fHeadI`: totalB and the three pins

WHAT STAYS. One premise, htst, a condition on the letter test: at every value of the struck letters that meets their equations, where test l is silent at e, K9's share and the
smallness test's share are. At a feed-forward segment `share4` (TotalExchangeLens.lean) is paid, since at the same number of slots `k4Share_silent` gives it.

Limits. These are implications. That the thread stands in front of one of these members at any run is shown nowhere here; the heads of TotalExchangeLens.lean and ExchangeByKind.lean
say what is not claimed of the forms that they state, and that holds here. No property of a prover or a protocol is proved here.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalExchangeLens
import Johnson.Desc.ProofFile.Honest.K9.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K9.KeepsBehind
import Johnson.P5J.K03RidesDigLeft
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.K9.BehindValues
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.AtFull.Shape.BatchCellsAtt
import Johnson.Desc.First.Look.K3PlanLay
import Johnson.Desc.First.Look.K3PlanLettersLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (k8Share)

/-- The feed-forward kind's run "free-slot". -/
def run4Of (p4 : OnBytes.Desc.First.K4.Par) : S → Except String S := fun t =>
  (named "the part is not there" (OnBytes.Desc.First.K4.part? t)).bind fun q =>
    (OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn p4.hp q).map (OnBytes.Desc.First.K4.setPart t)

theorem run4_lookup (p4 : OnBytes.Desc.First.K4.Par) :
    (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some (run4Of p4) := rfl

/-- It returns where its test passes at a state that holds the kind's structure. -/
theorem run4_returns (p4 : OnBytes.Desc.First.K4.Par) {s : S} {a : First.LayOwn} {o : OnBytes.Model.Layer.Own}
    (hh : s.here = .lay a) (ho : a.own = some o)
    (hf : OnBytes.Desc.First.K4.freeSlotOk p4.hp.used o.wo.sFv a.F = true) : ∃ z, run4Of p4 s = .ok z := by
  have hq : OnBytes.Desc.First.K4.part? s = some (a, if s.noneWaits then none else s.rowsOwed, s.tokv) := by
    unfold OnBytes.Desc.First.K4.part?
    rw [hh]
  have hd : ∀ X' Y, OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn p4.hp (a, X', Y) = .ok (a, X', Y) := by
    intro X' Y
    unfold OnBytes.Desc.First.K4.freeSlot
    simp only [OnBytes.Desc.First.K4.seatOwn, ho]
    show (OnBytes.Desc.First.K4.test "K4.free-slot" (OnBytes.Desc.First.K4.freeSlotOk p4.hp.used o.wo.sFv a.F) >>=
      fun _ => pure (a, X', Y)) = _
    rw [hf]
    rfl
  have e : run4Of p4 s = (OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn p4.hp
      (a, if s.noneWaits then none else s.rowsOwed, s.tokv)).map (OnBytes.Desc.First.K4.setPart s) := by
    unfold run4Of
    rw [hq]
    rfl
  rw [e, hd]
  exact ⟨_, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The premise K4Behind at the kind's own named test, paid.** -/
theorem k4Behind_paid {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww)
    (p4 : OnBytes.Desc.First.K4.Par) :
    K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g))
      (k4FreeShare p4.hp.used) (run4Of p4) := by
  intro κ s m En ds y cols s' x' z G St _ hsh z₁ hz₁
  have hm : 2 * g < 25 := by omega
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb : batchAt P5J.At.links P5J.At.ps (2 * g) = 28 * g + 9 := by
    rw [batch_at.1 (2 * g) (by omega)]
    omega
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  have hB := bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1
  have hp := IM.plan_flat O h.laid.planOk
  obtain ⟨-, -, -, -, -, -, -, o₀, -, -, -, -, ho, -⟩ := VerifiableInference.Desc.LinkJoin.layers_root h.scope h.reads O hp hg hq hB
  have hown : s'.own? = s.own? := bat_keeps_reading h hm Sd S.own? rests_own set_own
    (k9Keeps_of_step Sd _ s s' _ cols _ St.step.2)
  rw [ho] at hown
  have ⟨a, hh, ha⟩ : ∃ a, s'.here = .lay a ∧ a.own = some o₀ := by
    unfold S.own? at hown
    cases e : s'.here with
    | lay a => rw [e] at hown; exact ⟨a, rfl, hown⟩
    | _ => rw [e] at hown; exact nomatch hown
  have hfree : OnBytes.Desc.First.K4.freeSlotOk p4.hp.used o₀.wo.sFv a.F = true := by
    unfold k4FreeShare at hsh
    rw [hh] at hsh
    simp only [ha] at hsh
    by_cases e : OnBytes.Desc.First.K4.freeSlotOk p4.hp.used o₀.wo.sFv a.F = true
    · exact e
    · rw [if_neg e] at hsh
      exact nomatch hsh
  obtain ⟨F, tl, hF, -, rfl⟩ := K9L.k8LsTail_ok _ _ hz₁
  have hF' : F = a.F := by
    have : s'.fork? = some a.F := by simp [S.fork?, hh]
    exact Option.some.inj (hF.symm.trans this)
  refine run4_returns p4 (a := { a with tl := { tl with lsTail := F.LS.extract tl.slotA tl.slotB } }) (o := o₀) ?_ ha hfree
  unfold S.putTl
  simp [hh]

/-- **At an attention segment.** -/
theorem exchange_att_at_head {g : ℕ} (hg : g < 12)
    (htst : ∀ (ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Bs : ProofFile.PureBase) (Xl : LinkH),
      Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some ww → ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
      Bs.G₀.built[2 * g + 1]? = some Xl → ∀ e, test (2 * g + 1) e = none →
        freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) (Item.totalB (2 * g + 1)) := by
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, ww, Sd⟩ := seated_at_head h (2 * g + 1) hl
  obtain ⟨xx, tlD, hd⟩ := P5J.k03_digAt_some h hl
  have hD := placeD_of_dig hd
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨A, Xl, hA, e3, -⟩ := LPFK9.attOwesC_g h O hg (sub_odd g hg) Lk p hlk seg drawB kp
  obtain ⟨Bp, -, -, q, hBp, -, -, hq, -⟩ := Johnson.AtFull.Shape.k3_planes_att h g hg
  obtain rfl : Bp = Bs := Except.ok.inj (hBp.symm.trans O.made)
  have eW : Bp.G₀.W = P5J.At.X Zp := O.W
  rw [eW] at hA hq
  exact exchange_totalB_att_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hq hD
    (htst ww Bp Xl Sd.tested O.made e3)

/-- **At the head's segment.** -/
theorem exchange_24_at_head
    (htst : ∀ (ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Bs : ProofFile.PureBase) (Xl : LinkH),
      Desc.K9.testsWhere Zp.p.X 24 0 = some ww → ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
      Bs.G₀.built[24]? = some Xl → ∀ e, test 24 e = none →
        freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (batchAt P5J.At.links P5J.At.ps 24) (Item.totalB 24) := by
  have hl : 24 < 25 := by omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, ww, Sd⟩ := seated_at_head h 24 hl
  obtain ⟨xx, tlD, hd⟩ := P5J.k03_digAt_some h hl
  have hD := placeD_of_dig hd
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨Xl, e3, -⟩ := LPFK9.headOwesC_24 h O rfl Lk p hlk seg drawB kp
  obtain ⟨Bp, -, -, q, hBp, -, -, hq, -⟩ := Johnson.AtFull.Shape.k3_planes_head h
  obtain rfl : Bp = Bs := Except.ok.inj (hBp.symm.trans O.made)
  have eW : Bp.G₀.W = P5J.At.X Zp := O.W
  rw [eW] at hq
  exact exchange_totalB_24_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hq hD
    (htst ww Bp Xl Sd.tested O.made e3)

/-- **At a feed-forward segment.** -/
theorem exchange_lay_at_head {g : ℕ} (hg : g < 12)
    (htst : ∀ (ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Bs : ProofFile.PureBase) (Xl : LinkH),
      Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some ww → ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
      Bs.G₀.built[2 * g]? = some Xl → ∀ e, test (2 * g) e = none →
        freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (batchAt P5J.At.links P5J.At.ps (2 * g)) (Item.totalB (2 * g)) := by
  have hl : 2 * g < 25 := by omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, ww, Sd⟩ := seated_at_head h (2 * g) hl
  obtain ⟨xx, tlD, hd⟩ := P5J.k03_digAt_some h hl
  have hD := placeD_of_dig hd
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨p4, Xl, hk, hX, -⟩ := LPFK9.layersOwesC_whole h O (2 * g) hl (sub_even g hg) Lk p hlk seg drawB kp
  have e3 : Bs.G₀.built[2 * g]? = some Xl := by
    rw [Array.getElem?_toList] at hX
    exact hX
  have hC : ∃ pC, placeAt (P5J.At.X Zp) (2 * g) false = some pC := by
    have hn : 2 * g < 24 := by omega
    obtain ⟨xl, -, hx, -⟩ := First.Look.layAt_scope h.scope h.reads h.pubOne hn (by omega)
    exact ⟨_, H2K5.Door.placeAt_of (First.Look.layAt_letters h.scope h.reads h.pubOne hg hx).1⟩
  obtain ⟨pC, hC⟩ := hC
  obtain ⟨-, -, xm, -, -, hx, -, hlnk, -, -, hG, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  have ep : p4 = LPFK9.parOfMember xm := Option.some.inj (hk.symm.trans (LPFK9.k4ParAt_of_mem hx hlnk))
  have hu : p4.hp.used = ww.2.2.filled := by
    have eW : Bs.G₀.W = P5J.At.X Zp := O.W
    rw [eW] at hG
    rw [ep]
    exact filled_lay h hg Sd.tested hG
  exact exchange_totalB_lay_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD
    (k4FreeShare p4.hp.used) (run4Of p4) (run4_lookup p4)
    (fun e he => by
      obtain ⟨a1, a2⟩ := htst ww Bs Xl Sd.tested O.made e3 e he
      exact ⟨a1, a2, by rw [hu]; exact k4Share_silent _ e a1⟩)
    (k4Behind_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd p4)

/-- **At every number of kind K9 and every item that the row there owes.** -/
theorem exchange_k9_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (htst : ∀ (l : ℕ) (ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Bs : ProofFile.PureBase) (Xl : LinkH), l < 25 →
      Desc.K9.testsWhere Zp.p.X l 0 = some ww → ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
      Bs.G₀.built[l]? = some Xl → ∀ e, test l e = none →
        freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K9 →
      ∀ j : VerifiableInference.Desc.First.Item,
      j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  refine exchange_owes_of_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid fun l hl => ?_
  by_cases h24 : l = 24
  · subst h24
    exact exchange_24_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun ww Bs Xl a b c => htst 24 ww Bs Xl hl a b c
  · by_cases hev : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      exact exchange_lay_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega)
        fun ww Bs Xl a b c => htst _ ww Bs Xl hl a b c
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      exact exchange_att_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega)
        fun ww Bs Xl a b c => htst _ ww Bs Xl hl a b c

/-- The statement is among what every run leaves. -/
theorem rests_st : VerifiableInference.Desc.LinkJoin.FieldRests (·.st : S → _) where
  tl s t := by
    unfold S.putTl
    split <;> first | rfl | (split <;> rfl)
  fork s G := by
    unfold S.putFork
    split <;> first | rfl | (split <;> rfl)
  wrote _ _ _ _ hw := by obtain ⟨_, rfl⟩ := hw; rfl
  head _ _ _ _ := rfl

/-- What K9's lens reads of the statement is the statement. -/
theorem read_st {t : S} {q : Desc.K9.Part} (hq : Desc.K9.atS.get? t = some q) : q.d.st = t.st := by
  obtain ⟨L, -, h1⟩ := Option.bind_eq_some_iff.1 (show (t.link?).bind _ = some q from hq)
  obtain ⟨F, -, h2⟩ := Option.bind_eq_some_iff.1 (show (t.fork?).bind _ = some q from h1)
  obtain ⟨tl, -, h3⟩ := Option.bind_eq_some_iff.1 (show (t.tl?).bind _ = some q from h2)
  obtain ⟨used, -, h4⟩ := Option.bind_eq_some_iff.1 (show (Desc.K9.usedOf t).bind _ = some q from h3)
  obtain rfl := Option.some.inj (show some _ = some q from h4)
  rfl

include h in
/-- The batching's clause of "keeps" leaves the statement. -/
theorem bat_st {l kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (hl : l < 25) (Sd : SeatedFree cF Zp l kk Lk p ww) {s s' : S}
    (K : K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s') : s'.st = s.st :=
  K.left (fun u v => v.st = u.st) (fun _ => rfl) (fun _ _ _ a b => b.trans a)
    (fun u a q ha hd => by
      show q.d.st = u.st
      rw [hd]
      exact read_st ha)
    fun o ho run hr n u z hz => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
      exact rests_at_head h hl Sd (·.st) rests_st j o run hj hr n u z hz

/-- **`ExchangeS` whole at the batching of each segment: totalB and the three pins.** -/
theorem k9_exchangeS_bat (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
    (f : KindName → Place → TS → TS → Prop)
    (hf : ∀ pl s s', k9KeepsAt cF Zp pl s s' → formsBehind h.𝔇.pubD pl s' → f KindName.K9 pl s s')
    (hf' : ∀ pl s s', pl.kind = KindName.K9 → f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (htst : ∀ (l : ℕ) (ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Bs : ProofFile.PureBase) (Xl : LinkH), l < 25 →
      Desc.K9.testsWhere Zp.p.X l 0 = some ww → ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
      Bs.G₀.built[l]? = some Xl → ∀ e, test l e = none →
        freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (l : ℕ) (hl : l < 25) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy f) w).thread Said (14 * l + IM.nAt l + 2) := by
  have eb : batchAt P5J.At.links P5J.At.ps l = 14 * l + IM.nAt l + 2 := batch_number l hl
  refine (exchangeS_iff _ _).2 fun i hi => ?_
  have hj : i ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 2)).owes := hi
  rw [bat_owes l hl] at hj
  rcases List.mem_cons.1 hj with rfl | hpin
  · have hB : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy f) w).thread SaidOk
        (batchAt P5J.At.links P5J.At.ps l) (Item.totalB l) := by
      by_cases h24 : l = 24
      · subst h24
        exact exchange_24_at_head h H Q test carryX item n₁ n₂ 339 Vd _ _ w
          fun ww Bs Xl a b c => htst 24 ww Bs Xl hl a b c
      · by_cases hev : l % 2 = 0
        · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
          exact exchange_lay_at_head h H Q test carryX item n₁ n₂ 339 Vd _ _ w (by omega)
            fun ww Bs Xl a b c => htst _ ww Bs Xl hl a b c
        · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
          exact exchange_att_at_head h H Q test carryX item n₁ n₂ 339 Vd _ _ w (by omega)
            fun ww Bs Xl a b c => htst _ ww Bs Xl hl a b c
    rw [eb] at hB
    exact exchangeAtS_mono _ hSaid hB
  · have hop := head_pins_open h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy f) w hl hpin
    rw [eb] at hop
    obtain ⟨Lk, p, ww, Qc, bE, bS, Sd, -⟩ := seats_at_head h hl
    have hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy f) w).thread.keeps (14 * l + IM.nAt l + 2) s s' → s'.st = s.st := by
      intro s s' hK
      have hblk : (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
          (kpBy f) w).thread.bs[14 * l + IM.nAt l + 2]? =
          some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := Sd.batching
      have hk := kind_bat_at h hl Sd.batching
      have hfk := (head_keeps_kind h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w hblk hk s s').1 hK
      exact bat_st h hl Sd (bat_of_k9KeepsAt Sd (hf' _ s s' hk hfk))
    have hBh := (k9_behindS h H Q test carryX item n₁ n₂ Vd ν st R f w Said hf l hl).1
    have h3 : i ∈ [Item.pin l 0, Item.pin l 1, Item.pin l 2] := hpin
    rcases List.mem_cons.1 h3 with rfl | h3
    · exact exchangeAtS_pin h H Q test carryX item n₁ n₂ 339 Vd _ _ w l 0 Said hst hop hBh
    rcases List.mem_cons.1 h3 with rfl | h3
    · exact exchangeAtS_pin h H Q test carryX item n₁ n₂ 339 Vd _ _ w l 1 Said hst hop hBh
    rcases List.mem_cons.1 h3 with rfl | h3
    · exact exchangeAtS_pin h H Q test carryX item n₁ n₂ 339 Vd _ _ w l 2 Said hst hop hBh
    exact absurd h3 List.not_mem_nil

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rests_st
#print axioms ProofFile.Honest.K9.read_st
#print axioms ProofFile.Honest.K9.bat_st
#print axioms ProofFile.Honest.K9.k9_exchangeS_bat
#print axioms ProofFile.Honest.K9.run4_lookup
#print axioms ProofFile.Honest.K9.run4_returns
#print axioms ProofFile.Honest.K9.k4Behind_paid
#print axioms ProofFile.Honest.K9.exchange_att_at_head
#print axioms ProofFile.Honest.K9.exchange_24_at_head
#print axioms ProofFile.Honest.K9.exchange_lay_at_head
#print axioms ProofFile.Honest.K9.exchange_k9_at_head
