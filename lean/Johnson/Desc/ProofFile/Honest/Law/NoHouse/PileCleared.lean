-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/PileCleared.lean: what the table's row asks for after the
frame's step "cleared" of a segment of the first chain at the full size. At the 13 segments that
hand on a row (`P1L20.bearing l = true`) the row's `owes` holds the items `pile`, `pinW` and `pinI`.
The step puts one more row on the pile of pending rows, so `pile` does not pass over the step: its
statement after the step speaks of the new row too. The new row is the one of which the item `wo l`
speaks before the step, and `wo l` is open there. No definition.

  1  `rows_of_left`      where the open segment's sub-proof has left something for its row, the rows
     on the table are the pending rows
  2  `pile_grows`        at the library's meaning `mgAll`: `pile` and `wo m` at a state give `pile`
     at a state with the row of `wo m` added, if the two states have the same codes, message
     shapes and list of commitment trees
  3  `cleared_onePass`   along the full size's written lists: at each place "cleared", every item
     in the row's `owes` is `pile`, `pinW` or `pinI` and is open before the place; `wo l` is open
     there if the segment hands on a row; else `owes` is empty. The statement has no free variable.
     It is decided by the kernel's evaluation (`decide +kernel`), so it is counted apart
  4  `cleared_control`   the test can fail: it fails with `pile` struck from the three items
  5  `head_cleared_owes`   **the hypothesis `owes` of `noHouse_cleared` (Cleared.lean)**, at each of
     the 25 segments, for every `Rd`, `Kp` and `Said`
  6  `frame_owes_cleared_all`   so `PlaysS`, `BehindS` and `ExchangeS` at "cleared" without the
     hypothesis `owes` of `frame_owes_cleared` (FrameOwes.lean)

The library proves the opposite direction, `pile` after the step gives `wo` before it
(`pileGivesWo_of`, Johnson/Top/H0/Walk/FrameWo.lean). `rowAt_of_left` is from that file. The
transport of a row's statement between the two states is `rwBook_agree` (Thread/PileForward.lean) and
the library's `holds_congr`, as in `pile_older` and `wo_older` (Thread/WoForward.lean).

Limits.
  * Nothing shows that the invariant holds at any state, or that the step accepts.
  * Items 3 to 6: full size only. Items 5 and 6: under the library's `AtMgA` at the hash function
    `secondHashFunction`.
  * The item `pinW` of the row's `owes` is proved here through `head_pinW`
    (Honest/Thread/HeadPinW.lean), which holds by `rfl`: at these parameters the decoder of the
    stored table is a constant, so the item says nothing about the stored table, nor about the
    committed weights: it is no step toward correctness of extraction.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameOwes
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.FrameRides
import Johnson.Desc.ProofFile.Honest.Thread.OpenedKeepsR
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.RidesOk
import Johnson.Desc.K1.Law.HasRowAtLater
import Johnson.Top.H0.Walk.FrameWo
import Johnson.P1L20R.FrameSits
import Johnson.IMR.RootsWhole
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.ClearIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item Meaning start)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_pile mgAll_wo CellsQ)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.K13.Law (Holds holds_congr rwBook pileMasksC_iff)
open Johnson.Desc.First.Walk (leftLay)
open Johnson.Desc.First.Walk.Law (rowAt leftOf rowBy_some)
open Johnson.Desc.First.Walk.Tied (ClearedRec clearedGives rowAt_of_left)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The rows on the table -/

/-- Where something is left for the open segment's row, the rows on the table are the pending
rows. -/
theorem rows_of_left {s : S} {v : OnBytes.Model.WsForkOut} (h : leftOf s = some v) :
    s.rows = s.out.pending := by
  unfold S.rows
  cases hq : s.here with
  | mem a =>
    exfalso
    unfold leftOf leftLay leftHead at h
    rw [hq] at h
    cases h
  | _ => rfl

/-! ## 2 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s t : S}

/-- `pile` and `wo m` at `s` give `pile` at `t`, which has the row of `wo m` more. -/
theorem pile_grows (m : Nat) {r : OnBytes.TensorRow} (hrows : t.rows = s.rows ++ [r])
    (hrow : rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin s = some r) (hOn : pileMasksC s = true)
    (hc : t.st.codes = s.st.codes)
    (hx : (t.st.oracles[s.out.indexMasks]?).map (·.shape) =
      (s.st.oracles[s.out.indexMasks]?).map (·.shape))
    (hb : t.book = s.book) (z : P) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hp : (mgAll 𝔇 Mg).pile (z, s) y w) (hw : (mgAll 𝔇 Mg).wo m (z, s) y w) :
    (mgAll 𝔇 Mg).pile (z, t) y' w := by
  rw [mgAll_pile] at hp ⊢
  rw [mgAll_wo] at hw
  have hA := rwBook_agree 𝔇.arr 𝔇.mat13 (z, s) (z, t) w s.out.indexMasks hc hx
    (by show t.book.place[s.out.indexMasks]? = s.book.place[s.out.indexMasks]?; rw [hb])
    (fun q _ => by show t.book.trees[q.1]? = s.book.trees[q.1]?; rw [hb])
  have h1 : ∀ r' ∈ s.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, s) w) r' := hp
  show ∀ r' ∈ t.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, t) w) r'
  intro r' hm
  rw [hrows] at hm
  rcases List.mem_append.1 hm with hm | hm
  · exact (holds_congr _ ((pileMasksC_iff s).1 hOn r' hm) hA).2 (h1 r' hm)
  · obtain rfl := List.mem_singleton.1 hm
    exact (holds_congr OnBytes.Model.Reading.gl
      (VerifiableInference.Desc.K1.rowAt_onLedger hrow) hA).2 (hw r' hrow)

end

/-! ## 3 and 4 The written lists -/

set_option maxRecDepth 1000000 in
/-- Along the written lists, at each place "cleared". -/
theorem cleared_onePass :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      (List.range 25).all fun l => x.2 != P1L20.clearPlace l ||
        (((FirstRows.rowAt P5J.At.links x.2).owes.all fun i =>
            (i == Item.pile || i == Item.pinW || i == Item.pinI) && x.1.contains i) &&
          (if P1L20.bearing l then x.1.contains (Item.wo l)
            else (FirstRows.rowAt P5J.At.links x.2).owes.isEmpty))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with `pile` struck from the three items the same test fails. -/
theorem cleared_control :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      (List.range 25).all fun l => x.2 != P1L20.clearPlace l ||
        (((FirstRows.rowAt P5J.At.links x.2).owes.all fun i =>
            (i == Item.pinW || i == Item.pinI) && x.1.contains i) &&
          (if P1L20.bearing l then x.1.contains (Item.wo l)
            else (FirstRows.rowAt P5J.At.links x.2).owes.isEmpty))) = false := by
  decide +kernel

/-! ## 5 and 6 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

section
variable (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **What the table's row asks for holds after "cleared".** -/
theorem head_cleared_owes (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : Nat} (hl : l < 25) {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs)
    (hf : fs[l]? = some f) :
    ∀ k s m E t, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (P1L20.clearIx l) k s m E → f.clear s = .ok t →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Items
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
          (P1L20.clearIx l)).owes k t m E := by
  intro k s m E t hA e ds i hi
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, -, -, hp, -⟩ := P1L20.places_full hl
  have hp' : P5J.At.ps[P1L20.clearIx l]? = some (P1L20.clearPlace l) := hp
  rw [head_row_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp'] at hi
  -- the closed facts at this place
  have ht := FirstRows.onePass_at P5J.At.links
    (fun p O => (List.range 25).all fun l => p != P1L20.clearPlace l ||
      (((FirstRows.rowAt P5J.At.links p).owes.all fun i =>
          (i == Item.pile || i == Item.pinW || i == Item.pinI) && O.contains i) &&
        (if P1L20.bearing l then O.contains (Item.wo l)
          else (FirstRows.rowAt P5J.At.links p).owes.isEmpty)))
    P5J.At.ps (start P5J.At.links) cleared_onePass (P1L20.clearIx l) _ hp'
  have hc := List.all_eq_true.1 ht l (List.mem_range.2 hl)
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at hc
  obtain ⟨c1, c2⟩ := hc
  have ci := List.all_eq_true.1 c1 i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ci
  obtain ⟨csort, copen⟩ := ci
  have hopen : i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (P1L20.clearIx l) := (List.contains_iff_mem (α := Item)).1 copen
  have h0 := thr_item_at _ hA.1 hopen ds
  -- the step
  obtain ⟨Xl, counts, left, X', ecl, hX', hkk, hNCL, -, hflag⟩ := P1L20.clear_with_flag hfs hf
    (P1L20.plans_hold h.scope h.reads O (P1K2.flat_planOk O h.laid.planOk) hfs hl hf)
  rw [ecl] at e
  have hrec : ClearedRec Xl left Zp.p.X.layers.wsLay Zp.first.lin s t :=
    clearedGives Xl counts left _ _ s t e
  have hfail : t.failed = none := hrec.2.2.2.2.2.2.1.trans (form_shape hA.1.2.2.1).1
  have K := keepsCleared_of hrec hfail
  rcases csort with (rfl | rfl) | rfl
  · -- pile
    by_cases hbr : P1L20.bearing l = true
    · rw [if_pos hbr] at c2
      have hwo : Item.wo l ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
          (P1L20.clearIx l) := (List.contains_iff_mem (α := Item)).1 c2
      have hw := thr_item_at _ hA.1 hwo ds
      have hne : IM.subAt l ≠ VerifiableInference.Desc.First.ModelPart.attention := by
        unfold P1L20.bearing at hbr
        exact of_decide_eq_true hbr
      rcases hflag with ⟨g1, -⟩ | ⟨-, hv, hleft⟩
      · exact absurd (hkk ▸ g1) (P1L20.kind_not_att h.scope h.reads O hl hne hX')
      · obtain ⟨a1, -, -, a4, -, -, -, -, a9, -, -, a12, -, -, -, a16⟩ := hrec
        obtain ⟨q, hq, hpend⟩ := a16 hv
        obtain ⟨v, -, hv1, -⟩ := rowBy_some.1 hq
        have hrow : rowAt Zp.p.X.layers.wsLay (((Zp.p.built.links[l]?).map (·.NCL)).getD 0)
            Zp.first.lin s = some q := by
          rw [hX']
          show rowAt Zp.p.X.layers.wsLay X'.NCL Zp.first.lin s = some q
          rw [← hNCL]
          exact rowAt_of_left (hleft s) hq
        have hrows : t.rows = s.rows ++ [q] := by
          rw [rows_between a1, rows_of_left (hleft s v hv1), hpend]
        have hb : P1L20.clearIx l ≤ cF.blocksInOrder.length := by
          have e5 := (clearIx_bounds hl).2
          have e6 : cF.blocksInOrder.length = 358 := Meaning.Carry.flat_len h.scope h.reads O
          omega
        have hx : (t.st.oracles[s.out.indexMasks]?).map (·.shape) =
            (s.st.oracles[s.out.indexMasks]?).map (·.shape) := by
          have e7 := congrArg (Option.map fun o : OnBytes.Oracle => o.shape)
            (a12 s.out.indexMasks)
          simpa [Option.map_map, Function.comp_def] using e7
        exact pile_grows
          { h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } mgBase l hrows
          hrow (head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA.1) a9 hx a4
          m.st.input.x.pub
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) _ h0 hw
    · rw [if_neg hbr] at c2
      rw [List.isEmpty_iff.1 c2] at hi
      cases hi
  · -- pinW
    exact head_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ _ _ _
  · -- pinI
    exact ansJT_rows_older (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
      (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      (fun _ _ _ _ hq => (cleared_row K _).trans hq) h0

end

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- At the frame's step "cleared" of segment `l`, without a hypothesis on what the row asks for. -/
theorem frame_owes_cleared_all
    (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing) {l : Nat} (hl : l < 25)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said (P1L20.clearIx l) k m → Said (P1L20.clearIx l + 1) k m)
    (hb₀ : b₀ ≠ P1L20.clearIx l + 1)
    (hRd : ∀ v s t, t.atBetween = true → Rd (P1L20.clearIx l) v s →
      Rd (P1L20.clearIx l + 1) v t)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said (P1L20.clearIx l)) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, fr, bL, bB, bC, -, -, hf, -⟩ := hall l hl
  obtain ⟨-, Xl, counts, left, hcl, -⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  obtain ⟨blk, -, N⟩ := noHouse_cleared h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    (Said := Said) (fall := fun _ _ _ => some "") hl hfs hf noHalf said hb₀
    (fun v s t e hv => by
      rw [hcl] at e
      exact hRd v s t (clearedGives Xl counts left _ _ s t e).1 hv)
    (fun s t e h0 => (kpBy_at f (κ := KindName.frame) rfl s t).2 (by
      rw [hfF]
      exact kp_cleared h P5J.At.links hl hfs hf s t e h0))
    (head_cleared_owes h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w Said hl hfs hf)
    (fun _ _ _ _ _ hf' => nomatch hf') rides
  exact ⟨(noHouse_owes N).1, (noHouse_owes N).2.1, (noHouse_owes N).2.2.1⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rows_of_left
#print axioms ProofFile.Honest.FirstThread.pile_grows
#print axioms ProofFile.Honest.FirstThread.cleared_onePass
#print axioms ProofFile.Honest.FirstThread.cleared_control
#print axioms ProofFile.Honest.FirstThread.head_cleared_owes
#print axioms ProofFile.Honest.FirstThread.frame_owes_cleared_all
