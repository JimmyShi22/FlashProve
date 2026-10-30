-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FrameCellsN.lean: `frame_cells` and `frame_cellsS`
(FrameCells.lean) with a narrower hypothesis on the item `carry m`. No definition.

`frame_cells` takes `hcarry`: the invariant's argument `carryX` passes over every sub-protocol of
the kind `frame`, from the state before a step that `keeps` admits to the state after it. It spends
that hypothesis at number 0, at the chain's end, at "laid" and at "cleared", and nowhere else: the
table `frameOk` admits no `carry m` at the 25 steps after a batching. Here `hcarry` is asked only at
the places where it is spent, and in the form of the conclusion: `RidesPastAt` at the item. In that
form a proof of it may use the invariant before the step. `carry_frame_paid`
(Thread/CarryFramePaid.lean) proves it.

  1  `rides_stillN`, `rides_clearedN`   `rides_still` and `rides_cleared` with the new hypothesis
  2  `frame_cellsN`, `frame_cellsSN`   `frame_cells` and `frame_cellsS` with the new hypothesis

The four proofs are those of FrameCells.lean, but for the case of the item `carry m` and three
short proofs that a place is not a step after a batching.

Hypotheses that stay.
  * `hfF`: the clause of the kind `frame` is `keepsFrame P5J.At.links P1L20.bearing`.
  * `hcarry`, in the new form.

Limits.
  * Nothing shows that the invariant holds at any state.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * That the item `pinW` still holds after a step is proved here through `ridesPastAt_pinW`
    (Honest/Thread/HeadPinW.lean), whose proof returns its hypothesis unchanged: at these parameters
    the decoder of the stored table is a constant, so the item says nothing about the stored table,
    nor about the committed weights: it is no step toward correctness of extraction.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item Stand standOf standAt shapeAt)
open VerifiableInference.Desc.LinkJoin (hearN rest9 here9)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open Johnson.Desc.First.Walk.Law (leftOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

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

/-- `rides_still` with the item `carry m` taken as it stands. -/
theorem rides_stillN {b : Nat}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s' = s ∧ s'.failed = none)
    (hcarry : ∀ m, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.carry m))
    {i : Item}
    (hi : i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨
      i = .wrow ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
      ∃ m q, i = .constr m q ∧ q ∈ parts4) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b i := by
  have hst : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st := fun s s' hK => by rw [(hk s s' hK).1]
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl, hq⟩
  · exact ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).2
  · exact ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b
  · exact ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' hK => by
      rw [(hk s s' hK).1]
      exact ⟨rfl, rfl, rfl⟩
  · exact ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hst
  · exact ridesPastAt_pileOne_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).1
  · exact ridesPastAt_pinV h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hst
  · exact ridesPastAt_wrow_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).1
  · exact hcarry m
  · exact ridesPastAt_pinKept h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m hst
  · exact ridesPastAt_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b m hq

/-- `rides_cleared` with the item `carry m` taken as it stands. -/
theorem rides_clearedN {b l : Nat} {p : Place} {take : Bool} (hp : P5J.At.ps[b]? = some p)
    (hl : p.link = some l)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      keepsCleared take s s')
    (hcarry : ∀ m, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.carry m))
    {i : Item}
    (hi : i = .unmarked ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
      (take = false ∧ (i = .pinW ∨ i = .pile ∨ i = .pinI)) ∨
      ∃ m q, i = .constr m q ∧ q ∈ parts4) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b i := by
  rcases hi with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨ht, rfl | rfl | rfl⟩ | ⟨m, q, rfl, hq⟩
  · exact ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).1
  · exact hcarry m
  · exact ridesPastAt_pinKept_cleared h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m hk
  · exact ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b
  · intro k s mm E s' ps v hA hK h0
    have K := hk s s' hK
    obtain ⟨eo, es⟩ := K.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
    have hsh := (form_shape hA.2.2.1).2
    have hsh' : shapeAt P5J.At.links (some p) s = true := by
      rw [← hp]
      exact hsh
    have er : s'.rows = s.rows := by
      rw [rows_between K.2.1, rows_in_segment hl hsh', eo]
    exact (pile_same { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
      mgBase es K.2.2.2.2.1 er mm.st.input.x.pub
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v).2 h0
  · exact ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => ((hk s s' hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht).2
  · exact ridesPastAt_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b m hq

end

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **Every combination that `frameOk` admits at a place of the kind `frame`.** `hcarry`: the item
`carry m` passes over the sub-protocol. It is asked at the places other than the steps after a
batching. -/
theorem frame_cellsN (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
        (Item.carry m)) :
    ∀ b p i, P5J.At.ps[b]? = some p → p.kind = KindName.frame → frameOk p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said b
        i := by
  intro b p i hp hkind hok
  have hKp : ∀ s s', kpBy f p s s' → keepsFrame P5J.At.links P1L20.bearing p s s' :=
    fun s s' hc => by
      have e := (kpBy_at f hkind s s').1 hc
      rw [hfF] at e
      exact e
  have hK : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      keepsFrame P5J.At.links P1L20.bearing p s s' := fun s s' hk =>
    hKp s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hp s s').1 hk)
  cases hl : p.link with
  | none =>
    have hS : ∀ s s',
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
        s' = s ∧ s'.failed = none :=
      fun s s' hk => (keepsFrame_out P5J.At.links P1L20.bearing hl s s').1 (hK s s' hk)
    have go : (i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨
        i = .wrow ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
        ∃ m q, i = .constr m q ∧ q ∈ parts4) →
        RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
          Said b i := fun hi => ridesPastAtS_of _ _
      (rides_stillN h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hS
        (hcarry b p hp hkind fun l e => by
          rw [hl] at e
          cases e) hi)
    by_cases h0 : p.piece = 0
    · rcases frameOk_front hl h0 hok with e | e | e | e
      · exact go (Or.inl e)
      · exact go (Or.inr (Or.inl e))
      · exact go (Or.inr (Or.inr (Or.inl e)))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))))))
    · rcases frameOk_seal hl h0 hok with e | e | e | e | e | e
      · exact go (Or.inl e)
      · exact go (Or.inr (Or.inl e))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))
  | some l =>
    by_cases h0 : p.piece = 0
    · have hS : ∀ s s',
          (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
          s' = s ∧ s'.failed = none :=
        fun s s' hk => (keepsFrame_laid P5J.At.links P1L20.bearing hl h0 s s').1 (hK s s' hk)
      have go : (i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨
          i = .wrow ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
          ∃ m q, i = .constr m q ∧ q ∈ parts4) →
          RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
            Said b i := fun hi => ridesPastAtS_of _ _
        (rides_stillN h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hS
          (hcarry b p hp hkind fun l' _ e => by
            rw [h0] at e
            omega) hi)
      rcases frameOk_laid hl h0 hok with e | e | e | e | e | e | e
      · exact go (Or.inl e)
      · exact go (Or.inr (Or.inl e))
      · exact go (Or.inr (Or.inr (Or.inl e)))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))))))
    · by_cases hb : p.piece = hearN P5J.At.links l + 2
      · exact rides_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w Said hp
          (fun s s' hc =>
            (keepsFrame_behind P5J.At.links P1L20.bearing hl hb s s').1 (hKp s s' hc))
          (frameOk_behind hl hb hok)
      · exact ridesPastAtS_of _ _ (rides_clearedN h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
          (take := P1L20.bearing l) hp hl
          (fun s s' hk =>
            (keepsFrame_cleared P5J.At.links P1L20.bearing hl h0 hb s s').1 (hK s s' hk))
          (hcarry b p hp hkind fun l' e => by
            obtain rfl := Option.some.inj (hl.symm.trans e)
            exact hb) (frameOk_cleared hl h0 hb hok))

/-- The same in the form that `head_hR_of_cellsF` (RideOkFrame.lean) asks at a place of the kind
`frame`. -/
theorem frame_cellsSN (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
        (Item.carry m)) :
    ∀ b p i, P5J.At.ps[b]? = some p → p.kind = KindName.frame → rideOkF p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said b
        i :=
  fun b p i hp hkind hok =>
    frame_cellsN h H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said hfF hcarry b p i hp hkind
      ((rideOkF_frame hkind i).symm.trans hok)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rides_stillN
#print axioms ProofFile.Honest.FirstThread.rides_clearedN
#print axioms ProofFile.Honest.FirstThread.frame_cellsN
#print axioms ProofFile.Honest.FirstThread.frame_cellsSN
