-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerTidy.lean: "THE STATEMENT IS TIDY" AT THE LEDGER OF A PROOF FILE's SHARED
CHAIN: ONE TEST WITH CODE BESIDE shapeK, HANDED ON BY THE KIND's OWN BLOCKS AT THE PIECES. Tidy
(Johnson/Desc/Means/Walk.lean: in order; the open rows' kinds; no sample row on a message that is
not sampled; sampled members) is kept along RUNS of the chain (shared_steps, shared_tidy,
Johnson/Desc/Tidy/Chains.lean; blocksOr_steps, Johnson/Desc/K14/Quiet.lean): in the form "a yes of
the block's STEP", for a sending keeps it only with the rounds' own test (K1's admitted sample rows
are on their message where the answers' lengths fit). The table of joints wants it as a fact on the
record inside the promise: it is spent by hcong at the two proximity tests (cong_nine, cong_ten,
Johnson/Desc/K14/Law/LedgerSay.lean) and by the last chain's door.

  step_carry, held_step   a step is carried along a reading of the record where the rounds are the
                  same and a yes of the one decision is a yes of the other; so from the wrap in
                  which a description's piece holds a block to the kind's own block.
  tidY, tidY_iff, tidY_order   **the test**: Means.tidy4B of the record's statement, at every
                  border; it says Tidy; Tidy gives InOrder.
  tidy_piece      a yes of a piece that holds, in the wrap, a block with the rounds and the decision
                  of one of the kind's eight keeps Tidy: by K13.Law.piece_step (a piece's yes is a
                  yes of its block's step) and blocksOr_steps.
  HandsAt.tidy    **HandsAt** (Johnson/Desc/K14/Law/LedgerFilled.lean) for a test with tidY laid
                  beside it.
  cong_nine_at, cong_ten_at   **hcong at the two proximity tests** from tidY and
                  membX at borders 9 | 10.
WHAT STAYS. hp: the kind's blocks' own tests on the plan pass (the description's planOk) · that the
block which the piece holds has the kind's block's ROUNDS (HandsAt's step has it in front;
share_filled asks it as h2r … h8r; at b.retype: by rfl) · OVER THE TWO PROXIMITY TESTS (9 to 10, 10
to 11): K12's files' (K12's blocks' steps keep Tidy: a named premise of shared_steps) · at the
chain's first record: Tidy.start · at the front and "LIN point": by the same two lemmas (not laid
here).
What is not claimed. No member. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerFilled
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.Tidy.Chains
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Means.TestsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Tidy InOrder tidy4B tidy4B_iff)
open VerifiableInference.Desc (Block OpenedColumn noDigest Wit)
open VerifiableInference.Desc.Ground (TidyStay groundQuiet_tidy admitOn_tidy)
open VerifiableInference.Desc.Sound

/-- A step is carried along a reading of the record, where the rounds are the same and a yes of the
one decision is a yes of the other. -/
theorem step_carry {S T Cl Cl' : Type} (g : T → S) (b' : Block T Cl') (b : Block S Cl)
    (hr : b'.rounds = b.rounds)
    (hd : ∀ t rs gs t', b'.decide t rs gs = .ok t' → b.decide (g t) rs gs = .ok (g t'))
    (ft : ℕ) (t : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (t' : T) (n : ℕ)
    (h : b'.step ft t rs cols = .ok (t', n)) : b.step ft (g t) rs cols = .ok (g t', n) := by
  unfold Block.step at h ⊢
  rw [hr] at h
  simp only [bind, Except.bind, pure, Except.pure] at h ⊢
  split at h
  · cases h
  · rename_i u1 e1
    try rw [e1]
    try simp only
    split at h
    · cases h
    · rename_i u2 e2
      try rw [e2]
      try simp only
      split at h
      · cases h
      · rename_i s' e3
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        rw [hd _ _ _ _ e3]

/-- From the wrap to the kind's own block. -/
theorem held_step {U Cl : Type} (c : Block St Cl) (b : Block St Unit) (hc : DecidesAs c b)
    (hr : c.rounds = b.rounds) (ft : ℕ) (t t' : U × St) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (n : ℕ) (h : (heldW (U := U) c).step ft t rs cols = .ok (t', n)) :
    b.step ft t.2 rs cols = .ok (t'.2, n) :=
  step_carry Prod.snd (heldW (U := U) c) b hr
    (fun t rs gs t' hd => by
      rw [← hc]
      exact (wrap_decide c t t' rs gs hd).1) ft t rs cols t' n h

/-- **The test**: the record's statement is tidy. -/
def tidY : ℕ → St → Bool := fun _ s => tidy4B s.st

theorem tidY_iff (k : ℕ) (s : St) : tidY k s = true ↔ Tidy s.st := tidy4B_iff

/-- What hcong spends. -/
theorem tidY_order (k : ℕ) (s : St) (h : tidY k s = true) : InOrder s.st :=
  ((tidY_iff k s).1 h).inOrder

variable {P₁ Cl Cells Tok : Type} {Fr : Frame}

/-- **A yes of a piece keeps it.** -/
theorem tidy_piece (Q : P14) (b : Block St Unit) (hb : b ∈ blocksOr Q) (hp : b.planOk = true)
    (c : Block St Cl) (hc : DecidesAs c b) (hr : c.rounds = b.rounds)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c)
    (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (j k : ℕ) (h : tidY j a.1.2 = true) :
    tidY k y.1.2 = true := by
  obtain ⟨rs, cols, n, hs⟩ := VerifiableInference.Desc.K13.Law.piece_step x hout
  rw [hx] at hs
  exact (tidY_iff k _).2 (blocksOr_steps groundQuiet_tidy admitOn_tidy Q b hb hp _ _ _ _ _ _
    (held_step c b hc hr _ _ _ _ _ _ hs) ((tidY_iff j _).1 h))

/-- **HandsAt for a test with tidY laid beside it.** -/
theorem HandsAt.tidy {on : ℕ → (P₁ × St) × Fr.E.Str → Prop} {X : ℕ → St → Bool} (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)
    (hX : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8] X)
    (hT : ∀ k a, on k a → tidY k a.1.2 = true) :
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8]
      fun k s => X k s && tidY k s := by
  have hB : blocksOr Q = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hbl]
    rfl
  refine ⟨fun i b hi hb c hc hr x hx a τ y ha hout => Bool.and_eq_true_iff.2
    ⟨hX.step i b hi hb c hc hr x hx a τ y ha hout, ?_⟩, fun s z h => ?_, fun s h => ?_⟩
  · have hm := List.mem_of_getElem? hb
    exact tidy_piece Q b (by rw [hB]; exact hm) (hp b hm) c hc hr x hx a τ y hout _ _ (hT _ a ha)
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact Bool.and_eq_true_iff.2 ⟨hX.zeta s z h1, h2⟩
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact Bool.and_eq_true_iff.2 ⟨hX.last s h1, h2⟩

/-! ## hcong at the two proximity tests, from what stands beside shapeK -/

section
open Cb Johnson.Pack
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence (membX membX_nine membX_ten memOf)

variable (cs : OnBytes.Codes) (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE) (ms : List Mem) (N : NumbersS)
  (P : Par) (n : ℕ) (num : Msg2 → ℕ)

/-- **hcong at the test on G_u**, at a record at which tidY 9 and membX 9 say
yes. -/
theorem cong_nine_at (sU : ℕ) (s : St) (hT : tidY 9 s = true) (hM : membX sU 9 s = true)
    (hnum : num .oU = 0) (xU xS : Mem) (hU : mem 0 = some xU) (hSp : mem (sU + 1) = some xS)
    (mU : xU ∈ ms) (mS : xS ∈ ms) (sitU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (sitS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
    (m m' : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg)
    (hsame : ∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] →
      ∀ x ∈ ms, SitsAt x (N.tenant μ).1 (N.tenant μ).2 → m' x = m x)
    (q : RowS) (hq : q ∈ [RowS.sample .oU, .recG, .loc, .foldU])
    (h : SayK cs mem rd P n num s q m) : SayK cs mem rd P n num s q m' := by
  obtain ⟨G, hG, hm⟩ := Option.map_eq_some_iff.1 (membX_nine sU s hM).1
  exact cong_nine cs mem rd ms N P n num s (tidY_order 9 s hT) G 0 (sU + 1) hG hm hnum xU xS hU hSp
    mU mS sitU sitS m m' hsame q hq h

/-- **hcong at the test on G_omega**, the like at border 10. -/
theorem cong_ten_at (sU : ℕ) (s : St) (hT : tidY 10 s = true) (hM : membX sU 10 s = true)
    (hnO : num .oOmega = sU) (hnS : num .oSp = sU + 1) (xO xS : Mem) (hO : mem sU = some xO)
    (hSp : mem (sU + 1) = some xS) (mO : xO ∈ ms) (mS : xS ∈ ms)
    (sitO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (sitS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
    (m m' : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg)
    (hsame : ∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] →
      ∀ x ∈ ms, SitsAt x (N.tenant μ).1 (N.tenant μ).2 → m' x = m x)
    (q : RowS) (hq : q ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega])
    (h : SayK cs mem rd P n num s q m) : SayK cs mem rd P n num s q m' := by
  obtain ⟨G, hG, hm⟩ := Option.map_eq_some_iff.1 (membX_ten sU s hM)
  exact cong_ten cs mem rd ms N P n num s (tidY_order 10 s hT) G sU (sU + 1) hG hm hnO hnS xO xS hO
    hSp mO mS sitO sitS m m' hsame q hq h

end

end Desc.K14.Law

#print axioms Desc.K14.Law.cong_nine_at
#print axioms Desc.K14.Law.cong_ten_at
#print axioms Desc.K14.Law.HandsAt.tidy
#print axioms Desc.K14.Law.step_carry
#print axioms Desc.K14.Law.held_step
#print axioms Desc.K14.Law.tidy_piece
