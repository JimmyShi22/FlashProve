-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerApart.lean: FOUR OF THE SIX TESTS ON THE PLAN's NUMBERS THAT
each_rides_at_K_apart (Johnson/Desc/K14/Law/LedgerRidesApart.lean) ASKS: W's and the index masks'
components are apart (apartAt, Johnson/Desc/Sound/BordersSharedFill.lean) from the message that
block 9 | block 10 lays (o_u's | o_sp's). The other two, at o_omega's component, are
hap_nine | hap_ten (Johnson/Desc/Sound/SeamNumbersSh.lean).

  apart_of_ne      the test says yes where the block lays one message, and the component's number
                   and seat are not that message's.
  tenant_ge        a tenant at which a member of the plan's list sits lies in a tree from its
                   sending's first tree on (the user's hnew, all, htree).
  apart_four_at_K  the four tests, at the user's own letters.
THE SEATS' HALF IS PAID from binders of ledger_at_cap (hw hi ht mU sU mS sS hnew2 all2 htree2 hnew5
all5 htree5) with hb2 : base ≤ base2: W's and the masks' trees lie below the point's base, o_u's and
o_sp's from base2 on.
THE NUMBERS' HALF IS LEFT, AS FOUR INEQUALITIES ON THE PLAN's LETTER arr (nWU nWS nIU nIS): it gives
W's and the masks' tenants numbers other than o_u's and o_sp's: like SeamNumbersSh.lean's harr
(the three tenants have three numbers), for the slot's own two. No term for arr lies on the ground.
What is not claimed. The four inequalities. No instance. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRidesOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open Johnson.Pack
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.K1 (sampledAt shapesOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- The test's yes, where the block lays one message. -/
theorem apart_of_ne (N : NumbersS) (arr : ℕ → ℕ → ℕ) (k : ℕ) (m : Msg2) (c : Comp)
    (hl : laysAtS true k = [.msg m])
    (hn : numOfComp N arr c ≠ some (arr (N.tenant m).1 (N.tenant m).2))
    (hs : seatOfComp N c ≠ some (N.tenant m)) : apartAt N arr true k c = true := by
  unfold apartAt
  rw [hl]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [Bool.and_eq_true, bne_iff_ne, bne_iff_ne]
  exact ⟨hn, hs⟩

/-- A tenant at which a member of the plan's list sits lies from its sending's first tree on. -/
theorem tenant_ge (ms new : List Mem) {L : ℕ} (memK : Fin L → Mem) (P : Fin L → Prop)
    (b T j₀ t₀ : ℕ) (x : Mem) (hx : x ∈ ms) (hs : SitsAt x j₀ t₀)
    (hnew : ∀ x ∈ ms, SitsAt x j₀ t₀ → x ∈ new) (all : ∀ x ∈ new, ∃ k, P k ∧ memK k = x)
    (htree : ∀ k, ∃ j, ((memK k).1.seat (memK k).2).1 = b + j ∧ j < T) : b ≤ j₀ := by
  obtain ⟨k, _, rfl⟩ := all x (hnew x hx hs)
  obtain ⟨j, e, _⟩ := htree k
  have e' : ((memK k).1.seat (memK k).2).1 = j₀ := congrArg Prod.fst hs
  omega

/-- **The four tests**, at the user's own letters. -/
theorem apart_four_at_K {P₁ Cl Cells Tok : Type} {Fr : Frame} (ms : List Mem) (N : NumbersS)
    (Q : P14) (arr : ℕ → ℕ → ℕ) (sentU : Array OracleNotice) (base : Nat) (N₁ : Numbers)
    (Ns : NumbersS) (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (c2 c4 c5 c7 : Block St Cl)
    (x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (base2 : ℕ) (d21 d22 : RDT)
    (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er2 : Err (uLT (ckP .two) [d21, d22])) (base4 : ℕ) (d4 : RDT)
    (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 d52 : RDT)
    (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er5 : Err (uLT (ckP .two) [d51, d52])) (base7 : ℕ) (d7 : RDT)
    (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er7 : Err (uLT (ckP .two) [d7]))
    (ht : Tiled (pc2 c2 base2 d21 d22 ex2 er2) [x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51
      d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
    (xU : Mem) (mU : xU ∈ ms) (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem) (new2 : List Mem)
    (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
    (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
    (hnew2 : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new2)
    (memK5 : Fin (shapesOf (parO Q)).length → Mem) (new5 : List Mem)
    (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
    (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
    (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 →
      x ∈ new5)
    (xS : Mem) (mS : xS ∈ ms) (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
    (eN : N = tiedNumbers N₁ Ns) (hb2 : base ≤ base2)
    (nWU : arr N.w.1 N.w.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2)
    (nWS : arr N.w.1 N.w.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2)
    (nIU : arr N.index.1 N.index.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2)
    (nIS : arr N.index.1 N.index.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2) :
    apartAt N arr true 9 .w = true ∧ apartAt N arr true 9 .index = true ∧
      apartAt N arr true 10 .w = true ∧ apartAt N arr true 10 .index = true := by
  have gU : base2 ≤ (N.tenant .oU).1 :=
    tenant_ge ms new2 memK2 _ base2 _ _ _ xU mU sU hnew2 all2 htree2
  have gS : base5 ≤ (N.tenant .oSp).1 :=
    tenant_ge ms new5 memK5 _ base5 _ _ _ xS mS sS (hnew5 .oSp (.inr rfl)) all5 htree5
  have g5 : base2 ≤ base5 := tiled_base_le _ _ ht (pc2 c5 base5 d51 d52 ex5 er5) (by simp)
  have eW : N.w = N₁.w := by rw [eN]; rfl
  have eI : N.index = N₁.index := by rw [eN]; rfl
  have l9 : laysAtS true 9 = [.msg .oU] := by decide
  have l10 : laysAtS true 10 = [.msg .oSp] := by decide
  refine ⟨apart_of_ne N arr 9 .oU .w l9 (fun e => nWU (Option.some.inj e)) fun e => ?_,
    apart_of_ne N arr 9 .oU .index l9 (fun e => nIU (Option.some.inj e)) fun e => ?_,
    apart_of_ne N arr 10 .oSp .w l10 (fun e => nWS (Option.some.inj e)) fun e => ?_,
    apart_of_ne N arr 10 .oSp .index l10 (fun e => nIS (Option.some.inj e)) fun e => ?_⟩
  · have e' : N.w.1 = (N.tenant .oU).1 := congrArg Prod.fst (Option.some.inj e)
    rw [eW] at e'
    omega
  · have e' : N.index.1 = (N.tenant .oU).1 := congrArg Prod.fst (Option.some.inj e)
    rw [eI] at e'
    omega
  · have e' : N.w.1 = (N.tenant .oSp).1 := congrArg Prod.fst (Option.some.inj e)
    rw [eW] at e'
    omega
  · have e' : N.index.1 = (N.tenant .oSp).1 := congrArg Prod.fst (Option.some.inj e)
    rw [eI] at e'
    omega

end Desc.K14.Law

#print axioms Desc.K14.Law.apart_of_ne
#print axioms Desc.K14.Law.tenant_ge
#print axioms Desc.K14.Law.apart_four_at_K
