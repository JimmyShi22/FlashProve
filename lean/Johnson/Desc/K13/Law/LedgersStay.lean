-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersStay.lean: AT THE BLOCKS THAT TAKE NO MASK ENTRY THE LEDGERS' NUMBERS
STAY.

  LedStay T T'     nothing is taken: the code table stays, and of every message that is there its
                   shape and its ledger's four numbers (LedSame,
                   Johnson/Desc/K13/Law/LedgerOk.lean).
  LedStay.at       so the ledger of every message is that of the SAME number of takes (LedgerAt).
  LedStay.left     what is left, and where the search begins, stay.
  sendAtS_ledStay, commitAtS_ledStay, firstAtS_ledStay   K1's three blocks: a sending leaves every
                   older message whole (K1.decideSend_kept); a new group and the joinings turn no
                   ledger.
  firstEnd_ledStay   the first chain's last block.

NOT THROUGH GroundKeeps | GroundQuiet: both structures have a field for a take at any message, so
"the numbers stay" is no such relation: each block goes by its own text's read-out
(K1.commitOwn_ok, K1.firstOwn_ok: Johnson/Desc/K1/Law/Around.lean).

What is not claimed. Of W's commitment's second half (the own group, the joinings, the row on W) and
of kind K13's batching, which takes entries. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.LedgersKept
import Johnson.Desc.K1.Law.Around
import Johnson.Desc.K1.Law.KeptAtRecord
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.Tidy.Still
import Johnson.Desc.K13.FirstEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Keeps (Decides)

/-! ## 1 The four numbers stay -/

theorem LedSame.trans {x y z : OnBytes.Oracle} (h : LedSame x y) (k : LedSame y z) :
    LedSame x z := by
  refine ⟨k.1.trans h.1, fun l hl => ?_⟩
  obtain ⟨l₁, h1, a1, a2, a3, a4⟩ := h.2 l hl
  obtain ⟨l₂, h2, b1, b2, b3, b4⟩ := k.2 l₁ h1
  exact ⟨l₂, h2, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

/-- **Nothing is taken**: the code table stays, and of every message that is there its shape and its
ledger's four numbers. -/
def LedStay (T T' : Statement) : Prop :=
  T'.codes = T.codes ∧
    ∀ (i : ℕ) (x : OnBytes.Oracle), T.oracles[i]? = some x →
      ∃ x' : OnBytes.Oracle, T'.oracles[i]? = some x' ∧ LedSame x x'

theorem LedStay.refl (T : Statement) : LedStay T T := ⟨rfl, fun _ x h => ⟨x, h, LedSame.refl x⟩⟩

theorem LedStay.trans {A B C : Statement} (h : LedStay A B) (k : LedStay B C) : LedStay A C := by
  refine ⟨k.1.trans h.1, fun i x hx => ?_⟩
  obtain ⟨y, hy, s1⟩ := h.2 i x hx
  obtain ⟨z, hz, s2⟩ := k.2 i y hy
  exact ⟨z, hz, s1.trans s2⟩

/-- **So the ledger of every message is that of the same number of takes.** -/
theorem LedStay.at {T T' : Statement} (h : LedStay T T') {o k : ℕ} (hk : LedgerAt T o k) :
    LedgerAt T' o k := ledgerAt_same h.1 (h.2 o) hk

/-- What is left stays. -/
theorem LedStay.left {T T' : Statement} (h : LedStay T T') {o : ℕ} {l : Ledger}
    (hl : (T.oracles[o]?).bind (·.ledger) = some l) :
    ∃ l', (T'.oracles[o]?).bind (·.ledger) = some l' ∧ l'.left = l.left ∧ l'.next = l.next := by
  obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨x', hx', -, hL⟩ := h.2 o x hx
  obtain ⟨l', hl', e1, e2, -, -⟩ := hL l hxl
  exact ⟨l', by rw [hx']; exact hl', e2, e1⟩

variable {L Cl : Type}

/-- Where every older message is left whole. -/
theorem ledStay_kept {d d' : DState L} (h : K1.Kept d d') : LedStay d.st d'.st := by
  refine ⟨h.1, fun i x hx => ⟨x, ?_, LedSame.refl x⟩⟩
  rw [h.2.2 i (Array.getElem?_eq_some_iff.1 hx).1]
  exact hx

theorem joinP_ledStay (d d' : DState L) (g j : Nat) (kept : Bool)
    (h : joinP d g j kept = some d') : LedStay d.st d'.st := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨rfl, fun i x hx => ?_⟩
      show ∃ x', (d.st.oracles.modify j fun x => { x with groups := x.groups ++ [g] })[i]? =
        some x' ∧ LedSame x x'
      rw [Array.getElem?_modify]
      by_cases e : j = i
      · rw [if_pos e, hx]
        exact ⟨_, rfl, rfl, fun l hl => ⟨l, hl, rfl, rfl, rfl, rfl⟩⟩
      · rw [if_neg e]
        exact ⟨x, hx, LedSame.refl x⟩
  · cases h

theorem newGroupP_ledStay (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : LedStay d.st d'.st := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, fun _ x hx => ⟨x, hx, LedSame.refl x⟩⟩
  · cases h

theorem joinAll_ledStay (p : GPar) (g : Nat) (l : List (ReqMessage × Nat)) :
    ∀ (d d' : DState L), First.Send.joinAll Desc.Plain.groundG p g l d = some d' →
      LedStay d.st d'.st := by
  induction l with
  | nil =>
    intro d d' h
    cases h
    exact LedStay.refl _
  | cons x l ih =>
    intro d d' h
    cases hj : (Desc.Plain.groundG (L := L)).join p d g x.2 (decide (0 < x.1.life)) with
    | none => simp [First.Send.joinAll, hj] at h
    | some e =>
      simp only [First.Send.joinAll, hj, Option.bind_some] at h
      exact (joinP_ledStay d e g x.2 _ hj).trans (ih e d' h)

theorem joinOwnP_ledStay (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L)
    (h : joinOwnP Desc.Plain.groundG p d f sent ids = some y) : LedStay d.st y.2.st := by
  unfold joinOwnP at h
  split at h
  · cases hj : First.Send.joinAll Desc.Plain.groundG p f.group (zipT sent ids.toList) d with
    | none => simp [hj] at h
    | some e =>
      simp only [hj, Option.map_some, Option.some.injEq] at h
      subst h
      exact joinAll_ledStay _ _ _ _ _ hj
  · cases h

/-! ## 2 K1's three blocks take nothing -/

/-- **W's sending.** -/
theorem sendAtS_ledStay (P : K1.Par) :
    Decides (By LedStay fun s : S => s.st) (K1.sendAtS (Cl := Cl) P) := by
  intro s rs gs s' h
  obtain ⟨a, -, c⟩ := K1.sendAtS_kept P s s' rs gs h
  refine ⟨a, fun i x hx => ⟨x, ?_, LedSame.refl x⟩⟩
  rw [c i (Array.getElem?_eq_some_iff.1 hx).1]
  exact hx

/-- **A segment's later moment.** -/
theorem commitAtS_ledStay (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides (By LedStay fun s : S => s.st) (K1.commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  unfold K1.commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    obtain ⟨ids, d₁, f', h2, h3⟩ := K1.commitOwn_ok P link moment arrays _ y _ gs hy
    show LedStay s.st (((K1.laid s y.held.w).putLink y.held.L).putFork y.held.F).st
    rw [K1.Rel.putFork_st, K1.Rel.putLink_st]
    exact (ledStay_kept (K1.decideSend_kept P _ _ d₁ rs ids h2)).trans
      (joinOwnP_ledStay _ _ _ _ _ _ h3)
  · cases h

/-- **The first segment's opening**: a new group, the sending, the joinings. -/
theorem firstAtS_ledStay (q : Params.First) (gp : GPar) :
    Decides (By LedStay fun s : S => s.st) (K1.firstSegmentOpening (Cl := Cl) q gp) := by
  intro s rs gs s' h
  unfold K1.firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := Keeps.ebind_ok h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := Keeps.ebind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨g, d₁, ids, d₂, h3, h4, f₁, own, mine, f₂, h5⟩ := K1.firstOwn_ok _ _ _ _ _ _ _ h2
  show LedStay s.st d'.st
  exact ((newGroupP_ledStay _ _ _ _ _ h3).trans
    (ledStay_kept (K1.decideSend_kept _ _ d₁ d₂ rs ids h4))).trans
    (joinOwnP_ledStay _ _ _ _ _ _ h5)

/-- **The first chain's last block** returns the state that it was given. -/
theorem firstEnd_ledStay (piece : Nat) (front : List (Block S Cl)) :
    Decides (By LedStay fun s : S => s.st) (First.firstEnd piece front) := by
  intro s rs gs s' h
  have e : s' = s := Keeps.chainEnd_same 1 piece true _ First.endAsks h
  rw [e]
  exact LedStay.refl _

end VerifiableInference.Desc.K13.Law
