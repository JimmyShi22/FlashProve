-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersB.lean: the two sentences on ledgers WITH CODE, and K1's and K13's
blocks of the first chain at "every ledger is in order".

  nextNo m k, nextNo_eq   where the search begins in front of take k, IN CLOSED FORM: a test at a
                    large k walks no k steps (takenNo_eq, OnBytes/Iop/LedgerPlaces.lean).
  ledgerAtB st o k, ledgerAtB_iff   LedgerAt st o k as a Bool: at a NAMED number of takes.
  ledgersFitB st, ledgersFitB_iff   LedgersFit st as a Bool: each ledger at the number that what is
                    left fixes.
  FitStays; sendAtS_ledgersFit, commitAtS_ledgersFit, firstAtS_ledgersFit, atM3_ledgersFit,
  atM4_ledgersFit   in order in front of a yes, in order behind: by ledgersKept
                    (Johnson/Desc/K13/Law/LedgersKept.lean) and the blocks' laws.

The layer's own test, which has no Mathlib beneath it, is ledgersFitC
(Johnson/Desc/K13/PubK13.lean); its tie to LedgersFit: Johnson/Desc/K13/Law/LedgersC.lean.

What is not claimed. The number of takes at any border. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.K13.Law.LedgersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Keeps (Decides)

/-! ## 1 With code -/

/-- Where the search begins in front of take k, in closed form: 0, then the number behind the free
entry number k - 1, which is entry (k - 1) / m of row (k - 1) % m. -/
def nextNo (m k : ℕ) : ℕ :=
  if k = 0 then 0 else (k - 1) % m + 2 ^ Fmt.Places.logUp m * ((k - 1) / m) + 1

/-- **The ledger of message o is that of k takes since it was made**, with code. -/
def ledgerAtB (st : Statement) (o k : ℕ) : Bool :=
  match st.oracles[o]? with
  | none => false
  | some x =>
    match x.ledger with
    | none => false
    | some l =>
      decide (0 < x.shape.maskRows) && decide (1 ≤ x.shape.answers) &&
        decide (l.rows = x.shape.maskRows) && decide (l.logRows = ceilLog2 x.shape.maskRows) &&
        decide (l.left + k = Send.freeMaskEntries x.shape.maskRows
          (st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers) &&
        decide (l.next = nextNo x.shape.maskRows k)

/-- **Every ledger in the statement is in order**, with code: each at the number of takes that what
is left fixes. -/
def ledgersFitB (st : Statement) : Bool :=
  (List.range st.oracles.size).all fun o =>
    match st.oracles[o]? with
    | none => true
    | some x =>
      match x.ledger with
      | none => true
      | some l =>
        ledgerAtB st o (Send.freeMaskEntries x.shape.maskRows
          (st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers - l.left)

theorem nextNo_eq {m : ℕ} (hm : 0 < m) : ∀ k, nextNo m k = nextAt m k
  | 0 => rfl
  | k + 1 => by
    show nextNo m (k + 1) = takenNo m k + 1
    unfold nextNo
    rw [if_neg (Nat.succ_ne_zero k), takenNo_eq hm k, Nat.add_sub_cancel]
    rfl

theorem ledgerAtB_iff (st : Statement) (o k : ℕ) : ledgerAtB st o k = true ↔ LedgerAt st o k := by
  constructor
  · intro h
    unfold ledgerAtB at h
    cases hx : st.oracles[o]? with
    | none => simp [hx] at h
    | some x =>
      cases hl : x.ledger with
      | none => simp [hx, hl] at h
      | some l =>
        simp only [hx, hl, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨hm, ha⟩, hr⟩, hq⟩, hleft⟩, hn⟩ := h
        exact ⟨x, l, hx, hl, hm, ha, hr, hq, hleft, by rw [hn, nextNo_eq hm]⟩
  · rintro ⟨x, l, hx, hl, hm, ha, hr, hq, hleft, hn⟩
    unfold ledgerAtB
    simp only [hx, hl, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨hm, ha⟩, hr⟩, hq⟩, hleft⟩, by rw [hn, nextNo_eq hm]⟩

theorem ledgersFitB_iff (st : Statement) : ledgersFitB st = true ↔ LedgersFit st := by
  constructor
  · intro h o x hx hs
    have ho : o < st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    have h1 := List.all_eq_true.1 h o (List.mem_range.2 ho)
    cases hl : x.ledger with
    | none =>
      rw [hl] at hs
      cases hs
    | some l =>
      simp only [hx, hl] at h1
      exact ⟨_, (ledgerAtB_iff st o _).1 h1⟩
  · intro h
    unfold ledgersFitB
    rw [List.all_eq_true]
    intro o _
    cases hx : st.oracles[o]? with
    | none => rfl
    | some x =>
      cases hl : x.ledger with
      | none => simp only [hl]
      | some l =>
        obtain ⟨k, hk⟩ := h o x hx (by rw [hl]; rfl)
        simp only [hl]
        have hk' := hk
        obtain ⟨x', l', hx', hl', -, -, -, -, hleft, -⟩ := hk'
        obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
        obtain rfl : l = l' := Option.some.inj (hl.symm.trans hl')
        rw [← hleft, Nat.add_sub_cancel_left]
        exact (ledgerAtB_iff st o k).2 hk

/-! ## 2 K1's and K13's blocks of the first chain keep "every ledger is in order" -/

variable {Cl : Type}

/-- In order in front, in order behind. -/
def FitStays (T T' : Statement) : Prop := LedgersFit T → LedgersFit T'

theorem sendAtS_ledgersFit (P : K1.Par) :
    Decides (By FitStays fun s : S => s.st) (K1.sendAtS (Cl := Cl) P) :=
  K1.Rel.sendAtS_keeps ledgersKept P

theorem commitAtS_ledgersFit (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides (By FitStays fun s : S => s.st) (K1.commitAtS (Cl := Cl) P link moment arrays) :=
  K1.Rel.commitAtS_keeps ledgersKept P link moment arrays

theorem firstAtS_ledgersFit (q : Params.First) (gp : GPar) :
    Decides (By FitStays fun s : S => s.st) (K1.firstSegmentOpening (Cl := Cl) q gp) :=
  K1.Rel.firstAtS_keeps ledgersKept q gp

theorem atM3_ledgersFit (p : K13.Where) :
    Decides (By FitStays fun s : S => s.st) (K13.atM3 (Cl := Cl) p) :=
  K13.atM3_keeps (VerifiableInference.Desc.Ground.GroundKeeps.quiet ledgersKept) p

theorem atM4_ledgersFit (p : K13.Where) (commitW : Block S Cl)
    (hW : Decides (By FitStays fun s : S => s.st) commitW) :
    Decides (By FitStays fun s : S => s.st) (K13.atM4 p commitW) :=
  K13.atM4_keeps (VerifiableInference.Desc.Ground.GroundKeeps.quiet ledgersKept) p commitW hW

end VerifiableInference.Desc.K13.Law
