-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ShapeAll.lean: kind K13, the members' batching: THE KIND's WHOLE SHAPE AND
ITS ONE STEP: the shape `Sh` (ShapeDefs.lean of this folder), what stands at the chain's end
(ShapeSim.lean) and the mark of failure; ONE FUNCTION WITH CODE ON IT (`gK`): ONE TEST (`guardK`)
AND ONE UPDATE (`updK`), which read no round and no element of a field. And: wherever `gK` returns
at the shape of a state, the joined sub-protocol (`atM3`) returns from that state on all rounds that
pass `roundsFit` at `battRounds P`; and wherever the sub-protocol returns from a state without a
mark, on whatever rounds, `gK` returns the shape of the state behind. Definitions with code, and
statements with their proofs. Local to this kind.
Main names:
  `takeL`, `takeMasksInto_takeL`, `takeMasks_takeL`: the numbers of the mask entries that n takes
    hand out, of the ledger alone.
  `ledgerSh`, `freshSh`: the index masks' ledger, and the slots that will be taken, off the shape.
  `ShK`, `shK`: the whole shape; a state's. `updSh`, `endK`, `guardK`, `updK`, `gK`: **the step.**
  `atM3_returns`: **THE LAW ON "RETURNS"**: the nine tests on the shape accept, the rounds pass the
    step's own test: the sub-protocol returns, and the shape behind is the update's.
  `gK_step`: **a return of the sub-protocol carries the step of the shape.**
  `gK_ready`: where the step of the shape returns, the nine tests accept and no mark stands.
  `gK_returns`: so the sub-protocol returns on all rounds that pass the step's own test on rounds.

What is not claimed. THE FIELD `decide` ALONE IS TREATED: not `Block.step` (its test on the
columns), not the sub-protocol's test on the plan (`planOk`), not that the words of a sent or
sampled element are below the field's prime. "The step's own test on rounds" means `roundsFit` at
`battRounds P`: that the rounds which `atM3 P` declares are `battRounds P` is stated in no file of
this folder. That `roundsFit` at `battRounds P` reads no value is not stated either. That any state
of a run passes the test. That the shape at a state of a run hangs on no sent value and on no coin.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeSim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law
open Desc.Plain (DState)

/-- The numbers of the entries that n takes hand out. -/
def takeL : Nat → Ledger → List Nat
  | 0, _ => []
  | n + 1, l => nextOf l :: takeL n (taken l)

variable {L : Type}

/-- What the loop of the taking hands out, of the ledger alone. -/
theorem takeMasksInto_takeL (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ)
    (t : List ℕ × DState L) (l : Ledger), (d.st.oracles[o]?).bind (·.ledger) = some l →
    takeMasksInto o n d acc = some t → t.1 = acc.toList ++ takeL n l
  | 0, d, acc, t, l, _, h => by
    rw [← Option.some.inj h]
    exact (List.append_nil _).symm
  | n + 1, d, acc, t, l, hl, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      rw [hm] at h
      obtain ⟨l', a1, a2, a3⟩ := takeMask_num (i := q.1) (d' := q.2) hm
      obtain rfl : l = l' := Option.some.inj (hl.symm.trans a1)
      rw [takeMasksInto_takeL o n q.2 (acc.push q.1) t (taken l) a3 h, Array.toList_push, a2,
        List.append_assoc]
      rfl

/-- The same, as the text calls it. -/
theorem takeMasks_takeL {d : DState L} {o n : ℕ} {t : List ℕ × DState L} {l : Ledger}
    (hl : (d.st.oracles[o]?).bind (·.ledger) = some l) (h : takeMasksP d o n = some t) :
    t.1 = takeL n l := by
  have e := takeMasksInto_takeL o n d #[] t l hl h
  rw [e]
  rfl

/-- The index masks' ledger, off the shape. -/
def ledgerSh (h : Sh) : Option Ledger := (h.msgs[h.index]?).bind (·.ledger)

/-- At a state's shape it is the ledger of the state's index masks' message. -/
theorem ledgerSh_shOf (s : S) :
    ledgerSh (shOf s) = (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) := by
  unfold ledgerSh shOf
  simp only [Array.getElem?_map]
  cases s.st.oracles[s.out.indexMasks]? <;> rfl

/-- The slots that n takes will hand out, off the shape. -/
def freshSh (n : Nat) (h : Sh) : List Slot :=
  (((ledgerSh h).map (takeL n)).getD []).map fun i => ⟨h.index, i⟩

/-- **The kind's whole shape**: the shape; what stands at the chain's end; a mark of failure. -/
abbrev ShK : Type := Sh × Option EndSh × Bool

/-- A state's. -/
def shK (s : S) : ShK := (shOf s, endOf s, s.failed.isSome)

/-- The shape behind: the chain has come to its end; no count of rows waits; the index masks' ledger
is that of 1 + 2 kCol more takes. -/
def updSh (P : Where) (h : Sh) : Sh :=
  { h with
    atFin := false, quiet := true
    msgs := h.msgs.modify h.index (MsgSh.takes (Batt.masksOf P.lin.kCol)) }

/-- The step of ShapeStep.lean is this update under the nine tests. -/
theorem stepSh_eq (P : Where) (h : Sh) :
    stepSh P h = if readySh P h then some (updSh P h) else none := rfl

/-- What stands at the chain's end behind: W's message as the plan has it; no message sent yet; the
claim's row's shape. -/
def endK (P : Where) (h : Sh) : EndSh :=
  ⟨(linMessageW P.lin).getD #[], #[], some (noId, noId, noId, none,
    claimSh P.lin.kCol h.pile (freshSh (Batt.masksOf P.lin.kCol) h))⟩

/-- **THE ONE TEST**: no mark of failure; the nine tests on the shape. -/
def guardK (P : Where) (a : ShK) : Bool := !a.2.2 && readySh P a.1

/-- **THE ONE UPDATE.** -/
def updK (P : Where) (a : ShK) : ShK := (updSh P a.1, some (endK P a.1), false)

/-- **THE STEP OF THE SHAPE.** -/
def gK (P : Where) (a : ShK) : Except String ShK :=
  if guardK P a then .ok (updK P a) else .error "K13: a guard on the shape"

variable {Cl : Type}

/-- **THE LAW ON "RETURNS"**: where the nine tests on the state's shape accept, the joined
sub-protocol returns on all rounds that pass the step's own test on rounds, whatever elements they
hold; and the shape behind is the update's: the shape; what stands at the chain's end; the mark of
failure as it was. No premise is on a value that the rounds hold: rs is free under the test on
rounds. -/
theorem atM3_returns {P : Where} {s : S} (hsh : readySh P (shOf s) = true) (rs : List Fmt.RoundView)
    (hr : roundsFit (battRounds P) rs = true) (gs : List (List (Nat × List UInt64))) :
    ∃ s', (atM3 (Cl := Cl) P).decide s (rs.map noDigest) gs = .ok s' ∧
      shOf s' = updSh P (shOf s) ∧ endOf s' = some (endK P (shOf s)) ∧ s'.failed = s.failed := by
  obtain ⟨f, t₀, msg₀, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ready_of_shape hsh
  obtain ⟨row₀, h⟩ := atM3_accepts_fit (Cl := Cl) a1 a2 a3 a4 a5 a6 a7 a8 a9 rs hr gs
  refine ⟨_, h, ?_, ?_, atM3_failed h⟩
  · have q1 := shape_step h
    rw [stepSh_eq, if_pos hsh] at q1
    exact (Option.some.inj q1).symm
  · obtain ⟨t, msg, x, hd, o, b1, b2, b3, b4, b5⟩ := atM3_return_row h
    rw [b5, endOf_behind s t.2.st msg b3 b4]
    obtain ⟨l, hl⟩ : ∃ l, (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l := by
      have e : Batt.masksOf P.lin.kCol = 2 * P.lin.kCol + 1 := by
        unfold Batt.masksOf
        omega
      rw [e] at b1
      obtain ⟨y, l, hy, hl, -, -⟩ := (leftAtC_iff _ _ _).1 (takeMasks_left b1)
      refine ⟨l, ?_⟩
      have hy' : s.st.oracles[s.out.indexMasks]? = some y := hy
      rw [hy']
      exact hl
    have e1 : t.1 = takeL (Batt.masksOf P.lin.kCol) l := takeMasks_takeL (d := dOf s) hl b1
    have e2 : freshSh (Batt.masksOf P.lin.kCol) (shOf s) =
        t.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot) := by
      unfold freshSh
      rw [ledgerSh_shOf, hl, e1]
      rfl
    unfold endK
    rw [e2, b2]
    rfl

/-- What the one test says of a state. -/
theorem guardK_shK (P : Where) (s : S) :
    guardK P (shK s) = true ↔ s.failed = none ∧ readySh P (shOf s) = true := by
  unfold guardK shK
  cases s.failed <;> simp

/-- **A return of the sub-protocol, from a state without a mark, carries the step of the shape.** -/
theorem gK_step {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') (h0 : s.failed = none) :
    gK P (shK s) = .ok (shK s') := by
  have hsh := shape_of_return h
  unfold gK
  rw [if_pos ((guardK_shK P s).2 ⟨h0, hsh⟩)]
  have q1 := shape_step h
  rw [stepSh_eq, if_pos hsh] at q1
  have q2 : s'.failed = none := by rw [atM3_failed h, h0]
  obtain ⟨t, msg, x, hd, o, b1, b2, b3, b4, b5⟩ := atM3_return_row h
  have q3 : endOf s' = some (endK P (shOf s)) := by
    rw [b5, endOf_behind s t.2.st msg b3 b4]
    obtain ⟨l, hl⟩ : ∃ l, (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l := by
      have e : Batt.masksOf P.lin.kCol = 2 * P.lin.kCol + 1 := by
        unfold Batt.masksOf
        omega
      rw [e] at b1
      obtain ⟨y, l, hy, hl, -, -⟩ := (leftAtC_iff _ _ _).1 (takeMasks_left b1)
      refine ⟨l, ?_⟩
      have hy' : s.st.oracles[s.out.indexMasks]? = some y := hy
      rw [hy']
      exact hl
    have e1 : t.1 = takeL (Batt.masksOf P.lin.kCol) l := takeMasks_takeL (d := dOf s) hl b1
    have e2 : freshSh (Batt.masksOf P.lin.kCol) (shOf s) =
        t.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot) := by
      unfold freshSh
      rw [ledgerSh_shOf, hl, e1]
      rfl
    unfold endK
    rw [e2, b2]
    rfl
  show Except.ok (updSh P (shOf s), some (endK P (shOf s)), false) =
    Except.ok (shOf s', endOf s', s'.failed.isSome)
  rw [← Option.some.inj q1, q3, q2]
  rfl

/-- Where the step of the shape returns, the nine tests accept and no mark stands; and it returns
the update. -/
theorem gK_ready {P : Where} {s : S} {t : ShK} (h : gK P (shK s) = .ok t) :
    readySh P (shOf s) = true ∧ s.failed = none ∧ t = updK P (shK s) := by
  unfold gK at h
  by_cases hg : guardK P (shK s) = true
  · rw [if_pos hg] at h
    exact ⟨((guardK_shK P s).1 hg).2, ((guardK_shK P s).1 hg).1, (Except.ok.inj h).symm⟩
  · rw [if_neg hg] at h
    cases h

/-- **Where the step of the shape returns, the sub-protocol returns on all rounds that pass the
step's own test on rounds.** -/
theorem gK_returns {P : Where} {s : S} {t : ShK} (h : gK P (shK s) = .ok t) (rs : List Fmt.RoundView)
    (hr : roundsFit (battRounds P) rs = true) (gs : List (List (Nat × List UInt64))) :
    ∃ s', (atM3 (Cl := Cl) P).decide s (rs.map noDigest) gs = .ok s' :=
  (atM3_returns (gK_ready h).1 rs hr gs).imp fun _ q => q.1

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_takeL
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_takeL
#print axioms VerifiableInference.Desc.K13.Honest.ledgerSh_shOf
#print axioms VerifiableInference.Desc.K13.Honest.stepSh_eq
#print axioms VerifiableInference.Desc.K13.Honest.atM3_returns
#print axioms VerifiableInference.Desc.K13.Honest.guardK_shK
#print axioms VerifiableInference.Desc.K13.Honest.gK_step
#print axioms VerifiableInference.Desc.K13.Honest.gK_ready
#print axioms VerifiableInference.Desc.K13.Honest.gK_returns
