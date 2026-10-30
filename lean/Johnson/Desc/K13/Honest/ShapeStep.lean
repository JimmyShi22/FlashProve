-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ShapeStep.lean: kind K13, the members' batching: THE SHAPE's OWN STEP AT THE
JOINED SUB-PROTOCOL (`atM3`): a function with code on the shape `Sh` (ShapeDefs.lean of this folder;
its projection `shOf`: Shape.lean), which reads no round and no element of a field; and: WHERE THE
SUB-PROTOCOL RETURNS, FROM s TO s', THE SHAPE's STEP RETURNS, FROM THE SHAPE OF s TO THE SHAPE OF
s'. Definitions with code, and statements with their proofs. Local to this kind.
Main names:
  `stepSh`: **the step**: where the nine tests accept: the chain has come to its end; no count of
    rows waits; the ledger of the index masks' message is that of 1 + 2 kCol more takes.
  `atM3_return_form`: where the sub-protocol returns, the state behind is `withClaim` at what the
    verifier's taking returns.
  `takeMasksInto_msgs`, `takeMasks_msgs`: what the taking does to the messages' shapes and ledgers.
  `shape_step`: **the statement.**

What is not claimed. THE SHAPE `Sh` HOLDS NOTHING OF THE CLAIM THAT IS LAID, which the sub-protocol
behind W's commitment reads (its column point's length, its mask form's slots): a shape that serves
both places has more fields. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law
open Desc.Plain (DState)

/-- A message's shape and ledger, behind n takes. -/
def MsgSh.takes (n : Nat) (m : MsgSh) : MsgSh := { m with ledger := m.ledger.map (taken^[n]) }

/-- **The shape's own step.** -/
def stepSh (P : Where) (h : Sh) : Option Sh :=
  if readySh P h then
    some { h with
      atFin := false, quiet := true
      msgs := h.msgs.modify h.index (MsgSh.takes (Batt.masksOf P.lin.kCol)) }
  else none

/-- The messages' shapes and ledgers. -/
def msgsOf (st : Statement) : Array MsgSh := st.oracles.map fun x => ⟨x.shape, x.ledger⟩

variable {L : Type}

/-- What the loop of the taking does to the messages' shapes and ledgers. -/
theorem takeMasksInto_msgs (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ)
    (t : List ℕ × DState L), takeMasksInto o n d acc = some t →
    msgsOf t.2.st = (msgsOf d.st).modify o (MsgSh.takes n)
  | 0, d, acc, t, h => by
    have e : t = (acc.toList, d) := (Option.some.inj h).symm
    rw [e]
    apply Array.ext_getElem?
    intro j
    rw [Array.getElem?_modify]
    split
    · cases (msgsOf d.st)[j]? with
      | none => rfl
      | some m =>
        show some m = some (MsgSh.takes 0 m)
        cases m with
        | mk sh l => cases l <;> rfl
    · rfl
  | n + 1, d, acc, t, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      rw [hm] at h
      obtain ⟨x, l, hx, hl, -, -, hd⟩ := takeMask_left (i := q.1) (d' := q.2) hm
      rw [takeMasksInto_msgs o n q.2 (acc.push q.1) t h, hd]
      apply Array.ext_getElem?
      intro j
      rw [Array.getElem?_modify, Array.getElem?_modify]
      unfold msgsOf layLedger
      simp only [Array.getElem?_map, Array.getElem?_modify]
      split
      · rename_i hj
        subst hj
        rw [hx]
        show some (MsgSh.takes n ⟨x.shape, some (taken l)⟩) =
          some (MsgSh.takes (n + 1) ⟨x.shape, x.ledger⟩)
        rw [hl]
        rfl
      · rfl

/-- The same, as the text calls it. -/
theorem takeMasks_msgs {d : DState L} {o n : ℕ} {t : List ℕ × DState L}
    (h : takeMasksP d o n = some t) : msgsOf t.2.st = (msgsOf d.st).modify o (MsgSh.takes n) :=
  takeMasksInto_msgs o n d #[] t h

variable {Cl : Type}

/-- Where the joined sub-protocol returns, the state behind is `withClaim` at what the verifier's
taking returns. -/
theorem atM3_return_form {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∃ (t : List ℕ × St) (msg : Array OracleNotice) (row : TensorRow),
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      s' = withClaim s t.2.st msg row := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  have he := frontB_ok atS P h1
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  obtain ⟨p', msg, hp', rfl⟩ := quietB_ok atS P h3
  obtain ⟨f, -, -, hfin, -⟩ := atM3_rec h
  have e1 : atS.enter s = some s.enterMem := by simp only [atS, hfin]
  rw [e1] at he
  have e2 : s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } := by
    rw [← Option.some.inj he]
    simp only [S.enterMem, hfin]
  subst e2
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp'
  obtain ⟨_, _, _, t, _, o, _, _, _, _, _, b4, _, _, _, rfl⟩ := batt_ok hb
  exact ⟨t, msg, Batt.rowOf s.out.pending o, b4, rfl⟩

/-- **Where the joined sub-protocol returns, from s to s', the shape's own step returns, from the
shape of s to the shape of s'.** -/
theorem shape_step {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    stepSh P (shOf s) = some (shOf s') := by
  obtain ⟨t, msg, row, ht, rfl⟩ := atM3_return_form h
  unfold stepSh
  rw [if_pos (shape_of_return h)]
  have e1 : t.2.st.codes = s.st.codes := (takeMasks_same ht).1
  have e2 : msgsOf t.2.st = (msgsOf s.st).modify s.out.indexMasks
      (MsgSh.takes (Batt.masksOf P.lin.kCol)) := takeMasks_msgs ht
  show some (⟨false, s.out.reply.isSome, true, s.out.indexMasks, s.out.pending.map rowSh,
      s.st.codes, (msgsOf s.st).modify s.out.indexMasks (MsgSh.takes (Batt.masksOf P.lin.kCol))⟩ :
      Sh) =
    some ⟨false, s.out.reply.isSome, true, s.out.indexMasks, s.out.pending.map rowSh,
      t.2.st.codes, msgsOf t.2.st⟩
  rw [e1, e2]

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_msgs
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_msgs
#print axioms VerifiableInference.Desc.K13.Honest.atM3_return_form
#print axioms VerifiableInference.Desc.K13.Honest.shape_step
