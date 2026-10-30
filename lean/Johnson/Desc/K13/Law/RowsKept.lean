-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RowsKept.lean: the messages' stored sample rows along the proof file's first
chain (the relation of Johnson/Top/H0/K2Hands/SampleChain.lean: SameRows, OldRows, RowsInv
Q, KeepsInv Q): the share for the kind K13's sub-protocols and for a chain's last
sub-protocol, IN THAT FILE's END FORM. A law file; no running text imports it. The content is
proved: atM3_same and rowsB_same (Johnson/Desc/K13/Law/PinDec.lean: SameAll: the codes, and every
message's shape, mark, stored rows and pad stay): here they are called.
  sameRows_of_all: SameAll gives SameRows
  atM3_sameRows, keepsInv_atM3: an accept of the members' batching (M:3) gives SameRows between the
      two states' statements; so it keeps the invariant, for every Q, on all rounds
  rowsB_sameRows, keepsInv_atM4: the own group and (Eval) behind W's commitment (M:4) likewise; so
      M:4 keeps the invariant wherever the sub-protocol that commits to W does
  chainEnd_same, keepsInv_chainEnd: a chain's last sub-protocol returns the state that it is handed
A tool beside, for whoever has a sub-protocol that calls the ground's plain functions but never
admits a sample:
  OldNo A B: the messages of A have in B their shape and stored rows (OldRows), and no message of B
      from A's number on has a stored row (NoNewRows); inv_of_oldNo: it carries RowsInv Q for every
      Q
  groundQuiet_oldNo: OldNo is kept by the eight plain functions of the ground that ask nothing of
      their caller (Johnson/Desc/GroundQuiet.lean): so every law that is stated for a GroundQuiet
      relation can be called at it. The admitting of a sample, which writes stored rows, is not
      among the eight

What is not claimed. That W's commitment keeps the invariant: the kind K1's share
(Johnson/Desc/K1/Law/RowsKept.lean). That the first chain of the IOP as written in Lean is made of
these sub-protocols. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H0.K2Hands.RowsGround
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K13.Law.PinDec
import Johnson.Desc.ChainEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Keeps
open VerifiableInference.Desc.Keeps1

/-- The old messages keep their shape and stored rows; no new message has a stored row. -/
def OldNo (A B : Statement) : Prop := OldRows A B ∧ NoNewRows A.oracles.size B

theorem oldNo_of_same {A B : Statement} (h : SameRows A B) : OldNo A B := by
  refine ⟨oldRows_of_sameRows h, fun o x ho hx => ?_⟩
  have e := h.2 o
  rw [hx, Array.getElem?_eq_none ho] at e
  cases e

theorem oldNo_refl (A : Statement) : OldNo A A := oldNo_of_same (SameRows.refl A)

theorem oldNo_trans {A B C : Statement} (h1 : OldNo A B) (h2 : OldNo B C) : OldNo A C := by
  refine ⟨h1.1.trans h2.1, fun o x ho hx => ?_⟩
  by_cases hb : o < B.oracles.size
  · have e := h2.1.2 o hb
    rw [hx] at e
    obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
    have e3 : x0.sampleRows = x.sampleRows := (Prod.mk.inj e0).2
    rw [← e3]
    exact h1.2 o x0 ho hx0
  · exact h2.2 o x (Nat.le_of_not_lt hb) hx

/-- It carries the invariant, whatever is said of a message's stored rows. -/
theorem inv_of_oldNo {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {A B : Statement}
    (h : OldNo A B) (hA : RowsInv Q A) : RowsInv Q B :=
  rowsInv_oldRows h.1 (newInv_of_none h.2) hA

/-- **The eight plain functions that ask nothing of their caller keep it.** -/
theorem groundQuiet_oldNo : GroundQuiet OldNo where
  refl := oldNo_refl
  trans := oldNo_trans
  newGroup := fun d d' code maskCode n h => oldNo_of_same (newGroupP_rows d d' code maskCode n h)
  recv := fun ft d d' sent ids h => recvP_rows ft d d' sent ids h
  join := fun d d' g o kept h => oldNo_of_same (joinP_rows d d' g o kept h)
  addRow := fun d d' g row h => oldNo_of_same (addRowP_rows d d' g row h)
  takeMask := fun d d' o n h => oldNo_of_same (takeMaskP_rows d d' o n h)
  closeLedger := fun d d' o h => oldNo_of_same (closeLedgerP_rows d d' o h)
  spendAsMask := fun d d' o h => oldNo_of_same (spendAsMaskP_rows d d' o h)
  adopt := fun d d' sent given ids h => adoptP_rows d d' sent given ids h

variable {Cl : Type} {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop}

/-- SameAll reads more of a message than SameRows. -/
theorem sameRows_of_all {A B : Statement} (h : SameAll A B) : SameRows A B := by
  refine ⟨h.1, fun j => ?_⟩
  have e := congrArg (Option.map fun t : OracleShape × Bool × Array OnBytes.Row ×
    List (OnBytes.Part × Nat) => (t.1, t.2.2.1)) (h.2 j)
  simpa [sampleOf, Option.map_map, Function.comp_def] using e

/-- **M:3.** -/
theorem atM3_sameRows (p : Where) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (atM3 (Cl := Cl) p).decide s rs gs = .ok s') : SameRows s.st s'.st :=
  sameRows_of_all (atM3_same h)

theorem keepsInv_atM3 (p : Where) : KeepsInv Q (atM3 (Cl := Cl) p) :=
  keepsInv_of_rows (atM3_sameRows p)

/-- The own group and (Eval). -/
theorem rowsB_sameRows (p : Where) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (rowsB (Cl := Cl) atS p).decide s rs gs = .ok s') : SameRows s.st s'.st :=
  sameRows_of_all (rowsB_same h)

/-- **M:4**, wherever the sub-protocol that commits to W keeps the invariant. -/
theorem keepsInv_atM4 (p : Where) (commitW : Block S Cl) (hW : KeepsInv Q commitW) :
    KeepsInv Q (atM4 p commitW) :=
  keepsD_andThen _ hW (keepsInv_of_rows (rowsB_sameRows p))

/-- **A chain's last sub-protocol returns the state that it is handed.** -/
theorem chainEnd_same {T : Type} (chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : T → ChainEnd.Clauses) (s s' : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks).decide s rs gs = .ok s') :
    s' = s := by
  have h' : (ChainEnd.refuse (asks s)).map (fun _ => s) = .ok s' := h
  cases hr : ChainEnd.refuse (asks s) with
  | error e =>
    rw [hr] at h'
    cases h'
  | ok u =>
    rw [hr] at h'
    exact (Except.ok.inj h').symm

theorem keepsInv_chainEnd (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → ChainEnd.Clauses) :
    KeepsInv Q (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks) :=
  fun s s' rs gs _ hy hs => by
    rw [chainEnd_same chain piece sealed inFront asks s s' rs gs hy]
    exact hs

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.groundQuiet_oldNo
#print axioms VerifiableInference.Desc.K13.Law.sameRows_of_all
#print axioms VerifiableInference.Desc.K13.Law.atM3_sameRows
#print axioms VerifiableInference.Desc.K13.Law.keepsInv_atM3
#print axioms VerifiableInference.Desc.K13.Law.rowsB_sameRows
#print axioms VerifiableInference.Desc.K13.Law.keepsInv_atM4
#print axioms VerifiableInference.Desc.K13.Law.chainEnd_same
#print axioms VerifiableInference.Desc.K13.Law.keepsInv_chainEnd
