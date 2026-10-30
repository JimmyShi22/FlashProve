-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendSize.lean: the ledger of the messages' numbers: a yes of each of the
kind's blocks at the first chain's carried record adds just the place's messages to the
statement's: so the number "the k-th of the last messages behind the block", at which the law of a
sending seals a new message, is the number of the statement's messages in front of the block, plus
k.

Main names: Grows; grows_sendAtS, grows_commitAtS, grows_firstAtS, grows_laterAt; grows_andThen;
slot_eq.

What is not claimed. How a message's number goes with a tree and a tenant of the file. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

variable {T Cl : Type}

/-- A block's yes adds n messages to the statement's. -/
def Grows (stOf : T → Statement) (n : Nat) (b : Block T Cl) : Prop :=
  ∀ s s' rs gs, b.decide s rs gs = .ok s' → (stOf s').oracles.size = (stOf s).oracles.size + n

/-- A yes of the kind's decision, on whatever rounds. -/
theorem decideSend_size {L : Type} (P : Par) (owed : Option Nat) (d d' : DState L)
    (rs : List Fmt.RoundView) (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) :
    d'.st.oracles.size = d.st.oracles.size + (shapesOf P).length := by
  match rs, h with
  | [r₁, r₂], h => exact size_behind P owed d d' r₁ r₂ ids h

theorem grows_sendAtS (P : Par) :
    Grows (fun s : S => s.st) (shapesOf P).length (sendAtS P : Block S Cl) := by
  intro s s' rs gs h
  obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs h
  show s'.st.oracles.size = s.st.oracles.size + _
  rw [e1]
  exact decideSend_size P _ (stateOf s (#[] : Array Nat)) d' rs ids h1

theorem grows_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Grows (fun s : S => s.st) (shapesOf P).length
      (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h
  obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs h
  obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
  have a := decideSend_size P _ _ d₁ rs ids h2
  rw [e0] at a
  show s'.st.oracles.size = s.st.oracles.size + _
  rw [e1, size_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3)]
  exact a

theorem grows_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Grows (fun s : S => s.st) (shapesOf (parLater q gp link piece moment)).length
      (laterAt q gp link piece moment arrays : Block S Cl) :=
  grows_commitAtS _ _ _ _

theorem grows_firstAtS (q : Params.First) (gp : GPar) :
    Grows (fun s : S => s.st) (shapesOf (firstPar q gp)).length (firstSegmentOpening q gp : Block S Cl) := by
  intro s s' rs gs h
  obtain ⟨c, d', h1, e1, _⟩ := firstAtS_ok q gp s s' _ gs h
  obtain ⟨g, d₁, ids, d₂, h0, h2, f₁, own, mine, f₂, h3⟩ := firstOwn_ok _ _ _ _ _ _ _ h1
  have a := decideSend_size _ _ d₁ d₂ rs ids h2
  rw [newGroupP_size _ _ _ _ _ h0] at a
  show s'.st.oracles.size = s.st.oracles.size + _
  rw [e1, size_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3)]
  exact a

/-- With a block behind that leaves the messages. -/
theorem grows_andThen (stOf : T → Statement) (n : Nat) (name : String) (p q : Block T Cl)
    (hp : Grows stOf n p) (hq : LeavesMsgs stOf q) : Grows stOf n (p.andThen name q) := by
  intro s s' rs gs h
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  rw [size_of_same (hq _ _ _ _ h2)]
  exact hp _ _ _ _ h1

/-- **The slot at which the law seals new message number k is the number of the messages in front,
plus k.** -/
theorem slot_eq (stOf : T → Statement) (n : Nat) (b : Block T Cl) (hb : Grows stOf n b) (s s' : T)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide s rs gs = .ok s')
    (k : Nat) : (stOf s').oracles.size - n + k = (stOf s).oracles.size + k := by
  rw [hb s s' rs gs h]
  omega

end VerifiableInference.Desc.K1
