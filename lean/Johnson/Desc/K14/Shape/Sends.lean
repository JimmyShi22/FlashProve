-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Sends.lean: the shared chain's shape (Johnson/Desc/K14/Shape/Lin.lean): THE
UPDATE AT THE TWO SENDINGS; and: wherever a sending's decide function returns .ok, the shape behind
is the update of the shape in front: at the sending of o_u with no further premise; AT THE SENDING
OF o_omega AND o_sp WHERE THE PLAN HAS TWO CODES.

How. What a sending does to the shape of statement, book and roots is a function with code of its
public parameters and that shape alone, with its law from any return of the sending's own decision,
general in what the chain notes: sendCore, send_core (Johnson/Desc/First/Shape/SendCore.lean). They
are called here. Of the sampled seeds and the answers sent the state behind holds the new messages'
sample constraints alone, of which the shape keeps the number: that is a reading of the state that
the sending writes (K1.behind, as SendCore.lean's core_behind names it); no law says it. This file
adds what the kind notes behind a sending: the new messages' numbers, and o_u's layout.

Main names:
  ids_at              the new messages' numbers: a law on arrays. IT HAS KIN IN THE LIBRARY: ids_get
                      (Johnson/Desc/Sound/MembersCarried.lean) has the same statement; ids_next
                      (Johnson/Desc/K14/Honest/SendKept.lean) says that and i < n
  sendUUp, sendOUp    **the two updates**
  sendU_carries, sendO_carries   **the laws**, at the sub-protocols' decide functions, at any rounds

What is assumed, as premises: at the second sending: the plan has two codes. Nothing on the state,
on a round or on a column. sendU_carries serves both values of masksAhead.

What is not claimed. When a sending returns. Nothing on soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.Pieces
import Johnson.Desc.First.Shape.SendCore
import Johnson.Desc.Key.Laid.Laid2
import Johnson.Desc.K14.Law.LedgerRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (coreSh orc_size)
open VerifiableInference.Desc.First.Shape (sendCore send_core)
open VerifiableInference.Desc.Key.LaidW (sendAt_yes)
open Desc.K14.Law (parU parO)

/-- The new messages' numbers: a law on arrays: the entry number i of the array s, s + 1, …, s + n -
1, where it is there, is i + s. The library's ids_get (Johnson/Desc/Sound/MembersCarried.lean) has
the same statement; its ids_next (Johnson/Desc/K14/Honest/SendKept.lean) says more. -/
theorem ids_at (n s i v : Nat) (h : ((Array.range n).map (· + s))[i]? = some v) : v = i + s := by
  rw [Array.getElem?_map] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hi, e⟩ := Array.getElem?_eq_some_iff.1 hj
  rw [Array.getElem_range] at e
  rw [e]

/-- **The update at the sending of o_u**: the sending; the kind notes o_u's number and layout, and
the first mask's number where the masks go ahead; where they do not, the first mask is set to none,
whatever stood there. sentU is a free letter: it is the chain's update only where withU P.S = some
sentU. -/
def sendUUp (P : P14) (sentU : Array OracleNotice) (a : Sh2) : Sh2 :=
  { a with
    core := sendCore (parU P sentU) a.core
    lin := { a.lin with
      oU := a.core.st.oracles.length
      lay := vectorLay a.core.st.codes P.par.S.fold.u P.par.S.fold.rowsHigh
      firstMask := if P.par.S.masksAhead then some (a.core.st.oracles.length + 1) else none } }

/-- **The update at the sending of o_omega and o_sp**, where the plan has two codes: the sending;
the kind notes the two numbers. -/
def sendOUp (P : P14) (a : Sh2) : Sh2 :=
  { a with
    core := sendCore (parO P) a.core
    lin := { a.lin with
      oOmega := a.core.st.oracles.length, oSp := a.core.st.oracles.length + 1 } }

variable {P : P14} {sentU : Array OracleNotice}

/-- **The sending of o_u**: wherever its decide function returns .ok, the shape behind is sendUUp of
the shape in front. No premise but the return; sentU is any array. -/
theorem sendU_carries (n : String) (f : Option Fmt.Entry) (g : List (List Nat)) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n (parU P sentU) f g (behindU P.par)).decide d rs gs = .ok d') :
    sh2 d' = sendUUp P sentU (sh2 d) := by
  obtain ⟨ids, x, hx, hn⟩ := sendAt_yes P n _ f g _ d d' _ gs h
  obtain ⟨hi, e1, -, -⟩ := send_core hx
  have hi' : ids = (Array.range (parU P sentU).sent.size).map (· + d.st.oracles.size) := hi
  have e1' : coreSh (coreOf x) = sendCore (parU P sentU) (sh2 d).core := e1
  have hc : x.st.codes = d.st.codes := congrArg (·.st.codes) e1'
  subst hi'
  have z1 : (sh2 d).core.st.oracles.length = d.st.oracles.size := orc_size d.st
  unfold behindU at hn
  by_cases c : P.par.S.masksAhead = true
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, c, if_true,
      Option.map_eq_some_iff] at hn
    obtain ⟨mask, ⟨v, hv, rfl⟩, i0, h0, e⟩ := hn
    obtain rfl := Option.some.inj e
    obtain rfl := ids_at _ _ _ _ h0
    obtain rfl := ids_at _ _ _ _ hv
    unfold sendUUp
    rw [z1, if_pos c, ← e1']
    show Sh2.mk _ { linSh d.loc with
      oU := 0 + d.st.oracles.size, lay := vectorLay x.st.codes _ _
      firstMask := some (1 + d.st.oracles.size) } = _
    rw [hc, Nat.zero_add, Nat.add_comm 1]
    rfl
  · have c' : P.par.S.masksAhead = false := by simpa using c
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, c', Bool.false_eq_true, if_false,
      Option.some.injEq] at hn
    obtain ⟨mask, rfl, i0, h0, rfl⟩ := hn
    obtain rfl := ids_at _ _ _ _ h0
    unfold sendUUp
    rw [z1, if_neg c, ← e1']
    show Sh2.mk _ { linSh d.loc with
      oU := 0 + d.st.oracles.size, lay := vectorLay x.st.codes _ _, firstMask := none } = _
    rw [hc, Nat.zero_add]
    rfl

/-- **The sending of o_omega and o_sp**: wherever its decide function returns .ok, where the plan
has two codes (hS), the shape behind is sendOUp of the shape in front. -/
theorem sendO_carries (hS : P.par.S.sharedSplitNeeded = true) (n : String) (f : Option Fmt.Entry)
    (g : List (List Nat)) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n (parO P) f g (behindOmega P.par)).decide d rs gs = .ok d') :
    sh2 d' = sendOUp P (sh2 d) := by
  obtain ⟨ids, x, hx, hn⟩ := sendAt_yes P n _ f g _ d d' _ gs h
  obtain ⟨hi, e1, -, -⟩ := send_core hx
  have hi' : ids = (Array.range (parO P).sent.size).map (· + d.st.oracles.size) := hi
  have e1' : coreSh (coreOf x) = sendCore (parO P) (sh2 d).core := e1
  subst hi'
  have z1 : (sh2 d).core.st.oracles.length = d.st.oracles.size := orc_size d.st
  unfold behindOmega at hn
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, hS, if_true] at hn
  obtain ⟨sp, h1, i0, h0, e⟩ := hn
  obtain rfl := Option.some.inj e
  obtain rfl := ids_at _ _ _ _ h0
  obtain rfl := ids_at _ _ _ _ h1
  unfold sendOUp
  rw [z1, ← e1']
  show Sh2.mk _ { linSh d.loc with
    oOmega := 0 + d.st.oracles.size, oSp := 1 + d.st.oracles.size } = _
  rw [Nat.zero_add, Nat.add_comm 1]
  rfl

end Desc.K14.Shape

#print axioms Desc.K14.Shape.ids_at
#print axioms Desc.K14.Shape.sendU_carries
#print axioms Desc.K14.Shape.sendO_carries
