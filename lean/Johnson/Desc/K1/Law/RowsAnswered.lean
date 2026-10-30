-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowsAnswered.lean: "every message whose shape counts an answer has a stored
sample row" (the invariant of Johnson/Top/H0/K2Hands/AnsweredStored.lean: AnsweredStored,
NewAnswered, KeepsAns) along the proof file's first chain: the share of K1's files: for the kind
K1's sub-protocols that send messages, and for M:4 of the kind K13. A law file; no running text
imports it.
  newAnswered_same: NewAnswered passes along SameRows
  decideSend_answered: behind an accept of the kind's decision each NEW message whose shape counts
      an answer has as many stored rows as answers: NewAnswered. NO premise: neither the kind's
      condition on the list of rounds nor anything on the rounds
  keepsAns_sendAtS, keepsAns_commitAtS, keepsAns_firstAtS, keepsAns_laterAt, keepsAns_wAt: so each
      keeps the invariant
  keepsAns_atM3, keepsAns_atM4, keepsAns_chainEnd: the kind K13's two and a chain's last
      sub-protocol, by SameRows (Johnson/Desc/K13/Law/RowsKept.lean)

Whence. A new message is written as wr codes seeds o s ys (Writes.lean): where s counts an answer
its stored rows are rowsOf …, whose number is s.answers (rowsOf_size) since the place has a seed for
each answer (msgAt_answers_le) and the decision's own test on the counts has found the answers
(outs_spec).

What is not claimed. That the first chain of the IOP as written in Lean is made of these
sub-protocols. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H0.K2Hands.AnsweredStored
import Johnson.Desc.K1.Law.RowsKept
import Johnson.Desc.K13.Law.RowsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open VerifiableInference.Desc.Keeps1

theorem newAnswered_same {n : Nat} {A B : Statement} (h : NewAnswered n A) (hs : SameRows A B) :
    NewAnswered n B := by
  intro o x ho hx ha
  have e := hs.2 o
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
  obtain ⟨e1, e3⟩ := Prod.mk.inj e0
  rw [← e3]
  exact h o x0 ho hx0 (by rw [e1]; exact ha)

/-- **Behind an accept of the kind's decision each new message that counts an answer has its
stored rows.** -/
theorem decideSend_answered {L : Type} (P : Par) (owed : Option Nat) (d d' : DState L)
    (rs : List Fmt.RoundView) (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) :
    NewAnswered d.st.oracles.size d'.st := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨⟨_, _, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    intro o x ho hx ha
    obtain ⟨k, rfl⟩ : ∃ k, o = d.st.oracles.size + k := ⟨o - d.st.oracles.size, by omega⟩
    have hx' : (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)).toArray[d.st.oracles.size + k]? = some x := hx
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)] at hx'
    have hx2 : (outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[k]? =
        some x := by simpa using hx'
    have hk : k < (shapesOf P).length := by
      have := (List.getElem?_eq_some_iff.1 hx2).1
      rwa [outs_length] at this
    obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
      d.st.oracles.size (answersIn r₂) hf k hk
    obtain rfl : wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys' = x :=
      Option.some.inj (hget.symm.trans hx2)
    have hshape : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys').shape =
        (shapesOf P)[k] := by
      unfold wr
      split <;> rfl
    rw [hshape] at ha
    have e : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k)
          (shapesOf P)[k] ys' := by simp [wr, ha]
    have hlenS : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
    have hle : (shapesOf P)[k].answers ≤ (seedsOf P r₁).length := by
      rw [hlenS]
      exact msgAt_answers_le P ⟨k, hk⟩
    rw [e, rowsOf_size _ _ _ _ _ hle hy]
    exact ha

variable {Cl : Type}

theorem keepsAns_sendAtS (P : Par) : KeepsAns (sendAtS P : Block S Cl) :=
  fun s s' rs gs _ hy hg => by
    refine answered_oldRows (oldRows_sendAtS P s s' rs gs hy) ?_ hg
    obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs hy
    rw [e1]
    exact decideSend_answered P _ (stateOf s (#[] : Array Nat)) d' rs ids h1

theorem keepsAns_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    KeepsAns (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs _ hy hg => by
    refine answered_oldRows (oldRows_commitAtS P link moment arrays s s' rs gs hy) ?_ hg
    obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs hy
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
    have a := decideSend_answered P _ _ d₁ rs ids h2
    rw [e0] at a
    rw [e1]
    exact newAnswered_same a (sameRows_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

theorem keepsAns_firstAtS (q : Params.First) (gp : GPar) :
    KeepsAns (firstSegmentOpening q gp : Block S Cl) :=
  fun s s' rs gs _ hy hg => by
    refine answered_oldRows (oldRows_firstAtS q gp s s' rs gs hy) ?_ hg
    obtain ⟨c, d', h1, e1, _⟩ := firstAtS_ok q gp s s' _ gs hy
    obtain ⟨g, d₁, ids, d₂, h0, h2, f₁, own, mine, f₂, h3⟩ := firstOwn_ok _ _ _ _ _ _ _ h1
    have a0 : d₁.st.oracles = (stateOf s ()).st.oracles := by
      unfold Ground.newGroupP at h0
      split at h0
      · obtain rfl : _ = d₁ := (Prod.mk.inj (Option.some.inj h0)).2
        rfl
      · cases h0
    have a := decideSend_answered (firstPar q gp) _ d₁ d₂ rs ids h2
    rw [a0] at a
    rw [e1]
    exact newAnswered_same a (sameRows_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

theorem keepsAns_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    KeepsAns (laterAt q gp link piece moment arrays : Block S Cl) :=
  keepsAns_commitAtS _ link moment arrays

theorem keepsAns_wAt (q : Params.First) (gp : GPar) (piece : Nat) (msg : Array OracleNotice) :
    KeepsAns (sendAtS (parW q gp piece msg) : Block S Cl) := keepsAns_sendAtS _

/-! ## The kind K13's two, and a chain's last sub-protocol -/

theorem keepsAns_atM3 (p : K13.Where) : KeepsAns (K13.atM3 (Cl := Cl) p) :=
  keepsAns_of_rows (K13.Law.atM3_sameRows p)

theorem keepsAns_atM4 (p : K13.Where) (commitW : Block S Cl) (hW : KeepsAns commitW) :
    KeepsAns (K13.atM4 p commitW) :=
  keepsD_andThen _ hW (keepsAns_of_rows (K13.Law.rowsB_sameRows p))

theorem keepsAns_chainEnd (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → ChainEnd.Clauses) :
    KeepsAns (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks) :=
  fun s s' rs gs _ hy hs => by
    rw [K13.Law.chainEnd_same chain piece sealed inFront asks s s' rs gs hy]
    exact hs

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.decideSend_answered
#print axioms VerifiableInference.Desc.K1.keepsAns_sendAtS
#print axioms VerifiableInference.Desc.K1.keepsAns_commitAtS
#print axioms VerifiableInference.Desc.K1.keepsAns_firstAtS
#print axioms VerifiableInference.Desc.K1.keepsAns_laterAt
#print axioms VerifiableInference.Desc.K1.keepsAns_wAt
#print axioms VerifiableInference.Desc.K1.keepsAns_atM3
#print axioms VerifiableInference.Desc.K1.keepsAns_atM4
#print axioms VerifiableInference.Desc.K1.keepsAns_chainEnd
