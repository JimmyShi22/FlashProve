-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendAtS.lean: the kind's three blocks at the first chain's carried record
are sendings in the sense of the law in the form of the rule of composition (IsSend,
GoodSend3.lean); and what a sealed message gives: of the library's list of the word sent at most one
message meets the record's sample rows.

Main names: size_of_same; isSend_sendAtS, isSend_commitAtS, isSend_firstAtS; sealed_unique.

What is not claimed. The law itself is send_goodIn; its other premises are not met here. One answer
a message. Nothing on soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.K1.Law.SeedAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- Statements with the same messages have as many. -/
theorem size_of_same {A B : Statement} (h : SameMsgs A B) : B.oracles.size = A.oracles.size := by
  have key : ∀ j : Nat, j < B.oracles.size ↔ j < A.oracles.size := by
    intro j
    have e := congrArg Option.isSome (h.2 j)
    simp only [Option.isSome_map] at e
    constructor
    · intro hj
      by_contra hn
      rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
      cases e
    · intro hj
      by_contra hn
      rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
      cases e
  rcases Nat.lt_trichotomy B.oracles.size A.oracles.size with hlt | heq | hgt
  · exact absurd ((key _).2 hlt) (Nat.lt_irrefl _)
  · exact heq
  · exact absurd ((key _).1 hgt) (Nat.lt_irrefl _)

/-- W's sending. -/
theorem isSend_sendAtS (P : Par) : IsSend P (fun s : S => s.st) (sendAtS P : Block S Cl) := by
  intro s s' r₁ r₂ gs h
  obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs h
  exact ⟨_, _, d', _, ids, h1, by show SameMsgs d'.st s'.st; rw [e1]; exact ⟨rfl, fun _ => rfl⟩,
    by show s'.st.oracles.size = _; rw [e1]⟩

/-- A later moment. -/
theorem isSend_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    IsSend P (fun s : S => s.st) (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' r₁ r₂ gs h
  obtain ⟨t, y, _, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs h
  obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
  have hs := joinOwnP_msgs _ _ _ _ _ _ _ h3
  exact ⟨_, _, d₁, _, ids, h2, by show SameMsgs d₁.st s'.st; rw [e1]; exact hs,
    by show s'.st.oracles.size = _; rw [e1]; exact size_of_same hs⟩

/-- The first segment's opening. -/
theorem isSend_firstAtS (q : Params.First) (gp : GPar) :
    IsSend (firstPar q gp) (fun s : S => s.st) (firstSegmentOpening q gp : Block S Cl) := by
  intro s s' r₁ r₂ gs h
  obtain ⟨c, d', h1, e1, _⟩ := firstAtS_ok q gp s s' _ gs h
  obtain ⟨g, d₁, ids, d₂, _, h2, f₁, own, mine, f₂, h3⟩ := firstOwn_ok _ _ _ _ _ _ _ h1
  have hs := joinOwnP_msgs _ _ _ _ _ _ _ h3
  exact ⟨_, d₁, d₂, _, ids, h2, by show SameMsgs d₂.st s'.st; rw [e1]; exact hs,
    by show s'.st.oracles.size = _; rw [e1]; exact size_of_same hs⟩

/-- **What a sealed message gives**: two messages of the library's list of the word sent whose
tables both meet the record's sample rows of the message are one. -/
theorem sealed_unique (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str)
    (St : Statement) (o : Nat) (hT : Tie cs s) (h : Sealed cs s e f St o) :
    ∃ x, St.oracles[o]? = some x ∧ x.sampled = true ∧
      ∀ (w w' : Means.Words GE) (msg msg' : (portCode cs s).J → GE),
        w o = tabOf cs s msg → w' o = tabOf cs s msg' →
        (portOmZ cs s e).InList f msg → (portOmZ cs s e).InList f msg' →
        Means.AllSay rdE St x.sampleRows.toList w → Means.AllSay rdE St x.sampleRows.toList w' →
        msg = msg' := by
  obtain ⟨ρ, y, ⟨hc, x, z, β, t, hx, hs, hm, hr, hread, _⟩, hno⟩ := h
  refine ⟨x, hx, hm, fun w w' msg msg' hw hw' hl hl' a b => ?_⟩
  rw [hr] at a b
  exact unique_port' St o x hx cs s hc hs hT e f z β t ρ hread hno w w' msg msg' hw hw' hl hl'
    (a _ (by simp)) (b _ (by simp))

end VerifiableInference.Desc.K1
