-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/SendMore.lean: a yes of K1's sending's decision gives SentMore
(Johnson/Desc/Key/Laid/SentMoreDef.lean): the roots received, and each new sampled message's ledger.
Statement and proof, over decideSend_iff (Johnson/Desc/K1/Law/Writes3.lean) and our
outs_get (SendLaid.lean).
  send_more.
(Kin: decideSend_book has the book and the roots behind a sending.)
-/
import Johnson.Desc.Key.Laid.SendLaid
import Johnson.Desc.Key.Laid.SentMoreDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key.LaidW
open OnBytes OnBytes.Params OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.K1

variable {L : Type}

/-- **A yes of the sending's decision gives SentMore.** -/
theorem send_more (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    SentMore P.sent P.codes d.roots d'.roots d.st d'.st := by
  obtain ⟨⟨_, hc, _, hok, hf⟩, _, hd'⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  have hsome : (layTrees P.codes P.sent).isSome = true := by
    have := hok
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, Bool.and_eq_true] at this
    rw [← hc]
    exact (VerifiableInference.Desc.Own.treesCan_eq _ _) ▸ this.2.1
  obtain ⟨lay, hlay⟩ := Option.isSome_iff_exists.1 hsome
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hb : d' = put (recvD P.gp.firstTree d P.sent lay)
      (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)) := by
    rw [hd']
    simp [K1.behind, hlay]
  have hO : d'.st.oracles.toList = d.st.oracles.toList ++
      outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂) := by
    rw [hb]
    simp [put]
  refine ⟨⟨lay, by rw [hc]; exact hlay, by rw [hb]; rfl⟩, fun i n hn h0 => ?_⟩
  have hs : (shapesOf P)[i]? = some n.shape := by
    simp [shapesOf, hn]
  obtain ⟨ys', a, _⟩ := outs_get P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.size
    (answersIn r₂) i n.shape (by rw [hlen]; exact hf) hs
  refine ⟨wr P.codes (seedsOf P r₁) (d.st.oracles.size + i) n.shape ys', ?_, ?_⟩
  · rw [← Array.getElem?_toList, hO,
      List.getElem?_append_right (by rw [Array.length_toList]; omega), Array.length_toList,
      Nat.add_sub_cancel_left]
    exact a
  · simp [wr, h0]

end VerifiableInference.Desc.Key.LaidW
