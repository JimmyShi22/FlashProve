-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MadeSends.lean: WHAT THE PLANNER's LIST OF SENDINGS HOLDS FOR THE PROOF
FILE's FIRST CHAIN, WHEREVER IT IS MADE: from a return of `sendsFrom`
(Johnson/Desc/Ok/NumberPrices/AtDigest.lean: the body of Johnson.G.sendsOf, Johnson/G/Sends.lean).
Theorems on public data. A law file; no running text imports it.

  `mapM_zip_spec`   a step: a list made entry by entry of two zipped lists of one length.
  `sendsFrom_first`   where sendsFrom c returns seven lists, of the fifth, p0: its codes are the
                    proof's sizes' codes; its sendings bear, in order, the labels and the oracle
                    messages of `frameSends …` and then of W's sending (`wSend` returns); and at
                    each sending the one rule that lays oracle messages into trees returns
                    (`treesOf`: sendsFrom's own test against the plan's entry).
After Johnson/Goal/PlanValues/KeySendsCodes.lean's sendsOf_key_codes, which opens the same text for
the key's codes.

Limits. Labels, oracle messages and codes alone: nothing on the entries' numbers. One direction,
from a return. Nothing on soundness or on hiding.

-/
import Johnson.Desc.Ok.NumberPrices.AtDigest
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (Listed Sending ChainSends frameSends wSend)
open VerifiableInference.Number (sendsFrom)

/-- A list made entry by entry of two zipped lists of one length. -/
theorem mapM_zip_spec {α : Type} (f : α × Listed → Except String Sending) (Q : Sending → Prop)
    (hf : ∀ r s y, f (r, s) = .ok y → y.label = s.label ∧ y.sent = s.sent ∧ Q y) :
    ∀ (xs : List α) (L : List Listed) (out : List Sending), xs.length = L.length →
      (xs.zip L).mapM f = .ok out →
      out.map (fun y => (y.label, y.sent)) = L.map (fun l => (l.label, l.sent)) ∧ ∀ y ∈ out, Q y
  | [], [], out, _, h => by
    cases h
    exact ⟨rfl, fun _ hy => nomatch hy⟩
  | x :: xs, l :: L, out, hl, h => by
    rw [List.zip_cons_cons, List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := exc_bind h
    obtain ⟨ys, hys, h⟩ := exc_bind h
    cases h
    obtain ⟨a, b, c⟩ := hf x l y hy
    obtain ⟨i1, i2⟩ := mapM_zip_spec f Q hf xs L ys (by simpa using hl) hys
    refine ⟨by rw [List.map_cons, List.map_cons, i1, a, b], fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact c
    · exact i2 z hz
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- **The proof file's first chain's sendings, wherever the list is made.** -/
theorem sendsFrom_first {c : Configured} {k0 k1 k2 e p0 p1 p2 : ChainSends}
    (h : sendsFrom c = .ok [k0, k1, k2, e, p0, p1, p2]) :
    ∃ w, wSend c.sized.proof.batch.shape = .ok w ∧ p0.codes = c.sized.proof.codes ∧
      p0.sends.map (fun s => (s.label, s.sent)) =
        (frameSends c.sized.proof c.sized.set.samples 0 (reqGroups c.sized.proof.request).toList
          c.sized.proof.request.link ++ [w]).map (fun l => (l.label, l.sent)) ∧
      ∀ s ∈ p0.sends, (treesOf p0.codes s.sent.toArray).isSome = true := by
  unfold sendsFrom at h
  extract_lets z a one K B x at h
  have hone : ∀ (f : String) (ch : Nat) (cs : Codes) (L : List Listed) (P : Planned)
      (k : ChainSends), one f ch cs L P = .ok k → k.codes = cs ∧
        k.sends.map (fun s => (s.label, s.sent)) = L.map (fun l => (l.label, l.sent)) ∧
        ∀ s ∈ k.sends, (treesOf cs s.sent.toArray).isSome = true := by
    intro f ch cs L P k hk
    simp only [one] at hk
    split at hk
    · rename_i hlen
      obtain ⟨_, _, hk⟩ := exc_bind hk
      obtain ⟨out, hout, hk⟩ := exc_bind hk
      cases hk
      obtain ⟨i1, i2⟩ := mapM_zip_spec _ (fun y => (treesOf cs y.sent.toArray).isSome = true)
        (fun r s y hy => by
          dsimp only at hy
          split at hy
          · rename_i ht
            obtain ⟨_, _, hy⟩ := exc_bind hy
            split at hy
            · cases hy
              refine ⟨rfl, rfl, ?_⟩
              show (treesOf cs s.sent.toArray).isSome = true
              rw [eq_of_beq ht]
              rfl
            · cases hy
          · obtain ⟨_, e', _⟩ := exc_bind hy
            cases e') _ L out (eq_of_beq hlen) hout
      exact ⟨rfl, i1, i2⟩
    · obtain ⟨_, e', _⟩ := exc_bind hk
      cases e'
  split at h
  · obtain ⟨w1, _, h⟩ := exc_bind h
    obtain ⟨s1, _, h⟩ := exc_bind h
    obtain ⟨w2, hw2, h⟩ := exc_bind h
    obtain ⟨s2, _, h⟩ := exc_bind h
    rw [List.mapM_cons] at h
    obtain ⟨a0, _, h⟩ := exc_bind h
    obtain ⟨r0, hr0, h⟩ := exc_bind h
    cases h
    rw [List.mapM_cons] at hr0
    obtain ⟨a1, _, hr0⟩ := exc_bind hr0
    obtain ⟨r1, hr1, hr0⟩ := exc_bind hr0
    cases hr0
    rw [List.mapM_cons] at hr1
    obtain ⟨a2, _, hr1⟩ := exc_bind hr1
    obtain ⟨r2, hr2, hr1⟩ := exc_bind hr1
    cases hr1
    rw [List.mapM_cons] at hr2
    obtain ⟨a3, _, hr2⟩ := exc_bind hr2
    obtain ⟨r3, hr3, hr2⟩ := exc_bind hr2
    cases hr2
    rw [List.mapM_cons] at hr3
    obtain ⟨a4, h4, hr3⟩ := exc_bind hr3
    obtain ⟨r4, _, hr3⟩ := exc_bind hr3
    cases hr3
    obtain ⟨q1, q2, q3⟩ := hone _ _ _ _ _ _ h4
    exact ⟨w2, hw2, q1, q2, by rw [q1]; exact q3⟩
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mapM_zip_spec
#print axioms VerifiableInference.Desc.LinkJoin.sendsFrom_first
