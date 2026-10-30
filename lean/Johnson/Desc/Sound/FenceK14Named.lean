-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/FenceK14Named.lean: THE FENCE AT K14's TWO SENDINGS, WITH THE TWO SENDINGS NAMED TO THE LETTER. Five theorems.
WHY: `sends_are` and `seatedNew_named` (FenceK14Sends.lean, FenceK14Roots.lean) hide the place Q behind
"there is": Q.codes is handed out, Q.sent is not: two openings of that "there is" give unrelated Q's: so the starred statement is not the one meeting
point with the plan's half · no composed form in which (T) has left the interface for the one equation on the data.
  `blocks_two`: THE SECOND AND THE FIFTH OF blocks P ARE, TO THE LETTER: sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" sentU) (entries P)[0]? [[0], []]
    (behindU P.par), with withU P.S = some sentU · sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (entries P)[1]? [[1], [1, 0]] (behindOmega P.par).
  `seatedNew_sendAt`: THE RIDER AT AN EXPLICIT SENDING sendAt P n Q …: for lay := layTrees Q.codes Q.sent: at every yes under the fence, of a piece of the description's form
    that holds it: the i-th of Q.sent is seated at q.base + lay.tree i, at part lay.part i.
  `seatedNew_u`, `seatedNew_omega`: THE SAME AT THE TWO BY NAME: lay := layTrees P.codes sentU | layTrees P.codes (withOmega P.S): VALUES OF THE PLAN ALONE, IN THE STATEMENT.
  `bookKept_at_send_of_data`: BookKept at a piece of the description's form under (D) q.trees = the sum of its block's declared rounds' roots, and (R) under the fence.

Every "there is", walked: sentU: what goes out with o_u, where it can be said (withU P.S).
Limits. Book-keeping. No member. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceK14Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece below Received BookKept FenceAt SeatedAt bookedOf
  seated_of_received)
open _root_.Run.PQ (CK)

/-- **The two sendings, to the letter.** -/
theorem blocks_two (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ sentU, withU P.S = some sentU ∧
      b2 = sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" sentU) (entries P)[0]? [[0], []]
        (behindU P.par) ∧
      b5 = sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (entries P)[1]?
        [[1], [1, 0]] (behindOmega P.par) := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  exact ⟨sentU, hU, rfl, rfl⟩

variable {W ρ P₁ : Type} {F : Frame} {C : CK}

/-- **The rider at an explicit sending.** -/
theorem seatedNew_sendAt (lo : ℕ) (low : Tree → Option ℕ) (P : P14) (n : String)
    (Q : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (behind : St → Array Nat → Option St)
    (hbk : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (lay : TreeLay) (hl : layTrees Q.codes Q.sent = some lay)
    (q : Piece C F (P₁ × St) Unit W)
    (hq : q.b = (below (sendAt P n Q inFront groups behind)).lift Prod.snd
      fun (t : P₁ × St) s => (t.1, s)) :
    ∀ a τ c,
      FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
        (fun t => t.2.roots)) q.base a →
      q.ior.red.out a τ = some c →
      ∀ i, i < Q.sent.size → SeatedAt lo low c.1.2.book (a.1.2.st.oracles.size + i)
        (q.base + lay.tree.getD i 0) (lay.part.getD i 0) := by
  intro a τ c hf hout
  obtain ⟨_, gs, hd⟩ := piece_yes q a τ c hout
  rw [hq] at hd
  obtain ⟨hd', _⟩ := decide_below_lift _ a.1 c.1 _ gs hd
  have hR := sendAt_received_plan P n Q inFront groups behind hbk lay hl _ _ _ gs hd'
  exact seated_of_received lo low q.base _ _ lay _ _ _ _ _ _ hR hf.1

/-- **The rider at "send o_u", by name.** -/
theorem seatedNew_u (lo : ℕ) (low : Tree → Option ℕ) (P : P14) (sentU : Array OracleNotice)
    (lay : TreeLay) (hl : layTrees P.codes sentU = some lay) (q : Piece C F (P₁ × St) Unit W)
    (hq : q.b = (below (sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" sentU)
      (entries P)[0]? [[0], []] (behindU P.par))).lift Prod.snd fun (t : P₁ × St) s => (t.1, s)) :
    ∀ a τ c,
      FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
        (fun t => t.2.roots)) q.base a →
      q.ior.red.out a τ = some c →
      ∀ i, i < sentU.size → SeatedAt lo low c.1.2.book (a.1.2.st.oracles.size + i)
        (q.base + lay.tree.getD i 0) (lay.part.getD i 0) := by
  have h := seatedNew_sendAt lo low P _ (parK1 P 2 "o_u and the first mask" sentU) _ _ _
    (behindU_book P.par) lay (by rw [parK1_sent]; exact hl) q hq
  rw [parK1_sent] at h
  exact h

/-- **The rider at "send o_omega", by name.** -/
theorem seatedNew_omega (lo : ℕ) (low : Tree → Option ℕ) (P : P14)
    (lay : TreeLay) (hl : layTrees P.codes (withOmega P.S) = some lay)
    (q : Piece C F (P₁ × St) Unit W)
    (hq : q.b = (below (sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S))
      (entries P)[1]? [[1], [1, 0]] (behindOmega P.par))).lift Prod.snd
        fun (t : P₁ × St) s => (t.1, s)) :
    ∀ a τ c,
      FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
        (fun t => t.2.roots)) q.base a →
      q.ior.red.out a τ = some c →
      ∀ i, i < (withOmega P.S).size → SeatedAt lo low c.1.2.book (a.1.2.st.oracles.size + i)
        (q.base + lay.tree.getD i 0) (lay.part.getD i 0) := by
  have h := seatedNew_sendAt lo low P _ (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) _ _ _
    (behindOmega_book P.par) lay (by rw [parK1_sent]; exact hl) q hq
  rw [parK1_sent] at h
  exact h

/-- **BookKept at K14's two sendings, under the one equation on the data, and (R) under the fence.** -/
theorem bookKept_at_send_of_data (lo : ℕ) (low : Tree → Option ℕ) (rec : P₁ × St → ℕ → ρ) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b = b2 ∨ b = b5) (q : Piece C F (P₁ × St) Unit W)
    (hqb : q.b = (below b).lift Prod.snd fun (t : P₁ × St) s => (t.1, s))
    (hD : q.trees = (q.b.rounds.map (·.entry.roots)).sum)
    (hR : ∀ a τ c,
      FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
        (fun t => t.2.roots)) q.base a →
      q.ior.red.out a τ = some c → ∀ o, o < a.1.2.st.oracles.size → rec c.1 o = rec a.1 o) :
    BookKept (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book) (fun t => t.2.roots))
      rec q := by
  obtain ⟨n, Q, inFront, groups, behind, hbe, _, hbk⟩ := sends_are P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb
  refine bookKept_at_send_desc lo low rec P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb q hqb ?_ hR
  subst hbe
  refine hT_of_data P n Q inFront groups behind hbk q.trees ?_
  rw [hD, hqb]
  rfl

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.blocks_two
#print axioms Desc.K14.Law.Fence.seatedNew_sendAt
#print axioms Desc.K14.Law.Fence.seatedNew_u
#print axioms Desc.K14.Law.Fence.seatedNew_omega
#print axioms Desc.K14.Law.Fence.bookKept_at_send_of_data
