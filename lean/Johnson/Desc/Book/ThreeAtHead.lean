-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/ThreeAtHead.lean: three facts on the book at every reached last state of the first
chain, FROM THE ONE HEAD (`P5J.AtMg`, Johnson/P5J/AtMg.lean) at the concrete second hash function
and one general sentence on K2's texts: the book numbers its trees from 0 (`K12.Door.atFirstBook 0`)
· the book fits (`Sound.bookFitsB`) · the book has as many places as the statement has oracle
messages. One theorem. A joining.

Why. Row 0's law of the last table asks these three of the first chain's last state (its premise on
the book: Johnson/Desc/Book/LastBook.lean's `hB_of_facts` takes them). `Meaning.K2.five_at_end`
(Johnson/IMR/EndFive.lean) has them among five, and draws the third from a lemma on the book's
places that spends three premises more (what the sendings append · a test with code on the list of
rounds · that a list of places and shapes can be laid). The third alone is had without these: the
counts at every cut of the flat list (`Meaning.Carry.counts_at_cut`, Johnson/IMR/MsgsBehind.lean).

  `three_at_head`: h : `AtMg OnBytes.secondHashFunction Z D r Zp Np cF` · hT : `Meaning.Carry.K2Told` ⊢ at every
    p with `EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p`: the three. NO "no mark" IS ASKED.
    OFF THE HEAD: the scope · the files' reading · an opening · each sub-protocol of the first chain
    passes its test on the list of rounds.
    CALLED: `Meaning.K2.two_at_end` · `flat_358` · `counts_at_cut` · `K1.told_tenants_own`
    (Johnson/Desc/K1/Law/ToldCounts.lean: it is `K1Told`).

Limits. hT stays: a sentence on K2's list of a sending's oracle messages, with no letter of the
files: "the tenants told are as many as the messages announced". It is shown nowhere here. At
`OnBytes.secondHashFunction` alone; in scope alone. No example. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.IMR.EndFive
import Johnson.IMR.MsgsBehind
import Johnson.IMR.PlanOkFlat
import Johnson.Desc.K1.Law.ToldCounts
import Johnson.P5J.AtMg
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁ reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl}

/-- **The three facts on the book at the first chain's reached end, from the one head.** -/
theorem three_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hT : Meaning.Carry.K2Told) :
    ∀ p : ProofFile.InstPub × First.S, EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p →
      K12.Door.atFirstBook 0 p.2 = true ∧ Sound.bookFitsB p.2.book = true ∧
        p.2.book.place.size = p.2.st.oracles.size := by
  intro p hp0
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb := IM.blocksOk_of_planOk O h.laid.planOk
  have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := by
    intro b hb'
    unfold blocksOk at hb
    have h1 := List.all_eq_true.mp hb b hb'
    simp only [Bool.and_eq_true] at h1
    exact h1.1
  have hr : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) cF.blocksInOrder.length p := hp0
  obtain ⟨a1, a2⟩ := Meaning.K2.two_at_end O hp p hr
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  have hc := Meaning.Carry.counts_at_cut h.scope h.reads O
    (fun P hP => K1.told_tenants_own P hP) hT p.1 rs cols cF.blocksInOrder.length
    (Nat.le_of_eq (Meaning.K2.flat_358 h.scope O)) (fun b hb' => hp b (List.mem_of_mem_take hb'))
    _ f
  exact ⟨a1, a2, hc.2.1⟩

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.three_at_head
