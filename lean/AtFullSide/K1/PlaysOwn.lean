-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/PlaysOwn.lean: "it plays" (PlaysS) at a member of the kind K1, at any thread and at
every second condition Said, where the thread's tables of the member's own trees are the lot's
treeTbl.

  playsS_k1_own   of the kind: the member, its shape, the half, sendFits, and that the job's data
                  read of what stands in front what was heard alone. Of the thread: OwnTrees at
                  the member, with every tree fixed by the challenges in front of the member

Why. playsS_k1_by_play (Honest/K1/PlaysS.lean) asks PlayedTo, which the term's letters do not
give, and the two equations htab, hfix, of which hfix holds at no Script.ofLots over a chain with a
round. Of all that, the clause on the member's new trees alone needs the thread's tables, and only
at the member's own trees: OwnTrees says that, and ofLots_ownTrees gives it at a Script.ofLots.

Limits.
- "It plays" is the frame's name for a premise's form. It is no completeness.
- The pair ThrS is a premise: nothing here says that it holds of any stand.
- Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaysS
import Johnson.Desc.ProofFile.Honest.K1.ScriptLendRow
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open ProofFile.Honest.FirstThread (OwnTrees)

variable {S Cl V W X Xi Pb : Type} {Bk : ProverCoinCounts}

/-- **IT PLAYS, AT EVERY Said.** General in the thread. -/
theorem playsS_k1_own (T : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (blk : Block S Cl)
    (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) (own₀ : X)
    (hblk : T.bs[b]? = some blk)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (hf : sendFits J.P J.ride = true)
    (ho : ∀ w (fr fr' : Front X), fr.heard = fr'.heard → J.data w fr = J.data w fr')
    (hown : OwnTrees T b J.P.trees.length (treeTbl T.chain wit J own₀) fun _ => 0) :
    PlaysS T Said b := by
  intro blk' hblk' k s m E ds l hT hd _ hl
  obtain rfl : blk' = blk := Option.some.inj (hblk'.symm.trans hblk)
  obtain ⟨y, hM⟩ := k1_moved T blk' wit J hsh hh hf k m E ds l hd hl
  refine ⟨y, [], hM, ?_⟩
  obtain ⟨c, d₀, d₁, hc, -, -, hy1, hyi, hyh⟩ :=
    k1_moved_term T blk' wit J hsh hh hf k m E ds y [] hd hM
  have hcut := cut_of_lendPlace _ k T.chain wit J c hc
  have hsent : E.sent = treesTo T.bs b := hT.1.2.2.2.2.1.2.2.1
  have hcount : (blk'.oracles.flatMap id).length = J.P.trees.length := by
    rw [hsh.2.2]
    simp [K1.oracles]
  have htabs : tablesOf y.1 =
      (treeTables J.P (J.rows c.1.1 m.shown (m.st.narrow wit id) 0)).map
        fun u => some (J.P.place, u) := by
    rw [hy1]
    simp [tablesOf, playedK1, Function.comp_def]
  have hr : rowsLaid J own₀ c.1.1 (wit m.st.input) m.st.heard =
      J.rows c.1.1 m.shown (m.st.narrow wit id) 0 := by
    have q := rowsLaid_part J own₀ ho c.1.1 m.shown (m.st.narrow wit id) 0
    rw [Nat.sub_zero, List.take_length] at q
    exact q
  have hlenH : m.st.heard.length = T.front + roundsTo T.bs b := by
    have q := drawsFit_length _ _ hT.1.2.1
    simpa [Thread.front, roundsTo, List.length_append] using q
  intro σ hσ
  have hin : σ ∈ T.hand (b + 1) := (List.mem_filter.1 hσ).1
  have hno : σ ∉ T.hand b := by
    have q := (List.mem_filter.1 hσ).2
    simpa using q
  unfold Thread.hand at hin
  rcases List.mem_append.1 hin with h1 | h1
  · exact absurd (List.mem_append_left _ h1) hno
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h1
  have ht' : t < treesTo T.bs (b + 1) := List.mem_range.1 ht
  rw [treesTo_succ hblk, hcount] at ht'
  have hge : treesTo T.bs b ≤ t := by
    by_contra hlt
    exact hno (List.mem_append_right _
      (List.mem_map.2 ⟨t, List.mem_range.2 (Nat.lt_of_not_le hlt), rfl⟩))
  obtain ⟨τ, rfl⟩ := Nat.exists_eq_add_of_le hge
  have hτ : τ < J.P.trees.length := Nat.lt_of_add_lt_add_left ht'
  have hlen : τ < (treeTables J.P (J.rows c.1.1 m.shown (m.st.narrow wit id) 0)).length := by
    rw [treeTables_length]
    exact hτ
  have htree : (E.add y.1).tree (.own (treesTo T.bs b + τ)) =
      some (scriptTable J own₀ τ c.1.1 (wit m.st.input) m.st.heard) := by
    rw [← hsent, Env.add_own, htabs, List.getElem?_map, List.getElem?_eq_getElem hlen]
    unfold scriptTable
    rw [hr, List.getElem?_eq_getElem hlen]
    rfl
  have hat : T.tableAt (.own (treesTo T.bs b + τ)) k y.2 =
      scriptTable J own₀ τ c.1.1 (wit m.st.input) m.st.heard := by
    unfold Thread.tableAt
    rw [hown.fixed τ hτ, hown.table τ hτ, hyi, hyh, Nat.add_zero, ← hlenH, List.take_left']
    · exact treeTbl_some T.chain wit J own₀ τ k c.1.1 hcut _ _
    · rfl
  unfold Thread.handAt
  rw [htree, hat]
  simp [Table.same_refl]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.playsS_k1_own
