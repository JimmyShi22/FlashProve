-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaysS.lean: THE FRAME's SENTENCE "IT PLAYS", ASKED FROM THE PAIR
OF A THREAD AND "THE PROVER's RUN STANDS WHERE THE FRAME's OWN PLAY STANDS" (PlaysS,
Honest/Thread/PaysS.lean, at PlayedTo, Honest/Small/PlayedTo.lean), AT A MEMBER OF THE KIND K1; and
what the thread's table at the member's new trees then is. Statements and proofs. General in the
thread.

  playsS_k1_by_play   PlaysS T (PlayedTo T start) b. Of this kind's: the member, its shape, the half
                and the public test sendFits. The four other premises are playsS_by_play's own, on
                the whole chain: the thread's own trees' tables are tableBy; each is fixed by the
                challenges in front of the round that sends it; every sub-protocol lists as many
                oracle messages as its rounds count roots; the whole chain's steps are laid
  k1_table_by_play   under the same eight premises, and where the job's data reads of Front what was
                heard alone: behind the member's rounds of a played run, the thread's table at each
                of the member's trees has scriptTable's place (Honest/K1/ScriptAt.lean) and is the
                same as its table in Table.same's sense, at the coins lent and the challenges heard
                in front of the member

WHAT IS SENT, NOT WHAT IS SHOWN. These tables are whole oracle messages: what is SENT; a verifier is
shown a root and the opened columns.

WHY NOT AN EQUATION OF FUNCTIONS. tableBy plays the chain along the list that it is handed: at a
list too short for the play to reach the tree, or along which a move in front refuses, it is its
default, one value at all coins; scriptTable holds the part's coins. The thread reads a table at one
list alone (Thread.tableAt): the law speaks there.

Limits. The premises are met together at no thread here. "It plays" is the frame's name for a
premise's form: IT IS NO COMPLETENESS, and it does not say that the prover's messages are accepted.
THE PAIR IN FRONT IS A PREMISE: nothing bars that it holds of no run; start and dflt are free
letters. tableBy's default IS the thread's table wherever the play does not reach the tree or no
half has sent it; WHETHER A PLAY ENDS IN FRONT CAN HANG ON THE INPUT (a part in front with a stop
that reads it): k1_table_by_play speaks at the stand right behind the member alone. That the book
lends the part its coins is a premise. Nothing on how a coin is made. On hiding nothing is said.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Plays
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.Small.PlayedTo
import Johnson.Desc.ProofFile.Honest.Thread.Sent
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open ProofFile.Honest.Small (PlayedTo tableBy playsS_by_play trees_by_play sentIn Listed)

variable {S Cl V W X Xi Pb : Type} {Bk : ProverCoinCounts}

/-- **IT PLAYS**, from the pair with PlayedTo, at tables that are the frame's own play's. Of this
kind's: the member, its shape, the half and sendFits ALONE. -/
theorem playsS_k1_by_play (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (dflt : Place × Table) (b : Nat)
    (blk : Block S Cl) (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (hblk : T.bs[b]? = some blk)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (hf : sendFits J.P J.ride = true)
    (htab : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h)
    (hfix : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hlist : ∀ x ∈ T.bs, Listed x)
    (hall : ∀ (k : Coins Bk) (w : W), ∃ Lall,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall) :
    PlaysS T (PlayedTo T start) b :=
  playsS_by_play T start dflt htab hfix hlist hblk (g := placeHalf wit J)
    (by
      rw [hsh.1]
      exact hh) hall
    fun k _ m E ds l _ hd _ hl =>
      (k1_moved T blk wit J hsh hh hf k m E ds l hd hl).imp fun _ h => ⟨[], h⟩

/-- **THE THREAD's TABLE AT THE MEMBER's TREES**: under playsS_k1_by_play's premises, and where the
job's data reads of Front what was heard alone: behind the member's rounds of a played run, the
thread's table at each of the member's trees IS THE SAME, IN Table.same's SENSE, AS scriptTable at
the coins lent and the challenges heard in front of the member. OF WHAT IS SENT AS AN ORACLE, WHOLE:
a verifier is shown a root and the opened columns. -/
theorem k1_table_by_play (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (dflt : Place × Table) (b : Nat)
    (blk : Block S Cl) (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (hblk : T.bs[b]? = some blk)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (hf : sendFits J.P J.ride = true)
    (htab : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h)
    (hfix : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hlist : ∀ x ∈ T.bs, Listed x)
    (hall : ∀ (k : Coins Bk) (w : W), ∃ Lall,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall)
    (own₀ : X)
    (ho : ∀ w (fr fr' : Front X), fr.heard = fr'.heard → J.data w fr = J.data w fr') :
    ∀ k s m E ds y cols c, ThrS T (PlayedTo T start) b k s m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.P.place (placeHalf (V := V) wit J).parts 0 =
        .ok c →
      ∀ τ, τ < J.P.trees.length →
        (scriptTable J own₀ τ c.1.1 (wit m.st.input) m.st.heard).1 =
            (T.tableAt (.own (treesTo T.bs b + τ)) k y.2).1 ∧
          (scriptTable J own₀ τ c.1.1 (wit m.st.input) m.st.heard).2.same
            (T.tableAt (.own (treesTo T.bs b + τ)) k y.2).2 = true := by
  intro k s m E ds y cols c hT hd hM hc τ hτ
  obtain ⟨c', d₀, d₁, hc', -, -, hy, -, -⟩ :=
    k1_moved_term T blk wit J hsh hh hf k m E ds y cols hd hM
  have ec : c' = c := Except.ok.inj (hc'.symm.trans hc)
  subst ec
  have hsent : E.sent = treesTo T.bs b := hT.1.2.2.2.2.1.2.2.1
  -- the tables of the term
  have htabs : tablesOf y.1 =
      (treeTables J.P (J.rows c'.1.1 m.shown (m.st.narrow wit id) 0)).map
        fun u => some (J.P.place, u) := by
    rw [hy]
    simp [tablesOf, playedK1, Function.comp_def]
  -- the tree at hand behind the member's rounds
  have hr : rowsLaid J own₀ c'.1.1 (wit m.st.input) m.st.heard =
      J.rows c'.1.1 m.shown (m.st.narrow wit id) 0 := by
    have q := rowsLaid_part J own₀ ho c'.1.1 m.shown (m.st.narrow wit id) 0
    rw [Nat.sub_zero, List.take_length] at q
    exact q
  have hlen : τ < (treeTables J.P (J.rows c'.1.1 m.shown (m.st.narrow wit id) 0)).length := by
    rw [treeTables_length]
    exact hτ
  have htree : (E.add y.1).tree (.own (treesTo T.bs b + τ)) =
      some (scriptTable J own₀ τ c'.1.1 (wit m.st.input) m.st.heard) := by
    rw [← hsent, Env.add_own, htabs, List.getElem?_map, List.getElem?_eq_getElem hlen]
    unfold scriptTable
    rw [hr, List.getElem?_eq_getElem hlen]
    rfl
  obtain ⟨Lall, hAll⟩ := hall k m.st.input
  have hsome : ∀ t ∈ tablesOf y.1, t.isSome = true := by
    rw [htabs]
    intro t ht
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
    rfl
  have hTr := trees_by_play T start dflt htab hfix hlist hblk hT hM hAll hsome
  -- the tree is new at hand behind the member
  have hnone : E.tree (.own (treesTo T.bs b + τ)) = none :=
    hT.1.2.2.2.2.1.2.2.2.1 _ (by rw [hsent]; exact Nat.le_add_right _ _)
  have hold : Fmt.TreeSource.own (treesTo T.bs b + τ) ∉ T.hand b := by
    intro hin
    have q := hT.1.1.2 _ hin
    unfold Thread.handAt at q
    rw [hnone] at q
    cases q
  have hcount : (blk.oracles.flatMap id).length = J.P.trees.length := by
    rw [hsh.2.2]
    simp [K1.oracles]
  have hnew : Fmt.TreeSource.own (treesTo T.bs b + τ) ∈ T.hand (b + 1) := by
    unfold Thread.hand
    refine List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_range.2 ?_, rfl⟩)
    rw [treesTo_succ hblk, hcount]
    exact Nat.add_lt_add_left hτ _
  have hfresh : Fmt.TreeSource.own (treesTo T.bs b + τ) ∈ T.fresh b := by
    unfold Thread.fresh
    refine List.mem_filter.2 ⟨hnew, ?_⟩
    simpa using hold
  have q := hTr _ hfresh
  unfold Thread.handAt at q
  rw [htree] at q
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at q
  exact q

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.playsS_k1_by_play
#print axioms ProofFile.Honest.K1.k1_table_by_play
