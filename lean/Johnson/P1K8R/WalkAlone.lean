-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WalkAlone.lean: THE WALK FROM A LOT's SUB-PROTOCOL TO WHAT THE SEATED LINK STATES, FOR
«EACH RUN OF CLAIMS COMMUTES WITH THE SMALLNESS TEST's DRAW» (RunBlind,
Johnson/Desc/First/K8/BlindReaders.lean; ClaimsBlind,
Johnson/Desc/First/Batch/Law/BlindRunsK3.lean). General in the kind. A joining of three groups of
rules.
  LeavesOut b         every run of claims that b states leaves what goes on to the later chains (S.out).
  claimsBlind_alone   b is the lot's b', alone, under a name at an address (IM.LaidAlone ProofFile.sameReply): ClaimsBlind b' · LeavesOut b' ⟹ ClaimsBlind b: by IM.claims_alone (Johnson/IMR/SeatForm.lean: the seated runs are the lot's, name by name, each behind the guard) and runBlind_guarded (Johnson/Desc/First/Batch/Law/BlindRunsK3.lean); the guard ProofFile.sameReply reads S.out.reply alone.
  states_blind        what sub-protocol number i of a link states (K9.statesOfLink), where that sub-protocol is in hand.
  walk_hear           AT THE FIRST CHAIN THAT THE DESCRIPTION's OWN MAKER RETURNS (ProofFile.chainBy at ProofFile.pureSeat): at link l, hearing sub-protocol number i (1 ≤ i ≤ 8) of a kind other than K9 | K10: every lot's sub-protocol at that address is ClaimsBlind and LeavesOut ⟹ there is the link Lk := c.links[l], and every run that its sub-protocol number i states is RunBlind: by IM.chain_hear_alone.
WHAT IS STILL BETWEEN THIS AND mg_readers' PREMISE (Johnson/P1K8R/ReadersAtMg.lean) AT THE CLOSED CONSTANT (P5J.mgAtAll, Johnson/P5J/MgAtAll.lean): (1) ProofFile.linkAt Zp l IS c.links[l]? (ProofFile's law on its own term) (2) for each address: the lot's sub-protocol IS the maker's text, which is ClaimsBlind (in other files, not named here) and LeavesOut (typed by nobody).
LIMITS. A rule over letters: no sub-protocol is shown ClaimsBlind or LeavesOut here. No soundness. Nothing on hiding.
-/
import Johnson.IMR.LaidFirst
import Johnson.Desc.First.Batch.Law.BlindRunsK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8 (RunBlind ClaimsBlind runBlind_guarded)
open VerifiableInference.Desc.K9 (statesOfLink)
open ProofFile (Cl)

/-- Every run of claims that the sub-protocol states leaves what goes on to the later chains. -/
def LeavesOut (b : Block S Cl) : Prop := ∀ c ∈ b.claims, ∀ n s z, c.2 n s = .ok z → z.2.out = s.out

/-- **A lot's sub-protocol as it stands in the first chain, alone**: its runs commute with the draw
where the lot's own do and leave what goes on to the later chains. -/
theorem claimsBlind_alone {b b' : Block S Cl} {name : String} {a : Place}
    (h : IM.LaidAlone ProofFile.sameReply b b' name a) (hb : ClaimsBlind b') (ho : LeavesOut b') :
    ClaimsBlind b := by
  intro c hc n
  rw [IM.claims_alone h] at hc
  obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
  exact runBlind_guarded ProofFile.sameReply
    (fun s z e => by
      unfold ProofFile.sameReply
      rw [e]
      simp)
    (c₀.2 n) (hb c₀ h₀ n) (ho c₀ h₀ n)

/-- What sub-protocol number i of a link states, where that sub-protocol is in hand. -/
theorem states_blind {Lk : Link S Cl} {i : ℕ} {b : Block S Cl} (h : Lk.hear[i]? = some b)
    (hb : ClaimsBlind b) : ∀ ρ ∈ statesOfLink Lk i, RunBlind (ρ.2 0) := by
  intro ρ hρ
  unfold statesOfLink at hρ
  rw [h] at hρ
  exact hb ρ hρ 0

/-- **THE WALK**: at the first chain that the description's own maker returns: what sub-protocol
number i of link l states commutes with the draw, where every lot's sub-protocol at that address
does and leaves what goes on to the later chains. -/
theorem walk_hear {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) (hk9 : k ≠ KindName.K9) (hk10 : k ≠ KindName.K10)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9)
    (H : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∀ b' ∈ L.blocks B.G₀,
      b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } →
      ClaimsBlind b' ∧ LeavesOut b') :
    ∃ Lk, c.links[l]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk i, RunBlind (ρ.2 0) := by
  obtain ⟨Lk, b, e1, e2, sp, _, L, hL, b', hb', _, ep, ha⟩ :=
    IM.chain_hear_alone hB hb hc l sub hl i k hk hk9 hk10 hi
  exact ⟨Lk, e1, states_blind e2 (claimsBlind_alone ha (H L hL b' hb' ep).1 (H L hL b' hb' ep).2)⟩

end P1K8T

#print axioms P1K8T.claimsBlind_alone
#print axioms P1K8T.walk_hear
