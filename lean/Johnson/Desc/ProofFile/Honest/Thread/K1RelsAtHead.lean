-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1RelsAtHead.lean: two of the library's relations between the
verifier's states before and after a sending at a later moment of a segment (kind K1), at the first
chain's invariant at `lettersHead`, from the invariant before the step and the sub-protocol's
accepting step. They are hypotheses of the lemmas on the open item `forms m k r`
(`ridesPastAt_forms_rec_test`, FormsKinds.lean). No definition.

  * `K1.RecRides new s s'` (Johnson/Desc/K1/Law/PubAtLaterIndex.lean): by the library's
    `laterSend_blkL` (Johnson/Desc/K1/Law/CallsG.lean), off the decision's yes on two rounds.
  * `K1.ReadersStay` (same file): what the segment's readers answer before the step they answer
    after it, at every item `forms` that is open before the step. By the lemma of the authors of
    kind K1, `K1.readers_later_all` (Honest/K1/Law/PubBehindAtFifty.lean). Its side conditions are
    supplied as in these authors' own `pub_later_head` (same file).

  `k1_rels_behind`   at the sending of the reads (`d` false) or of the digits (`d` true) of segment
     `l`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemma takes the sub-protocol's step. The condition `RidesPastAt` has the clause of `keeps`
    alone: to serve there, the conclusion has to be a part of that clause.
  * The third relation that `ridesPastAt_forms_rec_test` asks, `K1.AheadMeets`, is not shown here.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.K1.Law.PubBehindAtFifty
import Johnson.Desc.K1.Law.CallsG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- After a sending at a later moment of segment `l`: the library's relation `RecRides` at the new
messages' numbers, and the readers' answers stay at every item `forms` that is open before it. -/
theorem k1_rels_behind {l : Nat} (hl : l < 25) (d : Bool) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[VerifiableInference.Desc.K1.noL l d]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (VerifiableInference.Desc.K1.noL l d) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    ∃ new, VerifiableInference.Desc.K1.RecRides new s s' ∧
      ∀ mm kk ρ, Item.forms mm kk ρ ∈ openAt linksFull (flatPlacesOf linksFull true)
          (VerifiableInference.Desc.K1.noL l d) →
        VerifiableInference.Desc.K1.ReadersStay h.𝔇.pubD mm kk ρ s s' := by
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hb : VerifiableInference.Desc.K1.noL l d ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, X₁, arrs, he, hu⟩ := VerifiableInference.Desc.K1.k01_flat h.scope h.reads O l hl d
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hblk)
  have hY := VerifiableInference.Desc.K1.yesOf_of_yes hu hyes m.st.input.x.pub
  obtain ⟨-, rs, gs, hfit, hd⟩ := id hY
  have hlen : (rs.map VerifiableInference.Desc.noDigest).length = 2 := by
    rw [List.length_map, VerifiableInference.Desc.Keeps.fit_length _ _ hfit,
      VerifiableInference.Desc.K1.two_blkL]
  have hLS := VerifiableInference.Desc.K1.laterSend_blkL Zp Bs.G₀ l d X₁ arrs s s' _ gs hlen hd
  refine ⟨_, hLS.2.1, fun mm kk ρ ho => ?_⟩
  obtain ⟨-, hSo, -⟩ := K1.sides_later_head h O
  exact (K1.readers_later_all h.𝔇 h.scope h.reads O (VerifiableInference.Desc.K1.hDlk_atAll h)
    (VerifiableInference.Desc.K1.hlk_atAll h) ((VerifiableInference.Desc.K1.sortB_iff _).1 hSo)
    (by rw [O.W]; exact ⟨rfl, rfl, rfl⟩) l hl d X₁ arrs (m.st.input.x.pub, s)
    (m.st.input.x.pub, s') hY
    (fun h1 h2 => VerifiableInference.Desc.K1.tablesOk_of_no _ _ _ _
      (VerifiableInference.Desc.K1.no_tables_342 h.scope h.reads O (m.st.input.x.pub, s)
        (by
          subst h1
          subst h2
          exact hR)))
    mm kk ρ
    (Or.inl (List.mem_append_right _
      (List.mem_flatMap.2 ⟨Item.forms mm kk ρ, ho, List.mem_singleton.2 rfl⟩)))).2

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1_rels_behind
