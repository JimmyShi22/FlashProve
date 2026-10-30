-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/KeptMoreCommit.lean: a commitment's sub-protocol at the first chain's state keeps
all that the readers of the output head's four runs of claims read.

Why. `KeptMore` (Reads/ReaderFwd.lean) and `KeptJoin` (Reads/JoinFwd.lean) are premises of the laws
on the readers' one direction. In the output head's segment two commitments stand between the output
head's own sub-protocol and the batching. A commitment (`K1.commitAtS`, Johnson/Desc/K1/AtS.lean)
writes the ledger in one way alone: it notes at an array that its commitment was received.

What is stated and shown.
  `LedgerKept F G`: G is later than F (`OnBytes.PscRun.Later`); every array has as many own rows;
    the list of owed claims is the same. With `LedgerKept.refl`, `LedgerKept.trans`.
  `rootTaken_kept`, `commitOne_kept`, `commitFold_kept`, `commitBehind_kept`, `commitStep_kept`:
    along the commitment's own text.
  `keptJoin_commit`: **where a commitment's sub-protocol accepts: `KeptJoin` from the state in front
    to the state behind.** So `KeptMore` too.

Limits. `Rides` across a commitment is not shown here: the statement and the book grow there.
Nothing on soundness.


-/
import Johnson.Desc.Reads.JoinFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes.Model (Fork LinkCtx ChainCheck)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (K3.unpaid)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok)
open VerifiableInference.Reads.AtSeat (keptAll_commit)

/-- What a step must keep of the ledger. -/
structure LedgerKept (F G : Fork) : Prop where
  later : Later F G
  rows : ∀ t : ℕ, (G.trees[t]?).map (·.R) = (F.trees[t]?).map (·.R)
  owed : G.owed = F.owed

theorem LedgerKept.refl (F : Fork) : LedgerKept F F := ⟨Later.refl F, fun _ => rfl, rfl⟩

theorem LedgerKept.trans {F G H : Fork} (h : LedgerKept F G) (h' : LedgerKept G H) :
    LedgerKept F H :=
  ⟨h.later.trans h'.later, fun t => (h'.rows t).trans (h.rows t), h'.owed.trans h.owed⟩

theorem rootTaken_kept (F : Fork) (t w : ℕ) : LedgerKept F (F.rootTaken t w) := by
  refine ⟨⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩, fun i => ?_, rfl⟩
  unfold Fork.rootTaken
  show ((F.trees.modify t fun X => { X with root := some w })[i]?).map (·.R) = _
  rw [Array.getElem?_modify]
  split
  · cases F.trees[i]? <;> rfl
  · rfl

theorem commitOne_kept {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F') :
    LedgerKept F F' := by
  unfold L3.commitOne at h
  dsimp only at h
  split at h <;> split at h
  all_goals first
    | (rw [← Except.ok.inj h]
       exact rootTaken_kept F t 0)
    | cases h

theorem commitFold_kept {L : LinkCtx} : ∀ (ts : List ℕ) {F F' : Fork},
    ts.foldlM (L3.commitOne L) F = .ok F' → LedgerKept F F'
  | [], F, F', h => by
    rw [← Except.ok.inj h]
    exact LedgerKept.refl F
  | t :: ts, F, F', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := ReadsQuiet.bind_ok h
    exact (commitOne_kept h1).trans (commitFold_kept ts h2)

theorem commitBehind_kept {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) : LedgerKept F F' := by
  unfold L3.commitBehind at h
  obtain ⟨F1, h1, h2⟩ := ReadsQuiet.bind_ok h
  split at h2
  · have e := congrArg Prod.snd (Except.ok.inj h2)
    have e' : F1 = F' := e
    rw [← e']
    exact commitFold_kept ts h1
  · cases h2

theorem commitStep_kept {Wt : Type} {send : L3.Send Wt} {ts : List ℕ} {s s' : L3.St Wt}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') : LedgerKept s.F s'.F := by
  unfold L3.commitStep at h
  obtain ⟨_, _, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨⟨check, w⟩, _, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨⟨L', F'⟩, h3, h⟩ := ReadsQuiet.bind_ok h
  rw [← Except.ok.inj h]
  exact commitBehind_kept h3

/-- **Where a commitment's sub-protocol accepts.** -/
theorem keptJoin_commit {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) P link moment arrays).decide s rs gs =
      .ok s') (i : ℕ) : KeptJoin i s s' := by
  have kA := keptAll_commit P link moment arrays h i
  unfold VerifiableInference.Desc.K1.commitAtS at h
  dsimp only at h
  split at h
  · rename_i L0 F0 tl0 hL hF htl
    cases hb : (VerifiableInference.Desc.K1.commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := VerifiableInference.Desc.K1.owedOf s
          held := { L := L0, F := F0, tl := tl0, w := VerifiableInference.Desc.K1.stateOf s () } }
        rs gs with
    | error e =>
      rw [hb] at h
      cases h
    | ok y =>
      rw [hb] at h
      have e : ((VerifiableInference.Desc.K1.laid s y.held.w).putLink y.held.L).putFork y.held.F =
          s' := Except.ok.inj h
      have hk : LedgerKept F0 y.held.F := by
        unfold VerifiableInference.Desc.K1.commitOwn at hb
        dsimp only at hb
        split at hb
        · split at hb
          · cases hb
          · rename_i ts
            cases hs : L3.commitStep (VerifiableInference.Desc.K1.laterOwn P
                (VerifiableInference.Desc.K1.owedOf s)) ts
                { L := L0, F := F0, tl := tl0, w := VerifiableInference.Desc.K1.stateOf s () }
                rs with
            | error e =>
              rw [hs] at hb
              cases hb
            | ok x =>
              rw [hs] at hb
              rw [← Except.ok.inj hb]
              exact commitStep_kept hs
        · cases hb
      have key : ∀ o o' : HeadOwn, s.here = .head o → s'.here = .head o' →
          o' = { { o with L := y.held.L } with F := y.held.F } ∧ F0 = o.F := by
        intro o o' ho ho'
        have hop : o.opened = true ∧ F0 = o.F := by
          unfold S.fork? at hF
          rw [ho] at hF
          have hF' : (if o.opened = true then some o.F else none) = some F0 := hF
          by_cases hop : o.opened = true
          · rw [if_pos hop] at hF'
            exact ⟨hop, (Option.some.inj hF').symm⟩
          · rw [if_neg hop] at hF'
            cases hF'
        have h1 : (VerifiableInference.Desc.K1.laid s y.held.w).here = .head o := ho
        have h2 : s'.here = .head { { o with L := y.held.L } with F := y.held.F } := by
          rw [← e]
          unfold S.putFork S.putLink
          simp [h1, hop.1]
        rw [h2] at ho'
        exact ⟨(VerifiableInference.Desc.First.Here.head.inj ho').symm, hop.2⟩
      refine ⟨⟨kA, fun o o' ho ho' => ?_, fun o o' ho ho' => ?_, fun o o' ho ho' => ?_⟩,
        fun o o' g ho ho' _ hu => ?_⟩
      · rw [(key o o' ho ho').1]
      · obtain ⟨e1, e2⟩ := key o o' ho ho'
        rw [e1, ← e2]
        exact hk.later
      · obtain ⟨e1, e2⟩ := key o o' ho ho'
        rw [e1, ← e2]
        exact hk.rows
      · obtain ⟨e1, e2⟩ := key o o' ho ho'
        rw [e1]
        unfold K3.unpaid at hu ⊢
        show ((y.held.F.owed[g.owedJoin]?).map (·.added) != some true) = true
        rw [hk.owed, e2]
        exact hu
  · cases h

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.LedgerKept.refl
#print axioms VerifiableInference.Reads.Pass.LedgerKept.trans
#print axioms VerifiableInference.Reads.Pass.rootTaken_kept
#print axioms VerifiableInference.Reads.Pass.commitOne_kept
#print axioms VerifiableInference.Reads.Pass.commitFold_kept
#print axioms VerifiableInference.Reads.Pass.commitBehind_kept
#print axioms VerifiableInference.Reads.Pass.commitStep_kept
#print axioms VerifiableInference.Reads.Pass.keptJoin_commit
