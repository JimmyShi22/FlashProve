-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/KeptCommit.lean: a yes of a commitment's block at the first chain's state keeps
all that `KeptAll` (Reads/RowAtSeat.lean) asks.

Why. `row_at_seat` takes `KeptAll` from the state behind the fifth place of the head's link to the
state at which the run "policy" is run. One of the four decisions between is the digits' commitment,
a block of this make (`K1.commitAtS`, Johnson/Desc/K1/AtS.lean).

What is shown. Steps: they speak of the written texts `K1.commitAtS`, `K1.commitOwn`
(Johnson/Desc/K1/Own.lean) and `L3.commitStep`, `L3.commitBehind`, `L3.commitOne`
(Johnson/Top/H0/L3/Frame.lean).
  `rootTaken_cols`: noting that an array's commitment is received leaves every array's number of
    columns.
  `commitOne_cols`, `commitFold_cols`, `commitBehind_cols`, `commitStep_cols`: so do these texts.
  `keptAll_refl`, `keptAll_trans`: tools.
  `keptAll_commit`: **a yes of `K1.commitAtS` gives `KeptAll`**, at every number of an array.

Limits. One of the four decisions and none of the four runs that stand between. Nothing on
soundness.


-/
import Johnson.Desc.Reads.RowAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (Fork LinkCtx ChainCheck)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok)

/-- The number of columns of array i of a ledger, if the array is there. -/
def colsAt (F : Fork) (i : ℕ) : Option ℕ := (F.trees[i]?).map (·.K)

theorem rootTaken_cols (F : Fork) (t w i : ℕ) : colsAt (F.rootTaken t w) i = colsAt F i := by
  unfold colsAt Fork.rootTaken
  show ((F.trees.modify t fun X => { X with root := some w })[i]?).map (·.K) = _
  rw [Array.getElem?_modify]
  split
  · cases F.trees[i]? <;> rfl
  · rfl

theorem commitOne_cols {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F')
    (i : ℕ) : colsAt F' i = colsAt F i := by
  unfold L3.commitOne at h
  dsimp only at h
  split at h <;> split at h
  all_goals first
    | (rw [← Except.ok.inj h]
       exact rootTaken_cols F t 0 i)
    | cases h

theorem commitFold_cols {L : LinkCtx} (i : ℕ) : ∀ (ts : List ℕ) {F F' : Fork},
    ts.foldlM (L3.commitOne L) F = .ok F' → colsAt F' i = colsAt F i
  | [], F, F', h => by rw [← Except.ok.inj h]
  | t :: ts, F, F', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := ReadsQuiet.bind_ok h
    exact (commitFold_cols i ts h2).trans (commitOne_cols h1 i)

theorem commitBehind_cols {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) (i : ℕ) : colsAt F' i = colsAt F i := by
  unfold L3.commitBehind at h
  obtain ⟨F1, h1, h2⟩ := ReadsQuiet.bind_ok h
  split at h2
  · have e := congrArg Prod.snd (Except.ok.inj h2)
    have e' : F1 = F' := e
    rw [← e']
    exact commitFold_cols i ts h1
  · cases h2

theorem commitStep_cols {Wt : Type} {send : L3.Send Wt} {ts : List ℕ} {s s' : L3.St Wt}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') (i : ℕ) :
    colsAt s'.F i = colsAt s.F i := by
  unfold L3.commitStep at h
  obtain ⟨_, _, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨⟨check, w⟩, _, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨⟨L', F'⟩, h3, h⟩ := ReadsQuiet.bind_ok h
  rw [← Except.ok.inj h]
  exact commitBehind_cols h3 i

theorem keptAll_refl (i : ℕ) (s : S) : KeptAll i s s :=
  ⟨rfl, rfl, fun o ho => ⟨o, ho, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem keptAll_trans {i : ℕ} {s s' s'' : S} (h1 : KeptAll i s s') (h2 : KeptAll i s' s'') :
    KeptAll i s s'' := by
  refine ⟨h2.req.trans h1.req, h2.reply.trans h1.reply, fun o ho => ?_⟩
  obtain ⟨o', ho', a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1.own o ho
  obtain ⟨o'', ho'', b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2.own o' ho'
  exact ⟨o'', ho'', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8⟩

/-- **A yes of a commitment's block gives KeptAll.** -/
theorem keptAll_commit {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) P link moment arrays).decide s rs gs =
      .ok s') (i : ℕ) : KeptAll i s s' := by
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
      have hcols : colsAt y.held.F i = colsAt F0 i := by
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
              exact commitStep_cols hs i
        · cases hb
      rw [← e]
      refine ⟨?_, ?_, fun o ho => ?_⟩
      · unfold S.putFork S.putLink VerifiableInference.Desc.K1.laid
        split <;> (try split) <;> (try split) <;> (try split) <;> rfl
      · unfold S.putFork S.putLink VerifiableInference.Desc.K1.laid
        split <;> (try split) <;> (try split) <;> (try split) <;> rfl
      · have hop : o.opened = true ∧ F0 = o.F := by
          unfold S.fork? at hF
          rw [ho] at hF
          have hF' : (if o.opened = true then some o.F else none) = some F0 := hF
          by_cases hop : o.opened = true
          · rw [if_pos hop] at hF'
            exact ⟨hop, (Option.some.inj hF').symm⟩
          · rw [if_neg hop] at hF'
            cases hF'
        refine ⟨{ { o with L := y.held.L } with F := y.held.F }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, ?_⟩
        · have h1 : (VerifiableInference.Desc.K1.laid s y.held.w).here = .head o := ho
          unfold S.putFork S.putLink
          simp [h1, hop.1]
        · have := hcols
          rw [hop.2] at this
          exact this
  · cases h

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.rootTaken_cols
#print axioms VerifiableInference.Reads.AtSeat.commitOne_cols
#print axioms VerifiableInference.Reads.AtSeat.commitFold_cols
#print axioms VerifiableInference.Reads.AtSeat.commitBehind_cols
#print axioms VerifiableInference.Reads.AtSeat.commitStep_cols
#print axioms VerifiableInference.Reads.AtSeat.keptAll_refl
#print axioms VerifiableInference.Reads.AtSeat.keptAll_trans
#print axioms VerifiableInference.Reads.AtSeat.keptAll_commit
