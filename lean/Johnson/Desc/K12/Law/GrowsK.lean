-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/GrowsK.lean: the five plain functions that the proximity test (the kind K12) is
made of only grow the statement.

`Grows` (Johnson/Desc/Grows.lean): the same codes; no group and no message is dropped or changes its
number; a group keeps its codes and members, and a mark inRun is not taken back; a message keeps its
shape and the groups that it names, and a mark sampled is not taken back. Each theorem here is
general: every state, every target, every list of other messages, either flag.
  `batE_grows`: the batching: the group is begun.
  `foldE_grows`: the fold, both arms: the mask enters, or has come; it is spent.
  `tailB_grows`, `switchBehind_grows`, `switchE_grows`: the switch: the sending
    (Johnson/Desc/K12/Law/SendGrows.lean); the new message's ledger is shut; it joins; the kept
    members join (the loop, for every target); the rows are added.
  `behind_grows`: the last lines of the code switch's test, at parts whose switch only hands on: the
    group is begun.
  `baseE'_grows`: the base case: the masking message is spent.
  `plainGrow_five`: the five together, field by field in the words of the record PlainGrow of
    a file of this project that is not in this repository (K12FrameKeeps.lean): that record is not
    in this library and is not compiled here.
Every write of the statement in the five goes through a plain change that Grows.lean names (begun,
stSent, a change of one message, joined, withRow); no other write was found.
It stands over Johnson/Desc/K12/Law/OutK.lean and OutK2.lean (bat_st, foldD_state, baseEW_state,
spendPlain_form) and SwUnfold.lean (joinS_ok, addRowS_ok, beginRunE_ok, askOwedE_ok,
switchBehind_eq, tailB).
Limits: it does not say what a yes is worth, and nothing on rows, ledgers or pads (`Grows` leaves
them out). The kind lays the mark inRun: on the group under test at the batching, and on each group
that a fold makes at the batching behind its switch; which, to the letter: OutK2.begunG and
OutK2.groupsNew. No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.OutK2
import Johnson.Desc.GrowsGround
import Johnson.Desc.K12.Law.SendGrows

set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Test (CsParts csTest)
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)

/-- (1) The batching. -/
theorem batE_grows (g : ℕ) (s : H2K.PS) (x : (GroupRow × GroupLayout) × H2K.PS)
    (h : H2K.batE g s = .ok x) : Grows s.d.st x.2.d.st := by
  unfold H2K.batE at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨row, L, S'⟩, hb, h⟩ := bind_ok h
    cases h
    obtain ⟨G, _, rfl⟩ := bat_st _ _ _ _ _ _ _ (mapError_ok hb)
    exact grows_begun _ _ _
  · cases h

/-- (2) The fold, both arms. -/
theorem foldE_grows (F : FoldShape) (row : GroupRow) (m : Option ℕ) (s : H2K.PS)
    (x : SingleRows × H2K.PS) (h : H2K.foldE F row m s = .ok x) : Grows s.d.st x.2.d.st := by
  unfold H2K.foldE at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨rows', d'⟩, hf, h⟩ := bind_ok h
  cases h
  obtain ⟨id, d1, hcase, hsp⟩ := foldD_state _ _ _ _ _ _ _ _ _ (mapError_ok hf)
  have h2 := Ground.spendAsMaskP_grows _ _ _ hsp
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact h2
  · exact (Ground.recvP_grows _ _ _ _ _ hr).trans h2

/-- (4) csTest's last lines, at parts whose switch only hands on what the switch before has
returned. -/
theorem behind_grows (out : Switched) (theta : E) (old : SingleRows) (X : SwitchTarget) (grp : ℕ)
    (o : Array OracleNotice) (s : H2K.PS) (x : (Switched × GroupRow × GroupLayout) × H2K.PS)
    (h : csTest { H2K.csParts with switch := fun _ _ _ _ _ s => some ((out, theta), s) } old X grp
      o s = some x) : Grows s.d.st x.2.d.st := by
  unfold VerifiableInference.Desc.Test.csTest at h
  dsimp only at h
  split at h
  · cases h
  · rename_i run s2 hb
    split at h
    · cases h
    · rename_i s3 ha
      split at h
      · cases h
      · cases h
        obtain ⟨G, lay, _, _, _, a4⟩ := beginRunE_ok hb
        have a5 := askOwedE_ok ha
        show Grows s.d.st s3.d.st
        rw [a5, a4]
        exact grows_begun _ _ _

/-- (5) The base case. -/
theorem baseE'_grows (Rw : SingleRows) (m : Option ℕ) (c : ℕ) (s s' : H2K.PS)
    (h : H2K.baseE' Rw m c s = .ok s') : Grows s.d.st s'.d.st := by
  unfold H2K.baseE' at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨b, took⟩, h3, h⟩ := bind_ok h
    cases h
    obtain ⟨star, S1, ids, pos, o, _, k2, _, k4, _⟩ := baseEW_state _ _ _ _ _ _ _ _ (mapError_ok h3)
    obtain ⟨_, c2⟩ := spendPlain_form _ _ _ k2
    have k4' : b.st = S1 := k4
    show Grows s.d.st b.st
    rw [k4', c2]
    exact grows_modOracle _ _ _ fun _ => ⟨rfl, id, fun _ h => h⟩
  · cases h

/-- switchBehind's last lines (tailB, SwUnfold.lean), for EVERY target (kept members too).
-/
theorem tailB_grows (i : Tw.L9.SwIn) (out : Switched) (B : TreeBook) (left : List Tw.L9.Col)
    (y : Array E) (S1 : Statement) (o : Tw.L9.SwOut) (h : tailB i out B left y S1 = .ok o) :
    Grows S1 o.st := by
  unfold tailB at h
  obtain ⟨S2, h2, h⟩ := bind_ok h
  obtain ⟨S3, h3, h⟩ := bind_ok h
  have hex : ∃ (rows : List OnBytes.Row) (S4 : Statement),
      rows.foldlM (fun S r => Tw.L9.addRowS S i.grp r) S3 = .ok S4 ∧ o.st = S4 := by
    dsimp only at h
    split at h
    · split at h
      · cases h
      · simp only [pure_bind] at h
        split at h
        · rename_i rows h5
          obtain ⟨S4, h6, h⟩ := bind_ok h
          cases h
          exact ⟨rows, S4, h6, rfl⟩
        · cases h
    · cases h
  obtain ⟨rows, S4, h4, hS4⟩ := hex
  rw [hS4]
  have g2 : Grows S1 S2 := by
    obtain ⟨G, _, _, rfl⟩ := joinS_ok h2
    exact grows_joined _ _ _ _ _
  have g3 : Grows S2 S3 := by
    rw [← Array.foldlM_toList] at h3
    exact foldlM_keeps' Grows Grows.refl (fun _ _ _ a b => a.trans b) _
      (fun S p S' hs => by
        obtain ⟨G, _, _, rfl⟩ := joinS_ok hs
        exact grows_joined _ _ _ _ _) _ _ _ h3
  have g4 : Grows S3 S4 :=
    foldlM_keeps' Grows Grows.refl (fun _ _ _ a b => a.trans b) _
      (fun S r S' hs => by
        obtain ⟨_, _, rfl⟩ := addRowS_ok hs
        exact grows_withRow _ _ _) _ _ _ h4
  exact (g2.trans g3).trans g4

/-- What stands behind the sending, in a switch: for EVERY target. -/
theorem switchBehind_grows (i : Tw.L9.SwIn) (o : Tw.L9.SwOut) (h : Tw.L9.switchBehind i = .ok o) :
    Grows i.st o.st := by
  rw [switchBehind_eq] at h
  cases hcode : i.st.codes.base[i.old.code]? with
  | none => simp only [hcode] at h; cases h
  | some code =>
    simp only [hcode, pure_bind] at h
    obtain ⟨pos, _, h⟩ := bind_ok h
    obtain ⟨x, _, h⟩ := bind_ok h
    by_cases hm : 0 < i.T.shape.maskRows
    · rw [if_pos hm] at h
      obtain ⟨S1, h1, h⟩ := bind_ok h
      split at h1
      · cases h1
        have g2 := tailB_grows _ _ _ _ _ _ _ h
        have g1 : Grows i.st { i.st with oracles := i.st.oracles.modify (i.ids.getD 0 noId) fun x =>
            { x with ledger := x.ledger.map fun l => { l with closed := true } } } :=
          grows_modOracle i.st _ _ fun _ => ⟨rfl, id, fun _ h => h⟩
        exact g1.trans g2
      · cases h1
    · rw [if_neg hm] at h
      have g2 := tailB_grows _ _ _ _ _ _ _ h
      exact g2

/-- (3) The switch, for every target, every others, either flag. -/
theorem switchE_grows (old : SingleRows) (X : SwitchTarget) (grp : ℕ) (o : Array OracleNotice)
    (f : Bool) (s : H2K.PS) (x : (Switched × E) × H2K.PS)
    (h : H2K.switchE old X grp o f s = .ok x) : Grows s.d.st x.2.d.st := by
  unfold H2K.switchE at h
  split at h
  · dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨ids, a1, a2, took, d₂⟩, hsend, h⟩ := bind_ok h
    dsimp only at h
    have g1 := _root_.Desc.Plain.sendP_grows _ _ _ _ _ _ _ (opt_ok hsend)
    split at h
    · simp only [pure_bind] at h
      obtain ⟨oo, hb, h⟩ := bind_ok h
      cases h
      have g2 := switchBehind_grows _ _ (mapError_ok hb)
      exact g1.trans g2
    · obtain ⟨_, hth, _⟩ := bind_ok h
      cases hth
  · cases h

/-- THE FIVE, TOGETHER, in the words of the record PlainGrow (K12FrameKeeps.lean [not in this
library]), field by field. -/
theorem plainGrow_five :
    (∀ g s x, H2K.batE g s = .ok x → Grows s.d.st x.2.d.st) ∧
    (∀ F row m s x, H2K.foldE F row m s = .ok x → Grows s.d.st x.2.d.st) ∧
    (∀ old X grp o f s x, H2K.switchE old X grp o f s = .ok x → Grows s.d.st x.2.d.st) ∧
    (∀ out theta old X grp o s x,
      csTest { H2K.csParts with switch := fun _ _ _ _ _ s => some ((out, theta), s) } old X grp
        o s = some x → Grows s.d.st x.2.d.st) ∧
    (∀ Rw m c s s', H2K.baseE' Rw m c s = .ok s' → Grows s.d.st s'.d.st) :=
  ⟨batE_grows, foldE_grows, switchE_grows, behind_grows, baseE'_grows⟩

end H2K.Out

#print axioms H2K.Out.batE_grows
#print axioms H2K.Out.foldE_grows
#print axioms H2K.Out.behind_grows
#print axioms H2K.Out.baseE'_grows
#print axioms H2K.Out.switchBehind_grows
#print axioms H2K.Out.switchE_grows
#print axioms H2K.Out.plainGrow_five
