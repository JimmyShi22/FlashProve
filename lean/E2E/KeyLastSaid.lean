-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastSaid.lean: what is said of the prover's run on a file's last chain, up to its own proximity test: that the
field `opened` holds the columns that the two earlier chains read, and that the description's own folds over what was
seen at these columns reach the chain's first state. From this, at the test's place, the state on entry of the test
(`doorLast`, K12/DoorLast.lean) is the verifier's: its default is not taken.

Why. A thread does not read the field `opened` (`thr_took`, Honest/Thread/ThrField.lean), and the proximity test on the
last chain reads its state on entry off that field. So a letter of `Said`'s type has to bind it. On the last chain no
sub-protocol in front of the test has a round, so no column is read there, and the letter needs no set of tables.

Main names.
  `owed_of_fold`: where a fold returns with no column left over, it was handed as many columns as are owed.
  `stand_fold`: at a thread's last border, with its field clause: the fold over what was seen at the field's columns.
  `DoorAt`, `saidLast`: the letter. It speaks up to border 2 and says nothing behind.
  `saidNext_last`: it is carried, at a list whose members 0 and 1 have no round.
  `said_door`: it holds at the state that the door lays, from the two threads at their last borders and their field
    clauses.
  `try_of_said`, `door_of_said`, `hand_of_said`: at border 2 the text of the state on entry is the way in at the thread's
    state; so its default is not taken, and the named test `atHandLast` says yes.

What stays open. Every statement here is an implication from the threads. The field clauses at the two last borders
are premises (`L₁`, `L₂`): they are the letter of the two earlier chains. That the chain's first state is the one that
the letter names asks that `begun` is one-valued (`hfun`). Nothing here plays a part.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileD
import Johnson.Desc.ProofFile.Honest.Thread.ThrField
import Johnson.Desc.ProofFile.Honest.K12.DoorLast
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.ProofFile.Honest.Law.WalkFold
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open ProofFile.Honest.K12 (frontOf)
open ProofFile.Honest.K12.Light (doorLast doorLastTry doorLastTry_of_folds atHandLast colsOpened)
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks foldBlocks_cons_ok step_iff)
open VerifiableInference.Desc.K12 (T12)

/-! ## 1 Two laws on folds -/

section folds
variable {S Cl : Type}

/-- **Where a fold returns with no column left over, it was handed just the columns that are owed.** -/
theorem owed_of_fold (ft : Nat) : ∀ (l : List (Block S Cl)) (s e : S) (R r : List Fmt.RoundView) (C : List OpenedColumn),
    foldBlocks ft l s R C = .ok (e, r, []) → C.length = owed ft l R
  | [], s, e, R, r, C, h => by
    have q : (Except.ok (s, R, C) : Except String (S × List Fmt.RoundView × List OpenedColumn)) = .ok (e, r, []) := h
    have q' : C = [] := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj q)).2).2
    rw [owed_nil, q']
    rfl
  | b :: l, s, e, R, r, C, h => by
    obtain ⟨-, s', k, hs, h'⟩ := foldBlocks_cons_ok.1 h
    obtain ⟨⟨-, hf⟩, -, hk⟩ := (step_iff ft b s s' _ C k).1 hs
    subst hk
    have ih := owed_of_fold ft l s' e _ r _ h'
    have hw : (b.want ft (R.take b.rounds.length)).length ≤ C.length := by
      have e2 := congrArg List.length (beq_iff_eq.1 hf)
      rw [List.length_map, List.length_take] at e2
      omega
    rw [owed_cons, ← ih, List.length_drop]
    omega

end folds

/-- **At a thread's last border, with its field clause at an empty base**: the field holds the columns of the fold over
what was seen, from the chain's first state. -/
theorem stand_fold {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (T : Thread Bk S Cl V W Y Pb) (bs : List (Block S Cl))
    (hbs : T.bs = bs) (ha : T.ahead = []) (hft : T.ft = 0) (s₀ : S) {k : Coins Bk} {s : S}
    {m : Mid W Y} {E : Env} (hu : Thr T bs.length k s m E) (hF : T.Field [] bs.length m E)
    (hb : ∀ t, T.begun k m.st.input (m.st.heard.take T.front) t → t = s₀) :
    ∃ c, m.opened = some c ∧ m.seen.length = (bs.flatMap (·.rounds)).length ∧
      c.length = owed 0 bs m.seen ∧ foldBlocks 0 bs s₀ m.seen c = .ok (s, [], []) := by
  subst hbs
  obtain ⟨-, hFit, -, -, ⟨hseen, -, -, -, t, cols, hbeg, hcol, hfold⟩, -, -⟩ := hu
  obtain ⟨cols', hc', ho⟩ := (field_iff T [] T.bs.length m E).1 hF
  obtain rfl : cols' = cols := Except.ok.inj (hc'.symm.trans hcol)
  rw [List.nil_append] at ho
  have hfr : T.front = 0 := by
    unfold Thread.front
    rw [ha]
    rfl
  obtain rfl := hb t hbeg
  rw [hfr, List.drop_zero, hft, List.take_length] at hfold
  have hFit' : drawsFit (T.ahead ++ declsTo T.bs T.bs.length) m.st.heard = true := hFit
  rw [ha, List.nil_append] at hFit'
  have l := drawsFit_length _ _ hFit'
  have e2 := congrArg List.length hseen
  rw [List.length_map] at e2
  have ed : declsTo T.bs T.bs.length = T.bs.flatMap (·.rounds) := by
    unfold declsTo
    rw [List.take_length]
  rw [ed] at l
  exact ⟨cols', ho, e2.trans l, owed_of_fold 0 _ _ _ _ _ _ hfold, hfold⟩

/-! ## 2 The letter -/

section letter
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)

/-- **The two earlier chains as the description folds them**, at rounds r₁, r₂ and columns c₁, c₂: each fold takes all
it is handed; the two ends; the last chain's first state. -/
structure DoorAt (x : Xi) (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : F.S₁) (e₂ : F.S₂) (v₀ : F.S₃) : Prop where
  len₁ : r₁.length = (F.first.blocksInOrder.flatMap (·.rounds)).length
  len₂ : r₂.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length
  own₁ : c₁.length = owed 0 F.first.blocksInOrder r₁
  own₂ : c₂.length = owed 0 F.shared.blocksInOrder r₂
  fold₁ : foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) r₁ c₁ = .ok (e₁, [], [])
  fold₂ : foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r₂ c₂ = .ok (e₂, [], [])
  start : F.start₃ (F.pub x) e₁ e₂ = .ok v₀

variable (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)

/-- **What is said of the run on the last chain, up to border 2**: what was seen is the two earlier chains' rounds; the
field is their columns; the description folds them to the state at which the thread began. Behind border 2 it says
nothing: the one reader of the field stands at that border. -/
def saidLast (b : Nat) (k : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  b ≤ 2 → ∃ (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : F.S₁) (e₂ : F.S₂) (v₀ : F.S₃),
    m.seen = r₁ ++ r₂ ∧ m.opened = some (c₁ ++ c₂) ∧ DoorAt F m.st.input.x r₁ r₂ c₁ c₂ e₁ e₂ v₀ ∧
      T₃.begun k m.st.input (m.st.heard.take T₃.front) v₀

/-- **It is carried**, at a list whose members 0 and 1 have no round. Behind border 2 nothing is asked. -/
theorem saidNext_last (h₀ : ∀ blk, T₃.bs[0]? = some blk → blk.rounds = [])
    (h₁ : ∀ blk, T₃.bs[1]? = some blk → blk.rounds = []) (b : Nat) :
    SaidNext T₃ (saidLast F T₃) b := by
  intro blk hb k s m E ds y cols _ hS hd hM hle
  have hr : blk.rounds = [] := by
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · exact h₀ blk hb
    · exact h₁ blk hb
  rw [hr] at hd
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hd
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hM
  rw [hr] at hc
  have hc' : (Except.ok [] : Except String (List OpenedColumn)) = .ok cols := hc
  obtain rfl : [] = cols := Except.ok.inj hc'
  have hym : y = ([], m) := by
    cases l with
    | nil =>
      simp only [play] at hy
      cases hy
      rfl
    | cons _ _ => simp [play] at hy
  subst hym
  obtain ⟨r₁, r₂, c₁, c₂, e₁, e₂, v₀, hs, ho, hD, hbeg⟩ := hS (by omega)
  refine ⟨r₁, r₂, c₁, c₂, e₁, e₂, v₀, hs, ?_, hD, hbeg⟩
  show m.opened.map (· ++ []) = some (c₁ ++ c₂)
  rw [ho]
  simp

variable {F} (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)

/-- **It holds at the state that the door lays.** -/
theorem said_door (H : Prover W₀ Rc Xi Ky Tr X₀ X) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk)
    (hbs₁ : T₁.bs = F.first.blocksInOrder) (ha₁ : T₁.ahead = []) (hf₁ : T₁.ft = 0)
    (hbs₂ : T₂.bs = F.shared.blocksInOrder) (ha₂ : T₂.ahead = []) (hf₂ : T₂.ft = 0)
    {e₁ : F.S₁} {m₁ : Mid (Local W₀ Rc Xi Tr) X} {E₁ : Env} {e₂ : F.S₂}
    {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env} {s₃ : F.S₃} {o₁ o₂ : List OpenedColumn}
    (u₁ : Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁) (u₂ : Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂)
    (L₁ : T₁.Field [] F.first.blocksInOrder.length m₁ E₁) (L₂ : T₂.Field [] F.shared.blocksInOrder.length m₂ E₂)
    (b₁ : ∀ t, T₁.begun k m₁.st.input (m₁.st.heard.take T₁.front) t → t = F.start₁ (F.pub R.own.x))
    (b₂ : ∀ t, T₂.begun k m₂.st.input (m₂.st.heard.take T₂.front) t → t = F.start₂ (F.pub R.own.x))
    (hs : F.start₃ (F.pub R.own.x) e₁ e₂ = .ok s₃) (j₁ : m₁.opened = some o₁) (j₂ : m₂.opened = some o₂)
    (hbeg : T₃.begun k R.own (m₁.st.heard ++ m₂.st.heard) s₃)
    (hfr : T₃.front = (m₁.st.heard ++ m₂.st.heard).length) :
    saidLast F T₃ 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } := by
  intro _
  obtain ⟨c₁, g₁, n₁, w₁, f₁⟩ := stand_fold T₁ _ hbs₁ ha₁ hf₁ (F.start₁ (F.pub R.own.x))
    u₁ L₁ b₁
  obtain ⟨c₂, g₂, n₂, w₂, f₂⟩ := stand_fold T₂ _ hbs₂ ha₂ hf₂ (F.start₂ (F.pub R.own.x))
    u₂ L₂ b₂
  obtain rfl : c₁ = o₁ := Option.some.inj (g₁.symm.trans j₁)
  obtain rfl : c₂ = o₂ := Option.some.inj (g₂.symm.trans j₂)
  refine ⟨m₁.seen, m₂.seen, c₁, c₂, e₁, e₂, s₃, rfl, rfl, ⟨n₁, n₂, w₁, w₂, f₁, f₂, hs⟩, ?_⟩
  show T₃.begun k R.own ((m₁.st.heard ++ m₂.st.heard).take T₃.front) s₃
  rw [hfr, List.take_length]
  exact hbeg

end letter

/-! ## 3 The state on entry -/

section entry
variable {Xi W₀ Rc Tr X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)

theorem readsOf_nil (c f : Nat) (st : Nat → Nat → Option (List UInt64))
    (tr : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (Rs : List Fmt.Drawn) :
    readsOf c f st tr [] Rs = [] := by
  cases Rs <;> rfl

/-- **At border 2 the text of the state on entry is the way in at the thread's state.** pre: the blocks in front of the
test, the thread's first two, without a round; the text reads them as the description does. -/
theorem try_of_said (pre : List (Block F.S₃ F.Cl)) (hpre : T₃.bs.take 2 = pre)
    (hnone : pre.flatMap (·.rounds) = []) (hft : T₃.ft = F.lastChainFirstTreeNumber)
    (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s')
    (enter : F.S₃ → Except String T12) {k : Coins Bk} {st : F.S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T₃ 2 k st m E)
    (hS : saidLast F T₃ 2 k m) :
    doorLastTry F.first.blocksInOrder F.shared.blocksInOrder pre F.lastChainFirstTreeNumber
      (fun w : Local W₀ Rc Xi Tr => F.start₁ (F.pub w.x)) (fun w => F.start₂ (F.pub w.x))
      (fun w => F.start₃ (F.pub w.x)) enter colsOpened m.st.input (frontOf m) = enter st := by
  obtain ⟨r₁, r₂, c₁, c₂, e₁, e₂, v₀, hs, ho, hD, hbeg⟩ := hS (Nat.le_refl 2)
  obtain ⟨-, hFit, -, -, ⟨hseen, -, -, -, s₀, cols, hb₀, hcol, hfold⟩, -, -⟩ := hT
  obtain rfl : s₀ = v₀ := hfun _ _ _ _ _ hb₀ hbeg
  have hdecl : declsTo T₃.bs 2 = [] := by
    unfold declsTo
    rw [hpre]
    exact hnone
  have hcols : cols = [] := by
    unfold Thread.colsTo at hcol
    rw [hdecl, readsOf_nil] at hcol
    have q : (Except.ok [] : Except String (List OpenedColumn)) = .ok cols := hcol
    exact (Except.ok.inj q).symm
  subst hcols
  have hFit' : drawsFit (T₃.ahead ++ declsTo T₃.bs 2) m.st.heard = true := hFit
  rw [hdecl, List.append_nil] at hFit'
  have l := drawsFit_length _ _ hFit'
  have e2 := congrArg List.length hseen
  rw [List.length_map] at e2
  have hdrop : m.seen.drop T₃.front = [] := by
    apply List.drop_eq_nil_of_le
    unfold Thread.front
    omega
  rw [hdrop, hpre, hft] at hfold
  have h₁ : foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub m.st.input.x)) (frontOf m).seen.rounds
      (colsOpened m.st.input (frontOf m)) = .ok (e₁, r₂, c₂) := by
    show foldBlocks 0 F.first.blocksInOrder _ m.seen (m.opened.getD []) = _
    rw [hs, ho]
    show foldBlocks 0 F.first.blocksInOrder _ (r₁ ++ r₂) (c₁ ++ c₂) = _
    rw [foldBlocks_more 0 F.first.blocksInOrder _ r₁ r₂ c₁ c₂ hD.len₁ hD.own₁, hD.fold₁]
    rfl
  exact doorLastTry_of_folds _ _ _ _ _ _ _ enter colsOpened m.st.input (frontOf m) h₁ hD.fold₂ hD.start hfold

/-- **So the default is not taken**: the state on entry is what the way in returns. -/
theorem door_of_said (pre : List (Block F.S₃ F.Cl)) (hpre : T₃.bs.take 2 = pre)
    (hnone : pre.flatMap (·.rounds) = []) (hft : T₃.ft = F.lastChainFirstTreeNumber)
    (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s')
    (enter : F.S₃ → Except String T12) (fall : T12) {k : Coins Bk} {st : F.S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {t : T12} (hT : Thr T₃ 2 k st m E)
    (hS : saidLast F T₃ 2 k m) (he : enter st = .ok t) :
    doorLast F.first.blocksInOrder F.shared.blocksInOrder pre F.lastChainFirstTreeNumber
      (fun w : Local W₀ Rc Xi Tr => F.start₁ (F.pub w.x)) (fun w => F.start₂ (F.pub w.x))
      (fun w => F.start₃ (F.pub w.x)) enter colsOpened fall m.st.input (frontOf m) = t := by
  unfold doorLast
  rw [try_of_said T₃ pre hpre hnone hft hfun enter hT hS, he]
  rfl

/-- **The same as the named test**: the text returns. -/
theorem hand_of_said (pre : List (Block F.S₃ F.Cl)) (hpre : T₃.bs.take 2 = pre)
    (hnone : pre.flatMap (·.rounds) = []) (hft : T₃.ft = F.lastChainFirstTreeNumber)
    (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s')
    (enter : F.S₃ → Except String T12) {k : Coins Bk} {st : F.S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {t : T12} (hT : Thr T₃ 2 k st m E)
    (hS : saidLast F T₃ 2 k m) (he : enter st = .ok t) :
    atHandLast F.first.blocksInOrder F.shared.blocksInOrder pre F.lastChainFirstTreeNumber
      (fun w : Local W₀ Rc Xi Tr => F.start₁ (F.pub w.x)) (fun w => F.start₂ (F.pub w.x))
      (fun w => F.start₃ (F.pub w.x)) enter colsOpened m.st.input (frontOf m) = true := by
  unfold atHandLast
  rw [try_of_said T₃ pre hpre hnone hft hfun enter hT hS, he]
  rfl

end entry

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.owed_of_fold
#print axioms AtPublicFiles.KeyLastChain.stand_fold
#print axioms AtPublicFiles.KeyLastChain.saidNext_last
#print axioms AtPublicFiles.KeyLastChain.said_door
#print axioms AtPublicFiles.KeyLastChain.try_of_said
#print axioms AtPublicFiles.KeyLastChain.door_of_said
#print axioms AtPublicFiles.KeyLastChain.hand_of_said
