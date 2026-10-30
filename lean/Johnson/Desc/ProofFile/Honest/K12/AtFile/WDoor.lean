-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WDoor.lean: at a stand of the last chain's thread in front of
its proximity test the door's text returns the way in at the stand's own state. The door
(`doorTryW`, K12/AtProof/AtHandW.lean) runs the description's three folds over what a front shows,
so it returns there where the field `opened` holds the columns that the folds read. General in the
description, the thread, the way in and the place.

  `EndsAre`        the two earlier chains' folds at the head of the rounds seen and of the columns:
                   at the rounds r₁, r₂ and the columns c₁, c₂, with nothing left over, they return
                   e₁, e₂, and the base of the field is c₁ then c₂
  `door_of_parts`  the three folds, the start and the field give the door's value
  `door_at_made`   the same at `Thread.Made`: the fold over the blocks in front is the thread's
  `door_value`     so the state on entry is what the way in returns
  `cut_of_places`  where a list of four blocks stands at the last chain's four places, what the door
                   takes in front of the place of the third is the list's first two

What the letter owes. `Thread.Made` binds the columns in front (`Thread.colsTo`) and the first state.
The thread's letter on the field gives `m.opened = some (base ++ cols)` at these columns and
`EndsAre` at base. hs asks that the state at which the thread began is what the description's start
returns at the same e₁, e₂.

Limits.
- hs, hfront, hcut are premises. That a thread meets them at a run is not said here.
- The front spoken of is `frontOf m`: the rounds seen and the field as they stand at m.
- That the way in returns is not asked: the statement is an equation of the door's text and the way
  in; `door_value` takes the way in's yes.
- NOT IN FRONT OF A LAW OVER COINS: `door_at_made` and `door_value` stand behind a clause of `Thr`.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.AtHandW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block OpenedColumn FileDescription Place foldBlocks)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest.K12.Light (doorLastTry doorLastTry_of_folds colsOpened doorW)
open ProofFile.Honest.K12.AtProof (doorTryW doorW_try placeW)

variable {Xi W₀ Rc Tr X : Type} {F : FileDescription Xi}

/-- **The two earlier chains' folds at the head of what the state has seen.** -/
def EndsAre (F : FileDescription Xi) (m : Mid (Local W₀ Rc Xi Tr) X) (base : List OpenedColumn) (e₁ : F.S₁)
    (e₂ : F.S₂) : Prop :=
  ∃ r₁ r₂ rest c₁ c₂, m.seen = r₁ ++ (r₂ ++ rest) ∧ base = c₁ ++ c₂ ∧
    r₁.length = (F.first.blocksInOrder.flatMap (·.rounds)).length ∧
    c₁.length = owed 0 F.first.blocksInOrder r₁ ∧
    r₂.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length ∧
    c₂.length = owed 0 F.shared.blocksInOrder r₂ ∧
    foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub m.st.input.x)) r₁ c₁ = .ok (e₁, [], []) ∧
    foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub m.st.input.x)) r₂ c₂ = .ok (e₂, [], [])

/-- **The door's text at the parts**: the two folds, the start, the field and the fold over the blocks
in front. -/
theorem door_of_parts (enter : F.S₃ → Except String T12) (a : Place)
    (m : Mid (Local W₀ Rc Xi Tr) X) {base cols : List OpenedColumn} {e₁ : F.S₁} {e₂ : F.S₂} {s₀ s : F.S₃}
    {rest : List Fmt.RoundView} (hE : ∃ r₁ r₂ c₁ c₂, m.seen = r₁ ++ (r₂ ++ rest) ∧ base = c₁ ++ c₂ ∧
             r₁.length = (F.first.blocksInOrder.flatMap (·.rounds)).length ∧
             c₁.length = owed 0 F.first.blocksInOrder r₁ ∧
             r₂.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length ∧
             c₂.length = owed 0 F.shared.blocksInOrder r₂ ∧
             foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub m.st.input.x)) r₁ c₁ = .ok (e₁, [], []) ∧
             foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub m.st.input.x)) r₂ c₂ = .ok (e₂, [], []))
    (ho : m.opened = some (base ++ cols))
    (hs : F.start₃ (F.pub m.st.input.x) e₁ e₂ = .ok s₀)
    (hf : foldBlocks F.lastChainFirstTreeNumber (F.second.blocksInOrder.takeWhile (·.place != a)) s₀ rest cols =
      .ok (s, [], [])) :
    doorTryW F (·.x) enter a m.st.input (frontOf m) = enter s := by
  obtain ⟨r₁, r₂, c₁, c₂, h0, hb, n₁, l₁, n₂, l₂, f₁, f₂⟩ := hE
  have hco : colsOpened m.st.input (frontOf m) = c₁ ++ (c₂ ++ cols) := by
    show m.opened.getD [] = _
    rw [ho, hb, List.append_assoc]
    rfl
  have g₁ : foldBlocks 0 F.first.blocksInOrder ((fun w : Local W₀ Rc Xi Tr => F.start₁ (F.pub w.x))
               m.st.input) (frontOf m).seen.rounds (colsOpened m.st.input (frontOf m)) =
      .ok (e₁, r₂ ++ rest, c₂ ++ cols) := by
    show foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub m.st.input.x)) m.seen _ = _
    rw [hco, h0, ProofFile.Honest.foldBlocks_more 0 F.first.blocksInOrder _ _ _ _ _ n₁ l₁, f₁]
    rfl
  have g₂ : foldBlocks 0 F.shared.blocksInOrder ((fun w : Local W₀ Rc Xi Tr => F.start₂ (F.pub w.x))
               m.st.input) (r₂ ++ rest) (c₂ ++ cols) = .ok (e₂, rest, cols) := by
    show foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub m.st.input.x)) _ _ = _
    rw [ProofFile.Honest.foldBlocks_more 0 F.shared.blocksInOrder _ _ _ _ _ n₂ l₂, f₂]
    rfl
  exact doorLastTry_of_folds _ _ _ _ _ _ _ enter colsOpened m.st.input (frontOf m) g₁ g₂ hs hf

variable {Bk : ProverCoinCounts} {V Pb : Type}

/-- **At `Thread.Made`.** The thread's own fold is the door's third, where the thread's list in front
of the border is what the door cuts, and the thread's first tree and its rounds in front are the
description's. hs: the state at which the thread began is the start's at e₁, e₂. -/
theorem door_at_made (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb)
    (enter : F.S₃ → Except String T12) (a : Place) {b : ℕ} {k : Coins Bk} {s : F.S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {base cols : List OpenedColumn} {e₁ : F.S₁} {e₂ : F.S₂}
    (hft : T.ft = F.lastChainFirstTreeNumber)
    (hfront : T.front = (F.first.blocksInOrder.flatMap (·.rounds)).length +
      (F.shared.blocksInOrder.flatMap (·.rounds)).length)
    (hcut : T.bs.take b = F.second.blocksInOrder.takeWhile (·.place != a))
    (hM : T.Made b k s m E) (hE : EndsAre F m base e₁ e₂) (hc : T.colsTo b m E = .ok cols)
    (ho : m.opened = some (base ++ cols))
    (hs : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ →
      F.start₃ (F.pub m.st.input.x) e₁ e₂ = .ok s₀) :
    doorTryW F (·.x) enter a m.st.input (frontOf m) = enter s := by
  obtain ⟨-, -, -, -, s₀, cols', hbeg, hc', hf⟩ := hM
  obtain rfl : cols' = cols := Except.ok.inj (hc'.symm.trans hc)
  obtain ⟨r₁, r₂, rest, c₁, c₂, h0, hb, n₁, l₁, n₂, l₂, f₁, f₂⟩ := hE
  have hd : m.seen.drop T.front = rest := by
    rw [h0, hfront, ← n₁, ← n₂, ← List.append_assoc]
    exact List.drop_left' (List.length_append ..)
  rw [hd, hcut, hft] at hf
  exact door_of_parts enter a m ⟨r₁, r₂, c₁, c₂, h0, hb, n₁, l₁, n₂, l₂, f₁, f₂⟩ ho (hs s₀ hbeg) hf

/-- **The state on entry is what the way in returns**, at a job's door: where the text is the way in
at s and the way in returns R. -/
theorem door_value (enter : F.S₃ → Except String T12) (a : Place) (fall : T12)
    (m : Mid (Local W₀ Rc Xi Tr) X) {s : F.S₃} {R : T12}
    (h : doorTryW F (·.x) enter a m.st.input (frontOf m) = enter s) (he : enter s = .ok R) :
    doorW F (·.x) enter a fall m.st.input (frontOf m) = R := by
  rw [doorW_try, h, he]
  rfl

/-- **What the door takes in front of the third of four blocks** at the last chain's four places. -/
theorem cut_of_places {S Cl : Type} (bs : List (Block S Cl))
    (h : bs.map (·.place) =
      [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, placeW, ⟨3, none, 3, .frame⟩]) :
    bs.take 2 = bs.takeWhile (·.place != placeW) := by
  cases bs with
  | nil => simp at h
  | cons a t => cases t with
    | nil => simp at h
    | cons b t => cases t with
      | nil => simp at h
      | cons c t => cases t with
        | nil => simp at h
        | cons d t => cases t with
          | cons e l => simp at h
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
            obtain ⟨e0, e1, e2, -⟩ := h
            have k0 : (a.place != placeW) = true := by
              rw [e0]
              rfl
            have k1 : (b.place != placeW) = true := by
              rw [e1]
              rfl
            have k2 : (c.place != placeW) = false := by
              rw [e2]
              rfl
            simp [List.takeWhile_cons, k0, k1, k2]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.EndsAre
#print axioms ProofFile.Honest.K12.AtFile.door_of_parts
#print axioms ProofFile.Honest.K12.AtFile.door_at_made
#print axioms ProofFile.Honest.K12.AtFile.door_value
#print axioms ProofFile.Honest.K12.AtFile.cut_of_places
