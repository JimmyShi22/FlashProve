-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastStart.lean: the state at which a file's last chain begins, as a function of the run's coins, the input and the
challenges heard: for `PlayedTo` and `tableBy` (Honest/Small/PlayedTo.lean), whose `start` is a parameter. It is taken by
choice over the pairs of stands of the two earlier threads, as `endsBy` (Thread/OneState.lean) takes their last states;
so it reads no field of the last thread, and no circle arises with that thread's tables.

Main names.
  `doorMid`: the state that the door lays, with the field handed.
  `DoorState`: a state of that form at two stands of the earlier threads.
  `doorState_unique`, `startBy`, `startBy_eq`, `startBy_opened`.
  `saidKey`, `saidNext_key`, `played_door`: the letter of the last chain: `saidLast` and, up to border 2, `PlayedTo`.

What stays open. `OneStand` at both last borders is a premise: what is said of the two earlier chains has to fix the run.
`startBy` is defined by choice; nothing computes it. dflt: the value off the pairs: it has to hold a field.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastSaid
import Johnson.Desc.ProofFile.Honest.Small.PlayedTo
import Johnson.Desc.ProofFile.Honest.Thread.OneState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open ProofFile.Honest.Small (PlayedTo played_next)
open VerifiableInference.Desc (Block OpenedColumn FileDescription)

section
variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- **The state that the door lays**, at the input w and the field c. -/
def doorMid (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : Local W₀ Rc Xi Tr) (m₁ : Mid (Local W₀ Rc Xi Tr) X)
    (m₂ : Mid (Common W₀ Rc Ky) X₀) (c : List OpenedColumn) : Mid (Local W₀ Rc Xi Tr) X :=
  ⟨⟨w, m₁.st.heard ++ m₂.st.heard, H.meet m₁.st.own m₂.st⟩, m₁.loc, m₁.seen ++ m₂.seen, some c⟩

variable {S₁ S₂ Cl : Type} (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (T₁ : Thread Bk S₁ Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (T₂ : Thread Bk S₂ Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
  (n₁ n₂ : Nat) (cm : Local W₀ Rc Xi Tr → Common W₀ Rc Ky)

/-- **A state of that form, at two stands of the earlier threads.** -/
def DoorState (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn)
    (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  ∃ (e₁ : S₁) (m₁ : Mid (Local W₀ Rc Xi Tr) X) (E₁ : Env) (e₂ : S₂) (m₂ : Mid (Common W₀ Rc Ky) X₀)
    (E₂ : Env) (o₁ o₂ : List OpenedColumn),
    ThrS T₁ Said₁ n₁ k e₁ m₁ E₁ ∧ ThrS T₂ Said₂ n₂ k e₂ m₂ E₂ ∧ m₁.st.input = w ∧ m₂.st.input = cm w ∧
      m₁.st.heard ++ m₂.st.heard = h ∧ m₁.opened = some o₁ ∧ m₂.opened = some o₂ ∧
      m = doorMid H w m₁ m₂ (o₁ ++ o₂)

variable {H T₁ T₂ Said₁ Said₂ n₁ n₂ cm}

/-- **One run, one such state**, where what is said of the two earlier chains fixes their runs. -/
theorem doorState_unique (u₁ : OneStand Said₁ n₁) (u₂ : OneStand Said₂ n₂) {k : Coins Bk}
    {w : Local W₀ Rc Xi Tr} {h : List Fmt.Drawn} {m m' : Mid (Local W₀ Rc Xi Tr) X}
    (a : DoorState H T₁ T₂ Said₁ Said₂ n₁ n₂ cm k w h m)
    (b : DoorState H T₁ T₂ Said₁ Said₂ n₁ n₂ cm k w h m') : m = m' := by
  obtain ⟨e₁, m₁, E₁, e₂, m₂, E₂, o₁, o₂, t₁, t₂, i₁, i₂, hh, j₁, j₂, rfl⟩ := a
  obtain ⟨e₁', m₁', E₁', e₂', m₂', E₂', o₁', o₂', t₁', t₂', i₁', i₂', hh', j₁', j₂', rfl⟩ := b
  have hl : m₁.st.heard.length = m₁'.st.heard.length := by
    rw [T₁.heard_length t₁.1.2.1, T₁.heard_length t₁'.1.2.1]
  obtain ⟨a₁, a₂⟩ := List.append_inj (hh.trans hh'.symm) hl
  obtain rfl : m₁ = m₁' := u₁ k m₁ m₁' t₁.2 t₁'.2 (i₁.trans i₁'.symm) a₁
  obtain rfl : m₂ = m₂' := u₂ k m₂ m₂' t₂.2 t₂'.2 (i₂.trans i₂'.symm) a₂
  obtain rfl : o₁ = o₁' := Option.some.inj (j₁.symm.trans j₁')
  obtain rfl : o₂ = o₂' := Option.some.inj (j₂.symm.trans j₂')
  rfl

variable (H T₁ T₂ Said₁ Said₂ n₁ n₂ cm)

open Classical in
/-- **The last chain's start, by choice**; dflt off the pairs. -/
noncomputable def startBy (dflt : Mid (Local W₀ Rc Xi Tr) X) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) : Mid (Local W₀ Rc Xi Tr) X :=
  if hE : ∃ m, DoorState H T₁ T₂ Said₁ Said₂ n₁ n₂ cm k w h m then hE.choose else dflt

variable {H T₁ T₂ Said₁ Said₂ n₁ n₂ cm}

/-- **It returns such a state.** -/
theorem startBy_eq (dflt : Mid (Local W₀ Rc Xi Tr) X) (u₁ : OneStand Said₁ n₁) (u₂ : OneStand Said₂ n₂)
    {k : Coins Bk} {w : Local W₀ Rc Xi Tr} {h : List Fmt.Drawn} {m : Mid (Local W₀ Rc Xi Tr) X}
    (a : DoorState H T₁ T₂ Said₁ Said₂ n₁ n₂ cm k w h m) :
    startBy H T₁ T₂ Said₁ Said₂ n₁ n₂ cm dflt k w h = m := by
  have hE : ∃ m, DoorState H T₁ T₂ Said₁ Said₂ n₁ n₂ cm k w h m := ⟨m, a⟩
  unfold startBy
  rw [dif_pos hE]
  exact doorState_unique u₁ u₂ hE.choose_spec a

/-- **It holds a field**, where the default does. -/
theorem startBy_opened (dflt : Mid (Local W₀ Rc Xi Tr) X) (hd : dflt.opened.isSome = true) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) :
    (startBy H T₁ T₂ Said₁ Said₂ n₁ n₂ cm dflt k w h).opened.isSome = true := by
  unfold startBy
  split
  · rename_i hE
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := hE.choose_spec
    rw [e]
    rfl
  · exact hd

end

section
variable {W₀ Rc Xi Tr X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
  (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (start : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Mid (Local W₀ Rc Xi Tr) X)

/-- **What is said of the run on the last chain**: `saidLast`, and up to border 2 that the run is the play from `start`. -/
def saidKey (b : Nat) (k : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  saidLast F T₃ b k m ∧ (b ≤ 2 → PlayedTo T₃ start b k m)

/-- **It is carried**, at a list whose members 0 and 1 have no round. -/
theorem saidNext_key (h₀ : ∀ blk, T₃.bs[0]? = some blk → blk.rounds = [])
    (h₁ : ∀ blk, T₃.bs[1]? = some blk → blk.rounds = []) (b : Nat) :
    SaidNext T₃ (saidKey F T₃ start) b := by
  intro blk hb k s m E ds y cols hT hS hd hM
  refine ⟨saidNext_last F T₃ h₀ h₁ b blk hb k s m E ds y cols hT hS.1 hd hM, fun hle => ?_⟩
  have hr : blk.rounds = [] := by
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · exact h₀ blk hb
    · exact h₁ blk hb
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  rw [hr] at hd hc
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hd
  have hc' : (Except.ok [] : Except String (List OpenedColumn)) = .ok cols := hc
  obtain rfl : [] = cols := Except.ok.inj hc'
  obtain ⟨L, ps, hL, hp⟩ := hS.2 (by omega)
  have hlen : T₃.front ≤ m.st.heard.length := by
    rw [Thread.heard_length T₃ hT.2.1]
    exact Nat.le_add_right _ _
  obtain ⟨a1, a2⟩ := played_next hb hlen hL hp hl hy
  have e : y.2.took [] = y.2 := by
    obtain ⟨ps', st, loc, seen, opened⟩ := y
    cases opened with
    | none => rfl
    | some c =>
      show (⟨st, loc, seen, some (c ++ [])⟩ : Mid (Local W₀ Rc Xi Tr) X) = _
      rw [List.append_nil]
  rw [e]
  exact ⟨L ++ l, ps ++ y.1, a1, a2⟩

variable {F T₃ start}

/-- **At the door the run is the play of nothing from `start`.** -/
theorem played_door {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X}
    (hfr : T₃.front = m.st.heard.length) (hst : start k m.st.input m.st.heard = m) :
    PlayedTo T₃ start 0 k m := by
  refine ⟨[], [], ?_, ?_⟩
  · rw [List.take_zero]
    rfl
  · rw [hfr, List.drop_length, List.take_length, hst]
    simp only [play]

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.doorState_unique
#print axioms AtPublicFiles.KeyLastChain.startBy_eq
#print axioms AtPublicFiles.KeyLastChain.startBy_opened
#print axioms AtPublicFiles.KeyLastChain.saidNext_key
#print axioms AtPublicFiles.KeyLastChain.played_door
