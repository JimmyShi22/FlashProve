-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileRow.lean: A MEMBER FOR THE FILE's RULE
(Honest/Thread/File.lean, `file_runs`): at the toy row's own description `Fy`, book `By` and prover
`Hy` (Honest/Law/ToyRow.lean, ToyTies.lean) three threads sit; the four debts that say nothing of a
fall are met at each of its ten members; the threads are entered at the frame's own starts, and the
second chain's stands behind the door's yes: so the rule's premises can be met together, and it
yields that `runC` returns there. Theorems about these files' own made-up objects, but for one
general lemma. None is one of the library's goals.

  1  `plays_of_playsOn`   GENERAL: the first debt out of the chain's rule's first form
  2  `T₁y`, `T₂y`, `T₃y`   the three threads, at a run's two inputs
  3  the debts: `owes₁`, `owes₂`, `owes₃`
  4  the seams: `sits_row`, `enters₁_row`, `enters₂_row`, `door_row`
  5  `silent_row`, `runs_by_threads`   no list is withheld at the row; THE RULE, CALLED

The threads' letters. (V): the input is the run's own. (H): the stored table's columns are the
prover's; the shared chain's one tree and the second chain's one tree are functions of the run's
coins and the input. (F), (X): as in every thread; in front of the second chain stand the rounds of
the two earlier ones. NO ITEM, and a form, riders and keeps that ask nothing: so of the four debts
`Behind`, `Exchange` and `RidesPast` hold here with nothing in them, and `Plays` alone bears
content. The items' debts are met at Honest/Thread/ThrRow.lean's thread.

Limits. A toy: ten small members; no stop, no fall, no item. `runC` returns at this row by
Honest/Law/ToyRuns.lean's `runs_row` already, with `silent_row` for its premise on `silentAt`, from
sentences of that file's own: what is new here is that it follows from the threads' debts and seams.
Nothing on a verifier's accept. No part of the example reads what it is handed as `Seen`, so none
reads the field `opened`: what the hypotheses here ask of that field is met for free. Of a prover
with a part that reads the columns nothing is shown here. Among the hypotheses that the prose above
does not name: `drawsFit` (`drawFit` round by round, and as many challenges as rounds):
`look_trees`, `send_trees₃`, `runs_tell₃`; `ready … = .ok` (`ready` returns at these coins):
`enters₁_row`, `enters₂_row`. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw
import Johnson.Desc.ProofFile.Honest.Thread.ThrRow
import Johnson.Desc.ProofFile.Honest.Law.ToyRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

/-! ## 1 The first debt out of the chain's rule's first form -/

/-- **The first debt out of `PlaysOn`**, where the thread gives that form's sentence in front, and
the member's new trees are shown to be the functions' tables. A lemma on our own definitions. -/
theorem plays_of_playsOn {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    {blk : Block S Cl} {A B : Coins Bk → S → Mid W X → Env → Prop} (hblk : T.bs[b]? = some blk)
    (h : PlaysOn T.φ Bk T.chain T.ft T.hs blk A B)
    (hA : ∀ k s m E, Thr T b k s m E → A k s m E)
    (hT : ∀ k s m E ds y cols, Thr T b k s m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1)) : Plays T b := by
  intro blk' hblk' k s m E ds l hThr hd hst hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨y, cols, hy, hc, -⟩ := h k s m E ds l (hA k s m E hThr) hd hst hl
  have hMv : T.Moved blk k m E ds y cols := by
    unfold Thread.Moved
    exact ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨y, cols, hMv, hT k s m E ds y cols hThr hd hMv⟩

namespace Toy
open VerifiableInference.Desc.BlockToy (St send₃ tree tree₃ drawT sendS openA orc)
open OnBytes.Slice (toF ofF)

/-! ## 2 The three threads -/

/-- The shared chain's tree's table. -/
def tableL (k : Coins By) (w : L₀) : Table :=
  ⟨3, 1, fun p _ => toF (w.w₀.a p) + coinAt k 1 zO 0 + coinAt k 1 zO 1 + coinAt k 1 zO 1⟩

/-- **The first chain's thread**, at a run's input. -/
abbrev T₁y (w : L) : Thread By St Nat L L Nat Nat :=
  { φ := .own, chain := 0, ft := 0, bs := Fy.first.blocksInOrder, hs := Hy.first
    ahead := [], near := 0, taken := []
    fixed := fun _ => 0, table := fun _ k v _ => (pSend, tableY k v)
    stored := fun v => Hy.storedWords v.w₀ v.rc, valid := fun v => v = w
    ι := Empty, dec := inferInstance, start := [], row := fun _ => {}
    P := Unit, handed := fun _ _ _ => (), Wt := Unit
    form := fun _ _ => true, formP := fun _ _ => True
    means := fun _ i _ _ _ => i.elim
    wit := fun _ _ _ => ()
    strs := Env.strs 0 fun _ => none
    begun := fun _ _ _ s => s = st₀
    rides := fun _ _ _ => True
    keeps := fun _ _ _ => True }

/-- **The shared chain's thread**, at a run's shared input. -/
abbrev T₂y (w : L₀) : Thread By St Nat Empty L₀ Nat UInt64 :=
  { φ := .shared, chain := 1, ft := 0, bs := Fy.shared.blocksInOrder, hs := Hy.shared
    ahead := [], near := 0, taken := []
    fixed := fun _ => 0, table := fun _ k v _ => (pLook, tableL k v)
    stored := fun v => Hy.storedWords v.w₀ v.rc, valid := fun v => v = w
    ι := Empty, dec := inferInstance, start := [], row := fun _ => {}
    P := Unit, handed := fun _ _ _ => (), Wt := Unit
    form := fun _ _ => true, formP := fun _ _ => True
    means := fun _ i _ _ _ => i.elim
    wit := fun _ _ _ => ()
    strs := Env.strs 0 fun _ => none
    begun := fun _ _ _ s => s = st₀
    rides := fun _ _ _ => True
    keeps := fun _ _ _ => True }

/-- **The second chain's thread**, at a run's input. -/
abbrev T₃y (w : L) : Thread By St Nat L L Nat Nat :=
  { φ := .own, chain := 2, ft := Fy.lastChainFirstTreeNumber, bs := Fy.second.blocksInOrder, hs := Hy.second
    ahead := declsTo Fy.first.blocksInOrder 2 ++ declsTo Fy.shared.blocksInOrder 3
    near := (declsTo Fy.first.blocksInOrder 2).length, taken := []
    fixed := fun _ => 0, table := fun _ k v _ => (pSend, tableY k v)
    stored := fun v => Hy.storedWords v.w₀ v.rc, valid := fun v => v = w
    ι := Empty, dec := inferInstance, start := [], row := fun _ => {}
    P := Unit, handed := fun _ _ _ => (), Wt := Unit
    form := fun _ _ => true, formP := fun _ _ => True
    means := fun _ i _ _ _ => i.elim
    wit := fun _ _ _ => ()
    strs := Env.strs 0 fun _ => none
    begun := fun _ _ _ s => s = st₀
    rides := fun _ _ _ => True
    keeps := fun _ _ _ => True }

/-! ## 3 The debts -/

theorem storedOk_Hy (w₀ : Wit₀) (rc : UInt64) : storedOk (Hy.storedWords w₀ rc) :=
  fun _ => ⟨_, rfl, rfl⟩

/-- The first chain. -/
theorem owes₁ (w : L) : Owes (T₁y w) := by
  intro b hb
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟨rfl, trivial⟩, trivial, trivial⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ i _ => i.elim, fun _ _ _ _ _ _ i => i.elim⟩
  match b, hb with
  | 0, _ => exact plays_quiet (T₁y w) (b := 0) rfl rfl rfl
  | 1, _ =>
    refine plays_of_playsOn (T₁y w) (b := 1) rfl (thread₁ 1 _ rfl) (fun _ _ _ _ _ => trivial) ?_
    intro _ _ _ _ _ _ _ _ _ _ σ hσ
    have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  | n + 2, hb => exact absurd hb (Nat.not_lt.2 (Nat.le_add_left 2 n))

theorem find_look : (Hy.shared.find? fun g => g.place == zSide.block.place) = some zSide.half :=
  rfl

/-- What the shared chain's thread says of the tables at hand. -/
theorem parts₂ {w : L₀} {b : Nat} {k : Coins By} {s : St} {m : Mid L₀ Nat} {E : Env}
    (h : Thr (T₂y w) b k s m E) : storedOk E.stored ∧ E.sent = treesTo Fy.shared.blocksInOrder b := by
  unfold Thr Thread.Hand Thread.Made at h
  refine ⟨fun x => ?_, h.2.2.2.2.1.2.2.1⟩
  rw [h.1.1 0 x]
  exact storedOk_Hy m.st.input.w₀ m.st.input.rc x

/-- Behind `look` its tree is the function's table. -/
theorem look_trees {w : L₀} {k : Coins By} {s : St} {m : Mid L₀ Nat} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid L₀ Nat} {cols : List OpenedColumn}
    (hA : Thr (T₂y w) 1 k s m E) (hd : drawsFit zSide.block.rounds ds = true)
    (hMv : (T₂y w).Moved zSide.block k m E ds y cols) :
    (T₂y w).handAt (.own 0) k y.2 (E.add y.1) = true := by
  have hd' : drawsFit [{ entry := sendS }, { entry := openA, opens := [(tree, .own 0)] }] ds =
    true := hd
  obtain ⟨R₀, R₁, rfl, -, -⟩ := drawsFit_two hd'
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨c, hc, rfl⟩ := steps_one_half find_look hl
  obtain ⟨c₀, e₀, cu, hc₀, ht, hu⟩ := lendsLook_By k
  have ec : c = ((c₀, (), ()), ((e₀, (cu, ()), ()), ())) := Except.ok.inj (hc.symm.trans hc₀)
  subst ec
  obtain ⟨m', hy', hm'⟩ := play_look c₀ e₀ cu m R₀ R₁
  rw [ht, hu] at hy'
  have ey := Except.ok.inj (hy.symm.trans hy')
  subst ey
  have hs := (parts₂ hA).2
  obtain ⟨st, tre, sent⟩ := E
  have hs' : sent = 0 := hs
  subst hs'
  show ((some (pLook, tableL k m.st.input) : Option (Place × Table)).any fun u =>
    u.1 == pLook && u.2.same (tableL k m'.st.input)) = true
  rw [hm']
  show (pLook == pLook && (tableL k m.st.input).same (tableL k m.st.input)) = true
  rw [Table.same_refl]
  rfl

/-- `storeY`'s first law, from the stored columns alone. -/
theorem store_plays : PlaysOn .shared By 1 0 Hy.shared storeY
    (fun _ _ _ E => storedOk E.stored) anyAt := by
  refine plays_of_bare rfl fun k s m E ds y hA hd _ => ?_
  have hd' : drawsFit storeY.rounds ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨p, hp⟩ := one_of_length (poss_of_drawFit h₀)
  obtain ⟨el, ps, tr, dg⟩ := R
  have hp' : ps = [p] := hp
  subst hp'
  obtain ⟨u, hu, hl⟩ := hA (p % 2 ^ 3)
  refine ⟨[(Fmt.storedKey 0, p % 2 ^ 3, u)], ?_, fun _ _ _ => trivial⟩
  show fillCols [⟨Fmt.storedKey 0, p % 2 ^ 3, some 0, none, none, E.stored 0 (p % 2 ^ 3), 2⟩] [] =
    _
  rw [hu]
  show (if (u.length != 2) = true then _ else _) = _
  rw [hl]
  rfl

/-- The shared chain. -/
theorem owes₂ (w : L₀) : Owes (T₂y w) := by
  intro b hb
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟨rfl, trivial⟩, trivial, trivial⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ i _ => i.elim, fun _ _ _ _ _ _ i => i.elim⟩
  match b, hb with
  | 0, _ => exact plays_quiet (T₂y w) (b := 0) rfl rfl rfl
  | 1, _ =>
    refine plays_of_playsOn (T₂y w) (b := 1) rfl (thread₂ 1 _ rfl)
      (fun _ _ _ _ h => ⟨(parts₂ h).2, (parts₂ h).1⟩) ?_
    intro k s m E ds y cols hA hd hMv σ hσ
    have hσ' : σ ∈ [Fmt.TreeSource.own 0] := hσ
    cases List.mem_singleton.1 hσ'
    exact look_trees hA hd hMv
  | 2, _ =>
    refine plays_of_playsOn (T₂y w) (b := 2) rfl store_plays (fun _ _ _ _ h => (parts₂ h).1) ?_
    intro _ _ _ _ _ _ _ _ _ _ σ hσ
    have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  | n + 3, hb => exact absurd hb (Nat.not_lt.2 (Nat.le_add_left 3 n))

/-- What the second chain's thread says of the tables at hand. -/
theorem parts₃ {w : L} {b : Nat} {k : Coins By} {s : St} {m : Mid L Nat} {E : Env}
    (h : Thr (T₃y w) b k s m E) :
    (T₃y w).Trees ((T₃y w).hand b) k m E ∧ E.sent = treesTo Fy.second.blocksInOrder b := by
  unfold Thr Thread.Hand Thread.Made at h
  exact ⟨h.1.2, h.2.2.2.2.1.2.2.1⟩

/-- Behind `send₃` its tree is the function's table. -/
theorem send_trees₃ {w : L} {k : Coins By} {s : St} {m : Mid L Nat} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid L Nat} {cols : List OpenedColumn}
    (hA : Thr (T₃y w) 1 k s m E) (hd : drawsFit send₃.rounds ds = true)
    (hMv : (T₃y w).Moved send₃ k m E ds y cols) :
    (T₃y w).handAt (.own 0) k y.2 (E.add y.1) = true := by
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1 } }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨m', hy', hm'⟩ := send_moves (R := R) hl
  have ey := Except.ok.inj (hy.symm.trans hy')
  subst ey
  have hs := (parts₃ hA).2
  obtain ⟨st, tre, sent⟩ := E
  have hs' : sent = 0 := hs
  subst hs'
  show ((some (pSend, tableY k m.st.input) : Option (Place × Table)).any fun u =>
    u.1 == pSend && u.2.same (tableY k m'.st.input)) = true
  rw [hm']
  show (pSend == pSend && (tableY k m.st.input).same (tableY k m.st.input)) = true
  rw [Table.same_refl]
  rfl

/-- `tellB` from the thread in front of it. -/
theorem runs_tell₃ {w : L} {k : Coins By} {s : St} {m : Mid L Nat} {E : Env}
    {ds : List Fmt.Drawn} (hA : Thr (T₃y w) 2 k s m E) (hd : drawsFit tellB.rounds ds = true)
    (l : List (Step L Nat))
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [tellB] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree tellB.rounds ds) [] =
        .ok cols ∧ tellB.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s, cols.length) := by
  have hd' : drawsFit [{ entry := drawT, opens := [(tree₃, .own 0)] },
      { entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R₀, R₁, rfl, h₀, h₁⟩ := drawsFit_two hd'
  obtain ⟨x, hx⟩ := one_of_length (poss_of_drawFit h₀)
  obtain ⟨el, ps, tr, dg⟩ := R₀
  have hx' : ps = [x] := hx
  subst hx'
  obtain ⟨hTr, hs⟩ := parts₃ hA
  obtain ⟨pl, T, hT, hsame⟩ := hand_elim (hTr (.own 0)
    (show Fmt.TreeSource.own 0 ∈ [Fmt.TreeSource.own 0] from List.mem_singleton.2 rfl))
  obtain ⟨-, hcol⟩ := col_of_hand hsame (x % 2 ^ 2) (Nat.mod_lt _ (by decide))
  obtain ⟨st, tre, sent⟩ := E
  have hs' : sent = 1 := hs
  subst hs'
  exact tell_runs s hT hcol h₀ h₁ hl

/-- The second chain. -/
theorem owes₃ (w : L) : Owes (T₃y w) := by
  intro b hb
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟨rfl, trivial⟩, trivial, trivial⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ i _ => i.elim, fun _ _ _ _ _ _ i => i.elim⟩
  match b, hb with
  | 0, _ => exact plays_quiet (T₃y w) (b := 0) rfl rfl rfl
  | 1, _ =>
    refine plays_of_playsOn (T₃y w) (b := 1) rfl (thread₃ 1 _ rfl)
      (fun _ _ _ _ h => (parts₃ h).2) ?_
    intro k s m E ds y cols hA hd hMv σ hσ
    have hσ' : σ ∈ [Fmt.TreeSource.own 0] := hσ
    cases List.mem_singleton.1 hσ'
    exact send_trees₃ hA hd hMv
  | 2, _ =>
    intro blk hblk k s m E ds l hA hd _ hl
    cases Option.some.inj hblk
    obtain ⟨y, cols, hMv⟩ := moved_of_runs hl (runs_tell₃ hA hd l hl)
    refine ⟨y, cols, hMv, ?_⟩
    intro σ hσ
    have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  | 3, _ =>
    refine plays_of_playsOn (T₃y w) (b := 3) rfl (plays_of_good (good_carry (pre := [])) rfl)
      (fun _ _ _ _ _ => trivial) ?_
    intro _ _ _ _ _ _ _ _ _ _ σ hσ
    have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  | 4, _ => exact plays_quiet (T₃y w) (b := 4) rfl rfl rfl
  | n + 5, hb => exact absurd hb (Nat.not_lt.2 (Nat.le_add_left 5 n))

/-! ## 4 The seams -/

theorem sits_row (w : L) (w' : L₀) : Sits Fy Hy (T₁y w) (T₂y w') (T₃y w) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl⟩

section
variable {w₀ : Wit₀} {rc : UInt64} {x : Nat} {k : Coins By}
  {R : Ready Wit₀ UInt64 Nat UInt64 Trace Nat Nat}

theorem enters₁_row (hR : ready Fy By Hy w₀ rc x k = .ok R) :
    Enters₁ Fy Hy (T₁y R.own) w₀ rc x k R := by
  obtain ⟨-, tr, -, hown, -, -, -, -⟩ := ready_ok hR
  unfold Enters₁ Thr Thread.Hand Thread.Fit Thread.Form Thread.Made
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, rfl, ⟨rfl, trivial⟩, fun _ i _ => i.elim,
    ⟨rfl, rfl, rfl, fun _ _ => rfl, st₀, [], rfl, rfl, rfl⟩, trivial, rfl⟩
  · show Hy.storedWords w₀ rc i p = Hy.storedWords R.own.w₀ R.own.rc i p
    rw [hown]
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'

theorem enters₂_row (hR : ready Fy By Hy w₀ rc x k = .ok R) :
    Enters₂ Fy Hy (T₂y R.common) w₀ rc x k R := by
  obtain ⟨-, tr, -, -, hcom, -, -, -⟩ := ready_ok hR
  unfold Enters₂ Thr Thread.Hand Thread.Fit Thread.Form Thread.Made
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, rfl, ⟨rfl, trivial⟩, fun _ i _ => i.elim,
    ⟨rfl, rfl, rfl, fun _ _ => rfl, st₀, [], rfl, rfl, rfl⟩, trivial, rfl⟩
  · show Hy.storedWords w₀ rc i p = Hy.storedWords R.common.w₀ R.common.rc i p
    rw [hcom]
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'

/-- **The door, behind its yes.** -/
theorem door_row : DoorBehind Fy Hy (T₁y R.own) (T₂y R.common) (T₃y R.own) x k R := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs
  have es : s₃ = st₀ := (Except.ok.inj hs).symm
  subst es
  unfold Thr Thread.Hand Thread.Fit Thread.Made at u₁ u₂
  obtain ⟨⟨hst₁, -⟩, hF₁, -, -, ⟨hseen₁, hloc₁, -, -, -⟩, -, hv₁⟩ := u₁
  obtain ⟨-, hF₂, -, -, ⟨hseen₂, -, -, -, -⟩, -, -⟩ := u₂
  have hF₁' : drawsFit (declsTo Fy.first.blocksInOrder 2) m₁.st.heard = true := hF₁
  have hF₂' : drawsFit (declsTo Fy.shared.blocksInOrder 3) m₂.st.heard = true := hF₂
  have l₁ := drawsFit_length _ _ hF₁'
  have l₂ := drawsFit_length _ _ hF₂'
  have hv₁' : m₁.st.input = R.own := hv₁
  have hloc₁' : m₁.loc = m₁.st.heard := hloc₁
  unfold Thr Thread.Hand Thread.Fit Thread.Form Thread.Made
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, ?_, ⟨rfl, trivial⟩, fun _ i _ => i.elim,
    ⟨?_, ?_, rfl, fun _ _ => rfl, st₀, [], rfl, rfl, ?_⟩, trivial, rfl⟩
  · show E₁.stored i p = Hy.storedWords R.own.w₀ R.own.rc i p
    rw [hst₁ i p, hv₁']
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  · show drawsFit ((declsTo Fy.first.blocksInOrder 2 ++ declsTo Fy.shared.blocksInOrder 3) ++ [])
      (m₁.st.heard ++ m₂.st.heard) = true
    rw [List.append_nil, drawsFit_append, List.take_left' l₁, List.drop_left' l₁, hF₁', hF₂']
    rfl
  · show (m₁.seen ++ m₂.seen).map (·.drawn) = m₁.st.heard ++ m₂.st.heard
    rw [List.map_append, hseen₁, hseen₂]
  · show m₁.loc = (m₁.st.heard ++ m₂.st.heard).take (declsTo Fy.first.blocksInOrder 2).length ++
      (m₁.st.heard ++ m₂.st.heard).drop
        (declsTo Fy.first.blocksInOrder 2 ++ declsTo Fy.shared.blocksInOrder 3).length
    rw [List.take_left' l₁, List.length_append, ← l₁, ← l₂, ← List.length_append,
      List.drop_length, List.append_nil]
    exact hloc₁'
  · show VerifiableInference.Desc.foldBlocks Fy.lastChainFirstTreeNumber [] st₀
      ((m₁.seen ++ m₂.seen).drop (declsTo Fy.first.blocksInOrder 2 ++ declsTo Fy.shared.blocksInOrder 3).length)
      [] = .ok (st₀, [], [])
    have e1 : (m₁.seen ++ m₂.seen).length =
        (declsTo Fy.first.blocksInOrder 2 ++ declsTo Fy.shared.blocksInOrder 3).length := by
      rw [List.length_append, List.length_append, ← l₁, ← l₂, ← hseen₁, ← hseen₂,
        List.length_map, List.length_map]
    rw [← e1, List.drop_length]
    rfl

end

/-! ## 5 The rule, called -/

/-- No part of the row has a stop: so no list of challenges is withheld. -/
theorem silent_row (w₀ : Wit₀) (rc : UInt64) (x : Nat) (ρ' : Draws) :
    silentAt Fy Hy w₀ rc x ρ' = none := by
  unfold silentAt
  cases Hy.trace w₀ x with
  | none => rfl
  | some tr => rfl

/-- **`runC` RETURNS AT THE ROW, OUT OF THE THREADS' DEBTS AND SEAMS**: `file_runs`, with every
premise met at the inputs of `RelY`, at all coins, at every list of challenges that has its rounds'
shapes (`Draws.due`: the one premise that stays: it says at which lists the rule speaks). -/
theorem runs_by_threads : ∀ w₀ rc x, RelY w₀ rc x → ∀ (k : Coins By) ρ', ρ'.due Fy = true →
    ∃ r, runC Fy By Hy w₀ rc x k ρ' = .ok r := by
  intro w₀ rc x h k ρ' hρ
  have hs := silent_row w₀ rc x ρ'
  obtain ⟨R, hR, h₁, h₂, h₃⟩ := ready_row w₀ rc x k h
  have hP : PlanServes Hy w₀ rc R :=
    serves_of_sk (by rw [h₁]; exact fits_Ky.1) (by rw [h₂]; exact fits_Ky.2.1)
      (by rw [h₃]; exact fits_Ky.2.2) (by rw [h₁]; exact inTime_Ky.1)
      (by rw [h₂]; exact inTime_Ky.2.1) (by rw [h₃]; exact inTime_Ky.2.2)
      fun _ => ⟨_, rfl, rfl⟩
  exact file_runs (sits_row R.own R.common) (by with_unfolding_all rfl) (owes₁ R.own)
    (owes₂ R.common) (owes₃ R.own) hR (by with_unfolding_all rfl) hρ hs hP (enters₁_row hR)
    (enters₂_row hR) door_row

end Toy
end ProofFile.Honest

#print axioms ProofFile.Honest.plays_of_playsOn
#print axioms ProofFile.Honest.Toy.storedOk_Hy
#print axioms ProofFile.Honest.Toy.owes₁
#print axioms ProofFile.Honest.Toy.find_look
#print axioms ProofFile.Honest.Toy.parts₂
#print axioms ProofFile.Honest.Toy.look_trees
#print axioms ProofFile.Honest.Toy.store_plays
#print axioms ProofFile.Honest.Toy.owes₂
#print axioms ProofFile.Honest.Toy.parts₃
#print axioms ProofFile.Honest.Toy.send_trees₃
#print axioms ProofFile.Honest.Toy.runs_tell₃
#print axioms ProofFile.Honest.Toy.owes₃
#print axioms ProofFile.Honest.Toy.sits_row
#print axioms ProofFile.Honest.Toy.enters₁_row
#print axioms ProofFile.Honest.Toy.enters₂_row
#print axioms ProofFile.Honest.Toy.door_row
#print axioms ProofFile.Honest.Toy.silent_row
#print axioms ProofFile.Honest.Toy.runs_by_threads
#print axioms ProofFile.Honest.Toy.tableL
#print axioms ProofFile.Honest.Toy.T₁y
#print axioms ProofFile.Honest.Toy.T₂y
#print axioms ProofFile.Honest.Toy.T₃y
