-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WalkedTo.lean: A LETTER THAT FIXES THE STAND. The last chain's
thread names the two earlier chains' last states as a function `ends` of the run, and that function
exists only where one run has one state (`OneState`, `OneStand`, Honest/Thread/OneState.lean).
`PlayedTo` (Honest/Small/PlayedTo.lean) fixes the stand where the field `opened` is `none`; the
field letter `SaidField` asks `some`, so the two hold together of no stand. `WalkedTo` is the stand
that is reached sub-protocol by sub-protocol from a given first stand, by `Thread.Moved`, with the
columns taken in behind each sub-protocol, and it is what the field letter can stand beside.

  `WalkedTo`, `WalkedTo.inv_succ`   the letter; what a stand behind a sub-protocol came from
  `Thread.reads_congr_at`   two sets of available tables give the same reads
  `walkedTo_unique`   one first stand, one input, one list of challenges heard: one stand
  `SaidWalk`, `oneStand_walk`, `oneState_walk`   the field letter and this one, and `OneState`
  `saidNext_walk`, `saidNext_walk_of_owes`   the letter's `SaidNext`
  `saidWalk_start`   the letter at a start

What these are. Definitions and conditional lemmas on our own definitions. None is one of the
library's goals.

Limits.
  * `m₀` is a letter: which first stand a chain takes is not said here.
  * `ho` and `hdp` are premises. `hdp` asks `DepthsAt` at the stands of this letter alone. They are
    shown here of no thread.
  * The letter's step names some set of tables at which `Thread.Hand` holds behind the sub-protocol.
    Where no set of tables has it the stand behind that sub-protocol is not of this letter.
  * That a stand of a run's walk (`walk`, Honest/Walk.lean) is such a stand is not said here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SaidField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

/-! ## 1 The letter -/

/-- **The stand at a border, reached from `m₀ k` sub-protocol by sub-protocol**, with each
sub-protocol's columns taken in behind it. A definition: a filling of the letter `Said`. -/
inductive WalkedTo {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (m₀ : Coins Bk → Mid W X) (k : Coins Bk) : Nat → Mid W X → Prop
  | start : WalkedTo T m₀ k 0 (m₀ k)
  | next {b : Nat} {blk : Block S Cl} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
      {y : List Played × Mid W X} {cols : List OpenedColumn} :
      WalkedTo T m₀ k b m → T.bs[b]? = some blk → E.sent = treesTo T.bs b → T.Fit b m →
      drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Hand (b + 1) k (y.2.took cols) (E.add y.1) →
      WalkedTo T m₀ k (b + 1) (y.2.took cols)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- What a stand behind a sub-protocol came from. -/
theorem WalkedTo.inv_succ {T : Thread Bk S Cl V W X Pb} {m₀ : Coins Bk → Mid W X} {k : Coins Bk}
    {b : Nat} {m : Mid W X} (h : WalkedTo T m₀ k (b + 1) m) :
    ∃ blk m₁ E ds y cols, WalkedTo T m₀ k b m₁ ∧ T.bs[b]? = some blk ∧
      E.sent = treesTo T.bs b ∧ T.Fit b m₁ ∧
      drawsFit blk.rounds ds = true ∧ T.Moved blk k m₁ E ds y cols ∧
      T.Hand (b + 1) k (y.2.took cols) (E.add y.1) ∧ m = y.2.took cols := by
  cases h with
  | next w hb hs hf hd hM hH => exact ⟨_, _, _, _, _, _, w, hb, hs, hf, hd, hM, hH, rfl⟩

/-! ## 2 One stand -/

/-- **Two sets of available tables give the same reads**, of rounds declared before border `n`. -/
theorem Thread.reads_congr_at {n : Nat} {k : Coins Bk} {m : Mid W X} {E E' : Env}
    (h : T.Hand n k m E) (h' : T.Hand n k m E') (ho : T.opensAvailable n = true)
    (hd : DepthsAt T n k m) {rs : List Fmt.DeclaredRound} (hrs : ∀ d ∈ rs, d ∈ declsTo T.bs n)
    (Rs : List Fmt.Drawn) :
    readsOf T.chain T.ft E.stored E.tree rs Rs = readsOf T.chain T.ft E'.stored E'.tree rs Rs := by
  have hst : E.stored = E'.stored :=
    funext fun i => funext fun x => (h.1 i x).trans (h'.1 i x).symm
  have ht : ∀ d ∈ rs, ∀ o ∈ d.opens,
      (E.tree o.2).map (·.1) = (E'.tree o.2).map (·.1) ∧
        ∀ x, x < 2 ^ o.1.a → (E.tree o.2).map (·.2.col x) = (E'.tree o.2).map (·.2.col x) := by
    intro d hdr o hom
    have hdm := hrs d hdr
    have hσ : o.2 ∈ T.hand n :=
      of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 ho d hdm) o hom)
    obtain ⟨pt, e, p, -⟩ := T.handAt_elim (h.2 o.2 hσ)
    obtain ⟨pt', e', p', -⟩ := T.handAt_elim (h'.2 o.2 hσ)
    obtain ⟨qt, f, c⟩ := T.col_of_handAt (h.2 o.2 hσ)
    obtain ⟨qt', f', c'⟩ := T.col_of_handAt (h'.2 o.2 hσ)
    obtain rfl : pt = qt := Option.some.inj (e.symm.trans f)
    obtain rfl : pt' = qt' := Option.some.inj (e'.symm.trans f')
    refine ⟨?_, fun x hx => ?_⟩
    · rw [e, e']
      show some pt.1 = some pt'.1
      rw [p, p']
    · have hx' : x < 2 ^ (T.tableAt o.2 k m).2.logLength := by
        rw [hd d hdm o hom]
        exact hx
      rw [e, e']
      show some (pt.2.col x) = some (pt'.2.col x)
      rw [c x hx', c' x hx']
  rw [hst]
  exact readsOf_congr T.chain T.ft E'.stored rs Rs ht

/-- **One first stand, one input, one list of challenges heard: one stand.** -/
theorem walkedTo_unique {m₀ : Coins Bk → Mid W X} {k : Coins Bk} {n : Nat}
    (ho : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hdp : ∀ b, b ≤ n → ∀ m, WalkedTo T m₀ k b m → DepthsAt T b k m) :
    ∀ b, b ≤ n → ∀ {m m' : Mid W X}, WalkedTo T m₀ k b m → WalkedTo T m₀ k b m' →
      m.st.input = m'.st.input → m.st.heard = m'.st.heard → m = m' := by
  intro b
  induction b with
  | zero =>
    intro _ m m' h h' _ _
    cases h
    cases h'
    rfl
  | succ b ih =>
    intro hb m m' h h' hi hh
    obtain ⟨blk, m₁, E, ds, y, c, w, hk, -, -, hd, hM, hH, rfl⟩ := h.inv_succ
    obtain ⟨blk', m₂, E', ds', y', c', w', hk', -, -, hd', hM', hH', rfl⟩ := h'.inv_succ
    obtain rfl : blk = blk' := Option.some.inj (hk.symm.trans hk')
    obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
    obtain ⟨⟨l', hl', hy'⟩, hc'⟩ := hM'
    obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
    obtain ⟨ei', -, -⟩ := play_mid _ _ _ _ _ hy'
    have eh := play_heard _ _ _ _ _ hy
    have eh' := play_heard _ _ _ _ _ hy'
    have hi₀ : m₁.st.input = m₂.st.input := by
      have q : y.2.st.input = y'.2.st.input := hi
      rw [ei, ei'] at q
      exact q
    have hh₀ : y.2.st.heard = y'.2.st.heard := hh
    rw [eh, eh'] at hh₀
    have hlen : ds.length = ds'.length := by
      rw [drawsFit_length _ _ hd, drawsFit_length _ _ hd']
    obtain ⟨e₁, e₂⟩ := List.append_inj' hh₀ hlen
    obtain rfl : m₁ = m₂ := ih (Nat.le_of_succ_le hb) w w' hi₀ e₁
    obtain rfl : ds = ds' := e₂
    obtain rfl : l = l' := Except.ok.inj (hl.symm.trans hl')
    obtain rfl : y = y' := Except.ok.inj (hy.symm.trans hy')
    have a : T.Hand (b + 1) k (y.2.took c) (E.add y.1) := hH
    have a' : T.Hand (b + 1) k (y.2.took c) (E'.add y.1) := hH'
    have hq := T.reads_congr_at a a' (ho _ hb) (hdp _ hb _ h) (rs := blk.rounds)
      (fun d hm => by
        rw [declsTo_succ hk]
        exact List.mem_append_right _ hm)
      ds
    rw [hq] at hc
    obtain rfl : c = c' := Except.ok.inj (hc.symm.trans hc')
    rfl

/-! ## 3 The two letters together -/

/-- **The field letter and this one.** A definition: a filling of the letter `Said`. -/
def SaidWalk (B : Coins Bk → Mid W X → List OpenedColumn → Prop) (m₀ : Coins Bk → Mid W X) (b : Nat)
    (k : Coins Bk) (m : Mid W X) : Prop :=
  SaidField T B b k m ∧ WalkedTo T m₀ k b m

/-- **`OneStand`, at the letter.** -/
theorem oneStand_walk {B : Coins Bk → Mid W X → List OpenedColumn → Prop} {m₀ : Coins Bk → Mid W X}
    {n : Nat} (ho : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hdp : ∀ k b, b ≤ n → ∀ m, WalkedTo T m₀ k b m → DepthsAt T b k m) :
    OneStand (SaidWalk T B m₀) n :=
  fun k _ _ a a' hi hh => walkedTo_unique T ho (hdp k) n (Nat.le_refl n) a.2 a'.2 hi hh

/-- **`OneState`, at the letter.** `hfun`: the chain begins at one state. -/
theorem oneState_walk {B : Coins Bk → Mid W X → List OpenedColumn → Prop} {m₀ : Coins Bk → Mid W X}
    {n : Nat} (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁)
    (ho : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hdp : ∀ k b, b ≤ n → ∀ m, WalkedTo T m₀ k b m → DepthsAt T b k m) :
    OneState T (SaidWalk T B m₀) n :=
  oneState_at T (oneStand_walk T ho hdp) hfun (ho n (Nat.le_refl n))
    fun k _ m _ h => hdp k n (Nat.le_refl n) m h.2.2

/-! ## 4 The letter is carried -/

/-- **`SaidNext` at the letter, at one number.** `hdp` asks `DepthsAt` at this letter's stands. -/
theorem saidNext_walk {n b : Nat} {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    {m₀ : Coins Bk → Mid W X} (hfit : T.fits n = true) (hb : b ≤ n)
    (hT : TreesNext T (SaidWalk T B m₀) b) (hK : BaseKept T B b)
    (ho : T.opensAvailable (b + 1) = true)
    (hdp : ∀ k m, WalkedTo T m₀ k (b + 1) m → DepthsAt T (b + 1) k m) :
    SaidNext T (SaidWalk T B m₀) b := by
  intro blk hblk k s m E ds y cols hA hS hd hM
  have hTr := hT blk hblk k s m E ds y cols hA hS hd hM
  obtain ⟨⟨hOk, base, hB, hL⟩, hW⟩ := hS
  have hN : WalkedTo T m₀ k (b + 1) (y.2.took cols) :=
    WalkedTo.next hW hblk hA.2.2.2.2.1.2.2.1 hA.2.1 hd hM (T.hand_next hfit hb hA hM hTr)
  exact ⟨⟨saidNext_ok T b blk hblk k s m E ds y cols hA hOk hd hM, base,
    hK blk hblk k m E ds y cols base hM hB,
    field_all_next T hfit hb hblk hA hM hTr hL ho (hdp k _ hN)⟩, hN⟩

/-- **The same at every number, from `OwesS` at the letter**, with no stop at the members that have
new trees. -/
theorem saidNext_walk_of_owes {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    {m₀ : Coins Bk → Mid W X} (hfit : T.fits T.bs.length = true)
    (o : OwesS T (SaidWalk T B m₀))
    (hst : ∀ b, b < T.bs.length → T.fresh b ≠ [] → ∀ blk, T.bs[b]? = some blk →
      ∀ (m : Mid W X) (ds : List Fmt.Drawn),
        chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hK : ∀ b, b < T.bs.length → BaseKept T B b)
    (ho : ∀ b, b < T.bs.length → T.opensAvailable (b + 1) = true)
    (hdp : ∀ b, b < T.bs.length → ∀ k m, WalkedTo T m₀ k (b + 1) m → DepthsAt T (b + 1) k m) :
    ∀ b, SaidNext T (SaidWalk T B m₀) b := by
  intro b blk hblk
  have hj := lt_of_member T hblk
  refine saidNext_walk T hfit (Nat.le_of_lt hj) ?_ (hK b hj) (ho b hj) (hdp b hj) blk hblk
  by_cases h : T.fresh b = []
  · exact treesNext_of_fresh_nil T h
  · exact treesNext_of_playsS T (o b hj).1 (hst b hj h)

/-! ## 5 At a start -/

/-- **The letter at a start that has seen nothing, with the field laid at `some []`.** -/
theorem saidWalk_start {m₀ : Coins Bk → Mid W X} {k : Coins Bk} {m : Mid W X} (h : m.seen = [])
    (e : m₀ k = { m with opened := some [] }) :
    SaidWalk T BaseNil m₀ 0 k { m with opened := some [] } :=
  ⟨saidField_start T h, e ▸ WalkedTo.start⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.WalkedTo
#print axioms ProofFile.Honest.WalkedTo.inv_succ
#print axioms ProofFile.Honest.Thread.reads_congr_at
#print axioms ProofFile.Honest.walkedTo_unique
#print axioms ProofFile.Honest.SaidWalk
#print axioms ProofFile.Honest.oneStand_walk
#print axioms ProofFile.Honest.oneState_walk
#print axioms ProofFile.Honest.saidNext_walk
#print axioms ProofFile.Honest.saidNext_walk_of_owes
#print axioms ProofFile.Honest.saidWalk_start
