-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ClauseNext.lean: WHAT A CLAUSE OF THE LETTER `Said` OWES AT EVERY
BORDER, THROUGH OTHER KINDS' BLOCKS.
A kind may add a clause `C` to what is said of the prover's run, because a law of its own reads it.
`Said` is one letter for a whole chain, so `C` has to be carried over every member of that chain.
`ClauseCarried` is that debt at one member. `ClauseDebt` is the debt of a whole chain: `C` at the
start, and carried over every member.
`Leaves` is the usual way to pay it at another kind's member: `C` reads the stand through a map `π`,
and that member leaves `π` as it was. `ClauseOf` is a clause of that form.
`saidNext_walk_and` and `saidNext_field_and` say that the threads' two letters stay carried with
`C` beside them. Who pays at each member is for the kind that lays `C` to name.

Limits.
  * These are definitions and conditional lemmas on our own definitions. None is one of the library's
    goals. Nothing here is shown of any clause or any thread.
  * WHAT CANNOT GO THROUGH `Said`. `ClauseCarried` is asked at every list of challenges that a member
    can draw, and no acceptance is among its premises. So a clause that a member's own step makes
    true, such as «this challenge is not 0» at the member that draws it, cannot pay the debt there:
    `play` returns at 0 too. Such a sentence is read off `Thr`, whose clause `Made` says that the
    folds in front returned, or it goes to the third family `J` (Honest/Thread/ShapeJ.lean).
  * A clause that holds of nothing is carried for nothing, and then `ClauseDebt.start` cannot be met.
  * `fromThreads_walk` and the door are typed at the bare letter. `FromThreads` takes any letters, so
    a lot that lays a clause builds it at `SaidWalkAnd` itself.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WalkedTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 1 The debt -/

/-- **The clause `C` is carried over member number `b`**, wherever `Said` and `C` hold in front. The
state behind the member is the one that `SaidNext` names. A definition, meant as a hypothesis. -/
def ClauseCarried (Said C : Nat → Coins Bk → Mid W X → Prop) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E → Said b k m → C b k m →
    drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols → C (b + 1) k (y.2.took cols)

/-- **The debt of a whole chain.** `First`: the stands at which the chain begins; at the last chain
they come from the door. A definition, meant as a hypothesis. -/
structure ClauseDebt (Said C : Nat → Coins Bk → Mid W X → Prop)
    (First : Coins Bk → Mid W X → Prop) : Prop where
  start : ∀ k m, First k m → T.valid m.st.input → C 0 k m
  carried : ∀ b, b < T.bs.length → ClauseCarried T Said C b

/-- A clause that is carried by itself owes nothing more beside any letter. -/
theorem clauseCarried_of_saidNext {Said C : Nat → Coins Bk → Mid W X → Prop} {b : Nat}
    (h : SaidNext T C b) : ClauseCarried T Said C b :=
  fun blk hblk k s m E ds y cols hA _ hC hd hM => h blk hblk k s m E ds y cols hA hC hd hM

/-- **`SaidNext` at a letter with a clause beside it.** -/
theorem saidNext_clause {Said C : Nat → Coins Bk → Mid W X → Prop} {b : Nat}
    (h : SaidNext T Said b) (hC : ClauseCarried T Said C b) :
    SaidNext T (fun b k m => Said b k m ∧ C b k m) b :=
  fun blk hblk k s m E ds y cols hA hS hd hM =>
    ⟨h blk hblk k s m E ds y cols hA hS.1 hd hM,
      hC blk hblk k s m E ds y cols hA hS.1 hS.2 hd hM⟩

/-! ## 2 At another kind's member -/

/-- **Member number `b` leaves `π` as it was.** A definition, meant as a hypothesis. -/
def Leaves {α : Type} (Said : Nat → Coins Bk → Mid W X → Prop) (π : Mid W X → α) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E → Said b k m →
    drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols → π (y.2.took cols) = π m

/-- **A clause that reads the stand through `π`.** A definition: a form of clause. -/
def ClauseOf {α : Type} (π : Mid W X → α) (P : Nat → Coins Bk → α → Prop) (b : Nat) (k : Coins Bk)
    (m : Mid W X) : Prop :=
  P b k (π m)

/-- At a member that leaves `π`, a clause of that form is carried if its own sentence goes from the
border in front to the border behind. -/
theorem clauseCarried_of_leaves {α : Type} {Said : Nat → Coins Bk → Mid W X → Prop}
    {π : Mid W X → α} {P : Nat → Coins Bk → α → Prop} {b : Nat} (hL : Leaves T Said π b)
    (hP : ∀ k a, P b k a → P (b + 1) k a) : ClauseCarried T Said (ClauseOf π P) b := by
  intro blk hblk k s m E ds y cols hA hS hC hd hM
  show P (b + 1) k (π (y.2.took cols))
  rw [hL blk hblk k s m E ds y cols hA hS hd hM]
  exact hP k _ hC

/-- Every member leaves the input. -/
theorem leaves_input (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) :
    Leaves T Said (fun m => m.st.input) b := by
  intro blk _ k s m E ds y cols _ _ _ hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  exact (play_mid _ _ _ _ _ hy).1

theorem roundsTo_le (bs : List (Block S Cl)) {a c : Nat} (h : a ≤ c) :
    roundsTo bs a ≤ roundsTo bs c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold roundsTo declsTo
  rw [List.take_add, List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

/-- Every member behind border `b₀` leaves the first `n` challenges heard, where these were heard by
`b₀`: one law for every other kind's block. -/
theorem leaves_heard (Said : Nat → Coins Bk → Mid W X → Prop) {n b₀ b : Nat}
    (hn : n ≤ T.front + roundsTo T.bs b₀) (hb : b₀ ≤ b) :
    Leaves T Said (fun m => m.st.heard.take n) b := by
  intro blk _ k s m E ds y cols hA _ _ hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have hl := T.heard_length hA.2.1
  have hm := roundsTo_le T.bs hb
  show y.2.st.heard.take n = _
  rw [play_heard _ _ _ _ _ hy, List.take_append_of_le_length (by omega)]

/-- The same for the first `n` rounds seen. -/
theorem leaves_seen (Said : Nat → Coins Bk → Mid W X → Prop) {n b₀ b : Nat}
    (hn : n ≤ T.front + roundsTo T.bs b₀) (hb : b₀ ≤ b) :
    Leaves T Said (fun m => m.seen.take n) b := by
  intro blk _ k s m E ds y cols hA _ _ hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  obtain ⟨-, -, hs⟩ := play_mid _ _ _ _ _ hy
  have hl := T.heard_length hA.2.1
  have hm := roundsTo_le T.bs hb
  have hmap := hA.2.2.2.2.1.1
  have e : m.seen.length = m.st.heard.length := by
    rw [← hmap, List.length_map]
  show y.2.seen.take n = _
  rw [hs, List.take_append_of_le_length (by omega)]

/-! ## 3 The letters of the threads with a clause beside them -/

/-- The field letter and a clause. A definition: a filling of the letter `Said`. -/
def SaidFieldAnd (B : Coins Bk → Mid W X → List OpenedColumn → Prop)
    (C : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (k : Coins Bk) (m : Mid W X) : Prop :=
  SaidField T B b k m ∧ C b k m

/-- `SaidWalk` and a clause. A definition: a filling of the letter `Said`. -/
def SaidWalkAnd (B : Coins Bk → Mid W X → List OpenedColumn → Prop) (m₀ : Coins Bk → Mid W X)
    (C : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (k : Coins Bk) (m : Mid W X) : Prop :=
  SaidWalk T B m₀ b k m ∧ C b k m

/-- **`SaidNext` at the field letter with a clause**: the letter's own premises, and the clause's
debt at this member. -/
theorem saidNext_field_and {n b : Nat} {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    {C : Nat → Coins Bk → Mid W X → Prop} (hfit : T.fits n = true) (hb : b ≤ n)
    (hT : TreesNext T (SaidFieldAnd T B C) b) (hK : BaseKept T B b)
    (ho : T.opensAvailable (b + 1) = true)
    (hdp : ∀ (k : Coins Bk) (m : Mid W X), DepthsAt T (b + 1) k m)
    (hC : ClauseCarried T (SaidField T B) C b) : SaidNext T (SaidFieldAnd T B C) b := by
  intro blk hblk k s m E ds y cols hA hS hd hM
  have hTr := hT blk hblk k s m E ds y cols hA hS hd hM
  obtain ⟨hF, hc⟩ := hS
  have hF' := hF
  obtain ⟨hOk, base, hB, hL⟩ := hF'
  exact ⟨⟨saidNext_ok T b blk hblk k s m E ds y cols hA hOk hd hM, base,
    hK blk hblk k m E ds y cols base hM hB,
    field_all_next T hfit hb hblk hA hM hTr hL ho (hdp k _)⟩,
    hC blk hblk k s m E ds y cols hA hF hc hd hM⟩

/-- **`SaidNext` at `SaidWalk` with a clause**: the letter's own premises, and the clause's debt at
this member. -/
theorem saidNext_walk_and {n b : Nat} {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    {m₀ : Coins Bk → Mid W X} {C : Nat → Coins Bk → Mid W X → Prop}
    (hfit : T.fits n = true) (hb : b ≤ n) (hT : TreesNext T (SaidWalkAnd T B m₀ C) b)
    (hK : BaseKept T B b) (ho : T.opensAvailable (b + 1) = true)
    (hdp : ∀ k m, WalkedTo T m₀ k (b + 1) m → DepthsAt T (b + 1) k m)
    (hC : ClauseCarried T (SaidWalk T B m₀) C b) : SaidNext T (SaidWalkAnd T B m₀ C) b := by
  intro blk hblk k s m E ds y cols hA hS hd hM
  have hTr := hT blk hblk k s m E ds y cols hA hS hd hM
  obtain ⟨hW₀, hc⟩ := hS
  have hW₁ := hW₀
  obtain ⟨⟨hOk, base, hB, hL⟩, hW⟩ := hW₁
  have hN : WalkedTo T m₀ k (b + 1) (y.2.took cols) :=
    WalkedTo.next hW hblk hA.2.2.2.2.1.2.2.1 hA.2.1 hd hM (T.hand_next hfit hb hA hM hTr)
  exact ⟨⟨⟨saidNext_ok T b blk hblk k s m E ds y cols hA hOk hd hM, base,
    hK blk hblk k m E ds y cols base hM hB,
    field_all_next T hfit hb hblk hA hM hTr hL ho (hdp k _ hN)⟩, hN⟩,
    hC blk hblk k s m E ds y cols hA hW₀ hc hd hM⟩

/-- **The same at every number, from `OwesS` at the letter**, with no stop at the members that have
new trees. -/
theorem saidNext_walk_and_of_owes {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    {m₀ : Coins Bk → Mid W X} {C : Nat → Coins Bk → Mid W X → Prop}
    (hfit : T.fits T.bs.length = true) (o : OwesS T (SaidWalkAnd T B m₀ C))
    (hst : ∀ b, b < T.bs.length → T.fresh b ≠ [] → ∀ blk, T.bs[b]? = some blk →
      ∀ (m : Mid W X) (ds : List Fmt.Drawn),
        chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hK : ∀ b, b < T.bs.length → BaseKept T B b)
    (ho : ∀ b, b < T.bs.length → T.opensAvailable (b + 1) = true)
    (hdp : ∀ b, b < T.bs.length → ∀ k m, WalkedTo T m₀ k (b + 1) m → DepthsAt T (b + 1) k m)
    (hC : ∀ b, b < T.bs.length → ClauseCarried T (SaidWalk T B m₀) C b) :
    ∀ b, SaidNext T (SaidWalkAnd T B m₀ C) b := by
  intro b blk hblk
  have hj := lt_of_member T hblk
  refine saidNext_walk_and T hfit (Nat.le_of_lt hj) ?_ (hK b hj) (ho b hj) (hdp b hj) (hC b hj)
    blk hblk
  by_cases h : T.fresh b = []
  · exact treesNext_of_fresh_nil T h
  · exact treesNext_of_playsS T (o b hj).1 (hst b hj h)

/-- The letter with a clause, at a start. -/
theorem saidWalkAnd_start {m₀ : Coins Bk → Mid W X} {C : Nat → Coins Bk → Mid W X → Prop}
    {k : Coins Bk} {m : Mid W X} (h : m.seen = []) (e : m₀ k = { m with opened := some [] })
    (hC : C 0 k { m with opened := some [] }) :
    SaidWalkAnd T BaseNil m₀ C 0 k { m with opened := some [] } :=
  ⟨saidWalk_start T h e, hC⟩

/-- `OneStand` stays at a letter with a clause beside it. -/
theorem oneStand_walk_and {B : Coins Bk → Mid W X → List OpenedColumn → Prop} {m₀ : Coins Bk → Mid W X}
    {C : Nat → Coins Bk → Mid W X → Prop} {n : Nat}
    (ho : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hdp : ∀ k b, b ≤ n → ∀ m, WalkedTo T m₀ k b m → DepthsAt T b k m) :
    OneStand (SaidWalkAnd T B m₀ C) n :=
  fun k _ _ a a' hi hh => oneStand_walk T (B := B) ho hdp k _ _ a.1 a'.1 hi hh

/-- `OneState` stays too. `hfun`: the chain begins at one state. -/
theorem oneState_walk_and {B : Coins Bk → Mid W X → List OpenedColumn → Prop} {m₀ : Coins Bk → Mid W X}
    {C : Nat → Coins Bk → Mid W X → Prop} {n : Nat}
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁)
    (ho : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hdp : ∀ k b, b ≤ n → ∀ m, WalkedTo T m₀ k b m → DepthsAt T b k m) :
    OneState T (SaidWalkAnd T B m₀ C) n :=
  oneState_at T (oneStand_walk_and T ho hdp) hfun (ho n (Nat.le_refl n))
    fun k _ m _ h => hdp k n (Nat.le_refl n) m h.2.1.2

end ProofFile.Honest

#print axioms ProofFile.Honest.ClauseCarried
#print axioms ProofFile.Honest.ClauseDebt
#print axioms ProofFile.Honest.Leaves
#print axioms ProofFile.Honest.ClauseOf
#print axioms ProofFile.Honest.clauseCarried_of_leaves
#print axioms ProofFile.Honest.leaves_input
#print axioms ProofFile.Honest.SaidFieldAnd
#print axioms ProofFile.Honest.SaidWalkAnd
#print axioms ProofFile.Honest.saidNext_field_and
#print axioms ProofFile.Honest.saidNext_walk_and
#print axioms ProofFile.Honest.oneStand_walk_and
#print axioms ProofFile.Honest.oneState_walk_and
#print axioms ProofFile.Honest.clauseCarried_of_saidNext
#print axioms ProofFile.Honest.saidNext_clause
#print axioms ProofFile.Honest.roundsTo_le
#print axioms ProofFile.Honest.leaves_heard
#print axioms ProofFile.Honest.leaves_seen
#print axioms ProofFile.Honest.saidNext_walk_and_of_owes
#print axioms ProofFile.Honest.saidWalkAnd_start
