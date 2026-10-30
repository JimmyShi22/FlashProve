-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SampleSeatK2.lean: the code switch's blocks AS THEY ARE SUPPLIED TO THE PROOF
FILE's DESCRIPTION keep an invariant on the messages' stored sample rows (SampleChain.lean's
RowsInv Q), wherever the kind's own block does. A law file; no running text imports it.

The kind's block `codeSwitchKind p` stands alone at a later link's first call; at the head's link the quiet step
"opened" is joined behind it, and the quiet step that enters the head's link stands in another
kind's place; at the finish a quiet step is joined in front and one behind (K2C/Head.lean,
K2C/Finish.lean; Johnson/Desc/ProofFile/Lot/K2.lean's `pureAt`). These quiet steps change the
statement by a new group and by joins alone.

  newGroupG_smp, joinG_smp, joins_smp   K2's two calls of the ground, a run of joins: SameRows.
  firstFront_smp, finishFront_smp, firstBehind_smp   the fronts; the step behind a first call.
  enterHead_st, enterFin_st, openHead_st   entering and opening leave the statement.
  headFrontQ_smp, headOpenQ_smp, finishFrontQ_smp, finishBehindQ_smp   the four quiet steps.
  keepsInv_headOpened, keepsInv_finishPlace, keepsInv_atHead   the joined blocks.
  keepsInv_pureAt     every block that `P1K2.pureAt` makes, at the lot's own choice of what
                      follows a link's switch (nothing).
Limits: the premise hk (the kind's own decision keeps the invariant) is paid at QGood in
SampleChain.lean and at QGoodS in SampleChainS.lean. `pureMute` (the block that refuses where a
place's numbers cannot be made) is not treated: it never says yes. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.RowsGround
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Desc.ProofFile.Lot.K2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.Keeps1
open _root_.Tw.K2 (newGroupG joinG firstFront finishFront firstBehind dOf)

/-! ## K2's calls of the ground -/

theorem newGroupG_smp {S S' : Statement} {c m g : Nat} (h : newGroupG S c m = .ok (S', g)) :
    SameRows S S' := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    cases h
    exact newGroupP_rows (dOf S) d c m _ hd
  · cases h

theorem joinG_smp {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g o kept = .ok S') :
    SameRows S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    exact joinP_rows (dOf S) d g o kept hd
  · cases h

theorem joins_smp {α : Type} (f : α → Nat × Nat × Bool) : ∀ (l : List α) (S S' : Statement),
    l.foldlM (fun S y => joinG S (f y).1 (f y).2.1 (f y).2.2) S = .ok S' → SameRows S S'
  | [], S, S', h => by
    cases h
    exact SameRows.refl S
  | y :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    cases h1 : joinG S (f y).1 (f y).2.1 (f y).2.2 with
    | error e => rw [h1] at h; cases h
    | ok S1 =>
      rw [h1] at h
      exact (joinG_smp h1).trans (joins_smp f l S1 S' h)

theorem firstFront_smp {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S f = .ok x) : SameRows S x.st := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_smp a.opened

theorem finishFront_smp {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : finishFront S f = .ok x) : SameRows S x.st := by
  obtain ⟨G, S', g, a⟩ := (_root_.Tw.K2.finishFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_smp a.opened

theorem firstBehind_smp {S S' : Statement} {x : _root_.Tw.K2.Front} {s : Switched}
    {plain : List E} {f : ReqFrame} {mine : Array Nat}
    (h : firstBehind S x s plain = .ok (S', f, mine)) : SameRows S S' := by
  obtain ⟨mask, a⟩ := (_root_.Tw.K2.firstBehind_iff S x s plain S' f mine).1 h
  exact joins_smp (fun y : Params.ReqMessage × Nat => (x.f.group, y.2, decide (0 < y.1.life))) _ S
    S' a.joins

/-! ## Entering and opening -/

theorem mark_st (s : S) (n : String) : (s.mark n).st = s.st := by
  unfold S.mark
  split <;> rfl

theorem enterHead_st (s : S) (tl : HTailF2) : (s.enterHead tl).st = s.st := by
  unfold S.enterHead
  split
  · rfl
  · exact mark_st s _

theorem enterFin_st (s : S) : s.enterFin.st = s.st := by
  unfold S.enterFin
  split
  · rfl
  · exact mark_st s _

theorem openHead_st (s : S) : s.openHead.st = s.st := by
  unfold S.openHead
  split
  · split
    · exact mark_st s _
    · rfl
  · exact mark_st s _

/-! ## The four quiet steps -/

theorem headFrontQ_smp {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    SameRows s.st s'.st := by
  obtain ⟨x, s₁, a, A⟩ := (headFrontQ_iff tl s s').1 h
  rw [A.out]
  exact firstFront_smp A.front

theorem finishFrontQ_smp {s s' : S} (h : finishFrontQ s = .ok s') : SameRows s.st s'.st := by
  obtain ⟨G, x, s₁, a, A⟩ := (finishFrontQ_iff s s').1 h
  rw [A.out]
  exact finishFront_smp A.front

theorem finishBehindQ_smp {s s' : S} (h : finishBehindQ s = .ok s') : SameRows s.st s'.st := by
  obtain ⟨a, m, -, -, rfl⟩ := (finishBehindQ_iff s s').1 h
  exact SameRows.refl _

theorem headOpenQ_smp {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    SameRows s.st s'.st := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, A⟩ := (headOpenQ_iff P s s').1 h
  rw [A.out']
  exact firstBehind_smp A.behind

/-! ## The supplied blocks -/

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {Cl : Type}

theorem keepsInv_fn {f : S → Except String S} (h : ∀ s s', f s = .ok s' → SameRows s.st s'.st) :
    ∀ s s', f s = .ok s' → Inv Q s → Inv Q s' := fun a b hy hg => rowsInv_rows (h a b hy) hg

theorem keepsInv_headOpened (name : String) (place : VerifiableInference.Desc.Place)
    (P : HeadPar) : KeepsInv Q (headOpened name place P : Block S Cl) :=
  fun _ _ _ _ _ hy hg => rowsInv_rows (headOpenQ_smp hy) hg

theorem keepsInv_atHead (p : P2) (hk : KeepsInv Q (codeSwitchKind p : Block S Cl)) (name : String)
    (place : VerifiableInference.Desc.Place) (P : HeadPar) :
    KeepsInv Q ((codeSwitchKind p : Block S Cl).andThen name (headOpened name place P)) :=
  keepsD_andThen name hk (keepsInv_headOpened name place P)

theorem keepsInv_finishPlace (p : P2) (hk : KeepsInv Q (codeSwitchKind p : Block S Cl)) :
    KeepsInv Q (finishPlace p : Block S Cl) :=
  keepsD_under (b := ((roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece
      finishFrontQ).andThen p.name (codeSwitchKind p)).andThen p.name
      (roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece finishBehindQ))
    rfl
    (keepsD_andThen _
      (keepsD_andThen _ (keepsD_quiet (keepsInv_fn fun _ _ => finishFrontQ_smp)) hk)
      (keepsD_quiet (keepsInv_fn fun _ _ => finishBehindQ_smp)))

/-- **Every block that the lot's maker makes at a place of the kind.** -/
theorem keepsInv_pureAt (hk : ∀ p : P2, KeepsInv Q (codeSwitchKind p : Block S Unit)) (G : ProofFile.Ground)
    (x : ProofFile.Spot × P2) (b : Block S Unit)
    (h : P1K2.pureAt (fun _ _ => some none) G x = some b) : KeepsInv Q b := by
  unfold P1K2.pureAt at h
  dsimp only at h
  split at h
  · cases h
    exact keepsD_under rfl (keepsInv_finishPlace x.2 (hk x.2))
  · obtain ⟨P, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact keepsD_under rfl (keepsInv_atHead x.2 (hk x.2) _ _ P)
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨l, -, ho⟩ := Option.bind_eq_some_iff.1 ho
    cases ho
    exact keepsD_under rfl (hk x.2)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keepsInv_pureAt
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_smp
