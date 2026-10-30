-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookAtCut.lean:
bookAt (Johnson/Desc/First/Borders.lean: a fixed clause of the promise
at every border of the
first chain), AT EVERY CUT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, at the numbers off what the
blocks tell (its Numbers.withTold), of the verifier's state that the fold hands on from the first
state. UNDER K1Told AND hM (Johnson/IMR/MsgsSeat.lean, Johnson/IMR/MsgsCut.lean).

MARK WELL: IT STANDS OVER TWO FILES
(Johnson/Desc/First/BookFit.lean · BookNumbers.lean; FenceFit.lean is
not imported); THESE TWO STAND OVER Johnson/Desc/First/Borders.lean
(over another version of the base files another Borders.lean has to be laid too).



  toldOf l := l.map fun b => b.oracles.flatten: Numbers.withTold's letter "told".
  msgsTold_eq: msgsTold (toldOf l) k = ((l.take k).map toldMsgs).sum. treesTold_eq: blocksOk (l.take
      k) = true → treesTold (toldOf l) k = rootsOf (declOf (l.take k)): by told_len
          (Johnson/Desc/Sound/ToldCount.lean).
  bookAt_at_cut: **O : Open … · K1Told · k ≤ (frontOf c).length · borderOf ps ps[k]? = k · blocksOk
      (c.blocksInOrder.take k) = true · hM at ProofFile.startS Z p · foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p)
      rs cols = .ok r ⇒ bookAt (N.withTold ps (toldOf c.blocksInOrder)) ps[k]? r.1 = true.** AT EVERY o, N,
      ps.
THE THREE CONJUNCTS. As many trees as told: roots_at_cut_paid (Johnson/IMR/RootsSeat.lean) ·
open_roots (as many roots as trees) and start_empty · treesTold_eq. As many places as messages:
open_has. As many messages as told: msgs_at_cut_but · start_none (SizeSeat.lean) ·
msgsTold_eq.
PREMISES, AND WHO CAN PAY. K1Told · hM: see Johnson/IMR/MsgsCut.lean's head. borderOf ps ps[k]? = k:
holds
where the list of places has no place twice in front of k. blocksOk:
F.planOk.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription o's value. User: the table of
joints (FoldFacts). Letters: N, ps.



Compiled with the whole library.
Limits. Nothing behind the last link. No member. Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.MsgsCut
import Johnson.IMR.WalkGivesAt
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.Sound.ToldCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S treesTold msgsTold bookAt borderOf Numbers)
open Meaning.K2 (frontOf)
open Johnson.G.OfPlan (rootsOf)
open H2K.First (declOf)

/-- What the blocks of a list tell, block by block: Numbers.withTold's letter "told". -/
def toldOf {T Cl : Type} (l : List (Block T Cl)) : List (List Oracle) :=
  l.map fun b => b.oracles.flatten

theorem msgsTold_eq {T Cl : Type} (l : List (Block T Cl)) (k : Nat) :
    msgsTold (toldOf l) k = ((l.take k).map toldMsgs).sum := by
  unfold msgsTold toldOf
  rw [← List.map_take, List.map_map]
  rfl

theorem treesTold_eq {T Cl : Type} (l : List (Block T Cl)) (k : Nat)
    (h : blocksOk (l.take k) = true) : treesTold (toldOf l) k = rootsOf (declOf (l.take k)) := by
  have e := Sound.told_len (l.take k) h
  unfold treesTold toldOf
  rw [← List.map_take, List.map_map]
  have e2 : (oraclesOf (l.take k)).length =
      ((l.take k).map ((fun os : List Oracle => os.length) ∘ fun b => b.oracles.flatten)).sum := by
    unfold oraclesOf
    rw [List.length_flatMap]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    show (b.oracles.flatMap id).length = b.oracles.flatten.length
    rw [List.flatMap_id]
  rw [← e2, e]
  rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A' : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **PART 5's bookAt AT EVERY CUT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK**, at the numbers off
what the blocks tell. -/
theorem bookAt_at_cut (O : IM.Open o pol lay KL F Z Bs base c A' B) (h1 : K1Told) (N : Numbers)
    (ps : List Place) (k : Nat) (hk : k ≤ (frontOf c).length) (hb : borderOf ps ps[k]? = k)
    (hp : blocksOk (c.blocksInOrder.take k) = true) (ft : Nat) (p : ProofFile.InstPub) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn)
    (hM : ∀ (j : Nat) (b : Block S ProofFile.Cl), j < k → c.blocksInOrder[j]? = some b → Marked drawsPos b →
      ∀ r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn,
        foldBlocks ft (c.blocksInOrder.take j) (ProofFile.startS Z p) rs cols = .ok r₀ →
        foldBlocks ft (c.blocksInOrder.take (j + 1)) (ProofFile.startS Z p) rs cols = .ok r₁ →
        r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b)
    (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok r) :
    bookAt (N.withTold ps (toldOf c.blocksInOrder)) ps[k]? r.1 = true := by
  have hpl : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true := fun b hb' => by
    have t := List.all_eq_true.1 hp b hb'
    rw [Bool.and_eq_true] at t
    exact t.1
  have e1 := roots_at_cut_paid O k hk hpl ft _ rs cols r h
  rw [(Meaning.K2.start_empty O.pub p).2, Nat.zero_add] at e1
  have e2 := Meaning.K2.open_roots O hk h
  have e3 := Meaning.K2.open_has O hk h
  have e4 := msgs_at_cut_but O h1 k hk hpl ft _ rs cols hM r h
  rw [Meaning.K2.start_none O.pub p, Nat.zero_add] at e4
  unfold bookAt
  show (r.1.book.trees.size == treesTold (toldOf c.blocksInOrder) (borderOf ps ps[k]?) &&
    r.1.book.place.size == r.1.st.oracles.size &&
    r.1.st.oracles.size == msgsTold (toldOf c.blocksInOrder) (borderOf ps ps[k]?)) = true
  rw [hb, treesTold_eq _ _ hp, msgsTold_eq, ← e2, e1, e3, e4]
  simp

end

#print axioms msgsTold_eq
#print axioms treesTold_eq
#print axioms bookAt_at_cut

end Meaning.Carry
