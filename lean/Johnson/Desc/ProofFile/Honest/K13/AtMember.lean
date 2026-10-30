-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/AtMember.lean: kind K13, the members' batching: THE ROW's LEMMA
(Inner.lean of this folder) AT THE MEMBER ITSELF: where the value of the proof file's IOP as written
in Lean is opened (`IM.Open`, Johnson/IMR/: the public data Z, the first chain c₁ and the rest, as
the maker lays them), a member of the first chain at the place "M:3" has the kind's rounds, and its
own step accepts what the frame's `play` shows of the kind's row. Statements with their proofs:
`k13_step` and `k13_step_all` (Inner.lean of this folder) at that member, by the law on the member
at a lot's place (Johnson/Desc/ProofFile/Honest/Member/Uses.lean: `k13_m3_alone`, `k13_at_m3`;
AtLot.lean: `alone_gives`).
Main names:
  `k13_member_fields`: the member's rounds and oracle messages are the kind's.
  `k13_member_step`: **the statement**, at any W that meets hu and hrows.
  `k13_member_step_all`: **the same at every coin.**

What is not claimed. That `onlineDescription` returns a value, or that `IM.Open` holds of one: a premise.
That a member stands at the place: a premise (hm, hp); the place is written out: it is `k13Place
(whereOf Z)`, at which the side takes its member, by unfolding. Where the plan's pile has one row
the chain has no place of this kind (Johnson/Desc/K13/Kind.lean), so that premise cannot be met and
both statements are idle there. The member's test on the plan is not treated. The premises of
`k13_step` and `k13_step_all` stay premises, with one more: the state in front bears no mark of
failure. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Inner
import Johnson.Desc.ProofFile.Honest.Member.Uses
import Johnson.Desc.K13.Law.Tile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (battRounds St whereOf)
open VerifiableInference.Desc.K13.Law (Wit ρg Holds dOf atM3_rounds)
open VerifiableInference.Desc.K13.Honest (maskAt withClaim rowReads withTaken pileBelowC)
open ProofFile.Honest.AtPlace (k13_m3_alone k13_at_m3 alone_gives)

variable {W₀ Rc Xi Tr X : Type}
variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
  {base : List (Block S Cl)} {c₁ : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- The member's rounds and oracle messages are the kind's. -/
theorem k13_member_fields (O : IM.Open o pol lay KL F Z Bs base c₁ A B) {mem : Block S Cl}
    (hm : mem ∈ c₁.blocksInOrder) (hp : mem.place = ⟨1, none, 3, .K13⟩) :
    mem.rounds = battRounds (whereOf Z) ∧
      mem.oracles = List.replicate (2 + (whereOf Z).lin.kCol) [] := by
  obtain ⟨x, hF, hA⟩ := k13_m3_alone O hm hp
  obtain ⟨-, -, h3, h4, -⟩ := alone_gives sameReply x mem _ _ _ hF hA
  exact ⟨h3.trans (atM3_rounds (Cl := Unit) (whereOf Z)),
    h4.trans (atM3_oracles (Cl := Unit) (whereOf Z))⟩

/-- **The member's own step accepts what `play` shows of the kind's row**, reading no column, and
the row of the claim that it lays is true of W. Premises as in `k13_step`, at the public data's
`whereOf Z`; and the state in front bears no mark of failure. -/
theorem k13_member_step (O : IM.Open o pol lay KL F Z Bs base c₁ A B) {mem : Block S Cl}
    (hm : mem ∈ c₁.blocksInOrder) (hp : mem.place = ⟨1, none, 3, .K13⟩)
    (weights : W₀ → Weights) (pile : PileOf Xi) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile (whereOf Z)).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds (whereOf Z)) ds = true) {s : S}
    {f : VerifiableInference.Desc.First.FinOwn} {t : List Nat × St} {msg : Array OracleNotice}
    (h0 : s.failed = none) (hs : s.here = .fin f)
    (hreply : (!(whereOf Z).reply || s.out.reply.isSome) = true)
    (hcount : s.out.pending.length = (whereOf Z).rows)
    (hfit : memberRowsFit s.st (whereOf Z).lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits (whereOf Z).lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf (whereOf Z).lin.kCol) = some t)
    (hlin : linOk s.st.codes (whereOf Z).lin = true) (hmsg : linMessageW (whereOf Z).lin = some msg)
    (hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads)
    (W : Wit GE (whereOf Z).lin.matrixRows (whereOf Z).lin.kCol)
    (hmat : W.mat = (k13Wit (whereOf Z).lin.matrixRows (whereOf Z).lin.kCol
      (k13Ask weights pile m.st.input)).mat)
    (hu : ∀ j, j < 2 * (whereOf Z).lin.kCol + 1 → ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE) =
      maskAt W (t.1.map fun i => ⟨s.out.indexMasks, i⟩) j)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg W r) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile (whereOf Z)).steps mem v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      fillCols (readsOf chain ft stored tree mem.rounds ds) [] = .ok [] ∧
      mem.step ft s (roundsOf l) [] = .ok (withClaim s t.2.st msg row, 0) ∧ Holds ρg W row := by
  obtain ⟨hr, ho⟩ := k13_member_fields O hm hp
  exact k13_step (Cl' := Unit) weights pile (whereOf Z) mem hr ho v c m ds hd
    (fun rs gs t' h => k13_at_m3 o pol lay KL F Z Bs base c₁ A B O mem hm hp s t' rs gs h0 h)
    hs hreply hcount hfit hw hform ht hlin hmsg hpile W hmat hu hrows chain ft stored tree

/-- **The same AT EVERY COIN**: the row of the claim laid is true of Wb with the coins spent laid
under the slots that the verifier takes. Premises as in `k13_step_all`. -/
theorem k13_member_step_all (O : IM.Open o pol lay KL F Z Bs base c₁ A B) {mem : Block S Cl}
    (hm : mem ∈ c₁.blocksInOrder) (hp : mem.place = ⟨1, none, 3, .K13⟩)
    (weights : W₀ → Weights) (pile : PileOf Xi) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile (whereOf Z)).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds (whereOf Z)) ds = true) {s : S}
    {f : VerifiableInference.Desc.First.FinOwn} {t : List Nat × St} {msg : Array OracleNotice}
    (h0 : s.failed = none) (hs : s.here = .fin f)
    (hreply : (!(whereOf Z).reply || s.out.reply.isSome) = true)
    (hcount : s.out.pending.length = (whereOf Z).rows)
    (hfit : memberRowsFit s.st (whereOf Z).lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits (whereOf Z).lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf (whereOf Z).lin.kCol) = some t)
    (hlin : linOk s.st.codes (whereOf Z).lin = true) (hmsg : linMessageW (whereOf Z).lin = some msg)
    (hbelow : pileBelowC (dOf s).st s.out.indexMasks s.out.pending = true)
    (hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads)
    (Wb : Wit GE (whereOf Z).lin.matrixRows (whereOf Z).lin.kCol)
    (hmat : Wb.mat = (k13Wit (whereOf Z).lin.matrixRows (whereOf Z).lin.kCol
      (k13Ask weights pile m.st.input)).mat)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg Wb r) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile (whereOf Z)).steps mem v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      fillCols (readsOf chain ft stored tree mem.rounds ds) [] = .ok [] ∧
      mem.step ft s (roundsOf l) [] = .ok (withClaim s t.2.st msg row, 0) ∧
      Holds ρg (withTaken Wb (t.1.map fun i => ⟨s.out.indexMasks, i⟩)
        fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE)) row := by
  obtain ⟨hr, ho⟩ := k13_member_fields O hm hp
  exact k13_step_all (Cl' := Unit) weights pile (whereOf Z) mem hr ho v c m ds hd
    (fun rs gs t' h => k13_at_m3 o pol lay KL F Z Bs base c₁ A B O mem hm hp s t' rs gs h0 h)
    hs hreply hcount hfit hw hform ht hlin hmsg hbelow hpile Wb hmat hrows chain ft stored tree

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_member_fields
#print axioms ProofFile.Honest.K13.k13_member_step
#print axioms ProofFile.Honest.K13.k13_member_step_all
