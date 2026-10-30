--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/OwedBeside.lean: WHAT IS OWED BESIDE THE SHARE OF THE KIND K6 ("the
output head's own rounds") BEFORE ITS SIMULATORS SAY ANYTHING OF A RUN, AS NAMED PROPOSITIONS. NEITHER IS
PROVED HERE. K6's parts own no coin: what they send is masked by 173 coins of another part, the owner
(`headOwner`, Honest/K6/Term/BookAtTheHead.lean). The field `exact` TAKES these coins as uniform and
independent of the state.

  `OwnerFreshK6`   OWED WITH THE OWNER's KIND: at every list of the first chain, at every member of its side
        of which a part of K6's spends a coin: the equation of `Good.fresh` for that part, at the list's
        own bud. In the form of `OwnerFreshAt` (Honest/KindSheet.lean), as other kinds state theirs. It is a
        family over the letter G, the lists of all kinds' rows: it is owed at the G of the rule that ends
        in `Owed`. IT SAYS NOTHING AT A G WHOSE FIRST CHAIN HAS NO LIST AT THE OWNER's PLACE. It lies inside
        `Owed.good` and is nothing beyond it
  `ownerFreshK6_at_the_owner`   at a return of the maker: which equations these are: at the list at the
        owner's place, at its member number 0, for each of K6's six parts that spend (numbers 1, 2, 4, 5,
        6, 7); and to K6's eight parts no other part owes anything (`owner_of_the_heads_coins`)
  `ownerFreshK6_of_good`   it is a call of the field: where every list of the first chain meets `Good`,
        it holds
  `MaskTieK6`   the j-th mask entry that the relation's witness holds under K6's slots is the j-th coin that
        the book lends K6's row. It is the library's `MaskTieBookOn` (Honest/Law/Rule/TiesOn.lean) at K6's
        place and eight parts. It is owed for `Owed.runs`. IT SAYS NOTHING OF WHAT K6 SHOWS OR OF WHAT LATER
        PARTS CARRY. A family over letters (the thread, the states, four readers): with no state it
        holds emptily; it is owed at the first chain's thread
  `maskTieK6_of`   the library's rule for it (`maskTieBookOn_of`) at K6's numbers. Of its five premises
        the book's, `RowIsStretch`, IS PAID (`headPads_are_the_owners_coins`,
        Honest/K6/Term/BookAtTheHead.lean). FOUR ARE LEFT: the range in which the next two speak holds
        K6's 173 slots; the owner lays the mask row's entries among
        its coins from number 439 on (`SenderLays`: the owner's kind's); the reader of the witness reads
        that row (`ReaderReads`); K6's first slot in the verifier's ledger is 1995 (`LedgerIs`)

THE TIE TO THE CARRIERS IS NOT TYPED HERE, NOT EVEN AS A PROPOSITION. (i) How what K6's row shows hangs on its
173 lent coins, at each fixed state and challenges: 16 lone scalars and 3 claimed sums are a value plus a
coin; 10 end values are a value plus the challenge of "PSC Y" times a coin; the other 144 go by the
masked sumcheck's hiding polynomial, whose coefficients the coins are (Honest/Sum.lean, § 2): such a
scalar holds other coins too. It is had part by part in the small laws (`shows_scalars`,
Honest/Small/Scalars.lean; `sumOut_vals`, Honest/SumLaw/SumShown.lean) and gathered at K6's row nowhere.
(ii) That the runs which the segment's closing and the next code switch CARRY hold these same coins
of the owner: a statement on the book's carrying entries. (iii) The carriers' own `exact`, at each
fixed carried run: their kinds' share.

WHAT IT IS NOT. Two definitions and three lemmas that call other files' rules. Whether either proposition
holds at the values at which it is owed is not known here. Nothing
on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.KindSheet
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall
import Johnson.Desc.ProofFile.Honest.K6.Term.BookAtTheHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes (E)
open VerifiableInference.Desc (FileDescription Place)

/-! ## 1 The owner's debt -/

/-- **OWED BESIDE: the owner's debt.** At each list of the first chain, at each member of its side with
a coin that a part of K6's spends: the equation of `Good.fresh` for that part's address. A definition,
meant as a hypothesis. -/
def OwnerFreshK6 {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Prop :=
  ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ → ∀ u ∈ σ.members, ∀ i : Nat,
    Bk.spentBy ⟨σ.block.place, u.number⟩ ⟨IM.k6Place, i⟩ ≠ [] →
    OwnerFreshAt Face.own σ Bk (orderOf F) L.bud u ⟨IM.k6Place, i⟩

/-- **It is a call of the field.** Where every list of the first chain meets `Good`, at whatever `pre`,
A and B, the owner's debt to K6 is paid. -/
theorem ownerFreshK6_of_good {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (good : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ pre A B, Good pre Face.own σ Bk (orderOf F) 0 0 A B L.On L.bud) : OwnerFreshK6 G := by
  intro L hL σ hσ u hu i _
  obtain ⟨pre, A, B, g⟩ := good L hL σ hσ
  exact ownerFresh_of_good g hu _

/-- **Which equations these are, at a return of the maker.** book: what the returned book says of K6's row.
Where the first chain's lists hold a list L whose side σ stands at the owner's place, with a member u
of number 0: the equation of `Good.fresh` at u for each of K6's six parts that spend. Without such a
list `OwnerFreshK6` says nothing. -/
theorem ownerFreshK6_at_the_owner {W₀ Rc Tr X₀ X Ky : Type} {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    {reader : Local W₀ Rc Inst Tr → HeadAsk}
    {numbers : VerifiableInference.Desc.Kinds.Head.Par}
    (book : BookAtTheHead returned reader numbers)
    {W₁ Rc₁ Tr₁ X₁ X₂ : Type} (G : Sides returned.F returned.B W₁ Rc₁ Ky Tr₁ X₁ X₂)
    (owed : OwnerFreshK6 G) :
    ∀ L ∈ G.first, ∀ σ, L.side returned.F.first.blocksInOrder G.falls₁ = some σ →
      σ.block.place = headOwner.place → ∀ u ∈ σ.members, u.number = 0 →
      ∀ i ∈ [1, 2, 4, 5, 6, 7],
        OwnerFreshAt Face.own σ returned.B (orderOf returned.F) L.bud u ⟨IM.k6Place, i⟩ := by
  intro L hL σ hσ hp u hu h0 i hi
  refine owed L hL σ hσ u hu i ?_
  rw [hp, h0]
  exact the_six_spend_of_the_owner book i hi

/-! ## 2 The mask row's entries are the lent coins -/

section
variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **OWED BESIDE: the tie.** The mask entry that the relation's witness holds under K6's j-th slot is
the j-th coin that the book lends K6's row. T: the first chain's thread. At: at which states. opn,
maskOf, val, slot: the readers of the verifier's state and of the witness. A definition, meant as a
hypothesis. -/
def MaskTieK6 (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop)
    {A G : Type} (opn : S → Option A) (maskOf : A → S → W → T.Wt → Nat → G) (val : E → G)
    (slot : A → Nat) : Prop :=
  MaskTieBookOn T At IM.k6Place 8 opn (fun a s w v j => maskOf a s w v (slot a + j)) val
    (fun len j => j < len)

/-- **The library's rule for it, at K6's numbers.** stretch: the book's premise, which is paid at
every return of the maker. The four others are left. -/
theorem maskTieK6_of {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {A G : Type} {opn : S → Option A}
    {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G}
    {row : Coins Bk → W → List Fmt.Drawn → Nat → E} {N : Nat → Prop} {slot : A → Nat}
    (senderLays : SenderLays Bk T.chain headOwner 439 row N)
    (readerReads : ReaderReads T At opn maskOf val row N)
    (ledgerIs : LedgerIs At opn slot 1995)
    (stretch : RowIsStretch Bk T.chain IM.k6Place 8 headOwner (439 + 1995) 173)
    (inRange : ∀ j, j < 173 → N (1995 + j)) : MaskTieK6 T At opn maskOf val slot :=
  maskTieBookOn_of senderLays readerReads ledgerIs stretch inRange

end

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.OwnerFreshK6
#print axioms ProofFile.Honest.K6.ownerFreshK6_of_good
#print axioms ProofFile.Honest.K6.ownerFreshK6_at_the_owner
#print axioms ProofFile.Honest.K6.MaskTieK6
#print axioms ProofFile.Honest.K6.maskTieK6_of
