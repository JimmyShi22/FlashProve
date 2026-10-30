-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsAtWider.lean: WHEN THE MAKER OF THE ONE HONEST PROVER
RETURNS AT THE FILLINGS `widerFillOwn` AND `widerFillAt` (Honest/AtPureWiderAt.lean): just where
what it makes of the public files is there (`MakerHas`, Law/ReturnsOf.lean) and eleven named debts
are paid, among which the lot of the kind K5 does not stand. One definition, a premise's form, and
an abbreviation; five theorems. IT JOINS: it shows of no debt that it is paid anywhere. No property
is claimed.

Main names:
  `WiderDebts` a premise's form: of nine lots, five of them letters (the structure `LongLots`), each
    AT ONE READER OF THE INDEX (`I.weights Z`: the wrappers `HLot.byPub` and `HLot.byRows`
    unfolded), no half is astray in the first chain; of the shared chain's halves none is astray;
    the named member of the range is in range
  `widerOwn_fits`, `widerOwn_debts` where `MakerHas` holds and the debts are paid the filling meets
    the maker's four asks; where it meets them the debts are paid. The line of the kind K5 by
    `k5LotK_no_strays_desc` (Law/LotClean.lean), at every reader of the key points; the second chain
    has no half, by the filling's text
  `widerOwn_returns`   where `MakerHas` holds and the debts are paid the maker returns
  `widerOwn_returns_iff` **it returns just there.** The open functions O and the sides' first own
    state stand on the left alone: at `widerFillOwn` whether the maker returns hangs on neither
  `widerAt_returns_iff` **the same at `widerFillAt`**, at the five long lots `LongLots.plain o' S
    O`, which read two of O's functions

The function that stands for the earlier hash in the filling (o') is a letter of its own beside the
maker's (o); `widerFillOwn` does not read it, and it is not among the letters of `WiderDebts`.

Limits. OF THE FOUR THINGS MADE (`MakerHas`) NONE IS SHOWN AT ANY FILES HERE, and of no debt that it
is paid anywhere. A RETURN OF THE MAKER IS NO WHOLE HONEST PROVER: the maker tests that no half is
astray, not that no half lacks; these fillings have no lot of the kinds K9, K10 and K12. The
statements say "= []"; the maker's text says "the list is empty" (`isEmpty`). The list of debts is
the filling's written list of ten lots as it stands: an entry that turns there turns its field here,
and the proofs break aloud. Where the shared chain's maker rejects, the filling lays no half there,
and the debt on that chain is met for nothing. The other limits of Law/ReturnsOf.lean hold here too.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (FileDescription)

variable {W₀ X : Type} {o o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}

/-- The type of a lot of these fillings. -/
abbrev WLot (W₀ X : Type) : Type :=
  HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X

/-- **WHAT IS OWED OF THE FILLING FOR A RETURN AT `widerFillOwn`, BY NAME**: nine lots, each at one
reader of the index (`I.weights Z`), the shared chain, the range. A definition: a premise's form.
The lot of the kind K5 is not in it. -/
structure WiderDebts (L : LongLots W₀ X) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub)
    (G : Ground) (F : FileDescription Inst) : Prop where
  k1 : strays F.first.blocksInOrder ((L.k1 (I.weights Z)).halves Z G) = []
  k2 : strays F.first.blocksInOrder ((K2.switchLot (widerRows S Z G)
             fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩ :
               WLot W₀ X).halves Z G) = []
  k7 : strays F.first.blocksInOrder ((replyLot : WLot W₀ X).halves Z G) = []
  k11 : strays F.first.blocksInOrder ((L.k11 (I.weights Z)).halves Z G) = []
  k13 : strays F.first.blocksInOrder ((L.k13 (I.weights Z)).halves Z G) = []
  k3 : strays F.first.blocksInOrder ((L.k3 (I.weights Z)).halves Z G) = []
  k4 : strays F.first.blocksInOrder ((K4.k4HLot id (I.weights Z) fun _ _ => K4.k4LookAt :
             WLot W₀ X).halves Z G) = []
  k6 : strays F.first.blocksInOrder ((L.k6 (I.weights Z)).halves Z G) = []
  k8 : strays F.first.blocksInOrder ((K8.smallLot id fun _ G _ l => K3.matsOwn G.W l :
             WLot W₀ X).halves Z G) = []
  k14 : strays F.shared.blocksInOrder ((nowSharedBy (I.weights Z) Z).toOption.getD []) = []
  range : I.inRange I.dummy = true

variable {own₀ : X} {L : LongLots W₀ X} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz}
  {O : OnlineProverArguments} {Z : Pub} {G : Ground} {F : FileDescription Inst} {B : ProverCoinCounts}

/-- **Where the debts are paid the filling fits.** K5's line by `k5LotK_no_strays_desc`, at every
reader of the key points; the second chain has no half. -/
theorem widerOwn_fits (m : MakerHas o pol lay KL Z G F B) (d : WiderDebts L I S Z G F) :
    MakerAsks (widerFillOwn own₀ L I o' S O) Z G F := by
  refine ⟨strays_firstOf _ Z G _ fun M hM => ?_, d.k14, rfl, d.range⟩
  simp only [widerFillOwn, List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact d.k1
  · exact d.k2
  · exact d.k7
  · exact d.k11
  · exact d.k13
  · exact d.k3
  · exact d.k4
  · exact k5LotK_no_strays_desc id O.keyOf m.pub m.ground m.desc
  · exact d.k6
  · exact d.k8

/-- **Where the filling fits the debts are paid.** -/
theorem widerOwn_debts (f : MakerAsks (widerFillOwn own₀ L I o' S O) Z G F) :
    WiderDebts L I S Z G F := by
  have e := (strays_firstOf_iff F.first.blocksInOrder Z G _).1 f.first
  have at' : ∀ (n : Nat) (M : WLot W₀ X), (widerFillOwn own₀ L I o' S O).lots[n]? = some M →
      strays F.first.blocksInOrder (M.halves Z G) = [] := fun n M h => e M (List.mem_of_getElem? h)
  have h0 := at' 0 _ rfl
  have h1 := at' 1 _ rfl
  have h2 := at' 2 _ rfl
  have h3 := at' 3 _ rfl
  have h4 := at' 4 _ rfl
  have h5 := at' 5 _ rfl
  have h6 := at' 6 _ rfl
  have h8 := at' 8 _ rfl
  have h9 := at' 9 _ rfl
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h8, h9, f.shared, f.range⟩

/-- **WHERE THE DEBTS ARE PAID THE MAKER RETURNS AT `widerFillOwn`.** -/
theorem widerOwn_returns (m : MakerHas o pol lay KL Z G F B) (d : WiderDebts L I S Z G F) :
    ∃ A, onlineProverFromPublicFiles o pol lay KL (widerFillOwn own₀ L I o' S O) = .ok A ∧ A.Z = Z ∧ A.G = G ∧
      A.F = F ∧ A.B = B :=
  atPure_of_parts m (widerOwn_fits m d)

/-- **THE MAKER RETURNS AT `widerFillOwn` JUST WHERE THE DEBTS ARE PAID.** The open functions O and
the sides' first own state stand on the left alone. -/
theorem widerOwn_returns_iff :
    (∃ A, onlineProverFromPublicFiles o pol lay KL (widerFillOwn own₀ L I o' S O) = .ok A) ↔
      ∃ Z G F B, MakerHas o pol lay KL Z G F B ∧ WiderDebts L I S Z G F :=
  ⟨fun h => by
      obtain ⟨Z, G, F, B, m, f⟩ := atPure_returns_iff.1 h
      exact ⟨Z, G, F, B, m, widerOwn_debts f⟩,
    fun ⟨_, _, _, _, m, d⟩ => (widerOwn_returns m d).imp fun _ h => h.1⟩

/-- **The same at `widerFillAt`.** -/
theorem widerAt_returns_iff :
    (∃ A, onlineProverFromPublicFiles o pol lay KL (widerFillAt I o' S O) = .ok A) ↔
      ∃ Z G F B, MakerHas o pol lay KL Z G F B ∧
        WiderDebts (LongLots.plain (X := Unit) o' S O) I S Z G F :=
  widerOwn_returns_iff

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.widerOwn_fits
#print axioms ProofFile.Honest.K5.widerOwn_debts
#print axioms ProofFile.Honest.K5.widerOwn_returns
#print axioms ProofFile.Honest.K5.widerOwn_returns_iff
#print axioms ProofFile.Honest.K5.widerAt_returns_iff
