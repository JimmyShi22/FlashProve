-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OwnsNothingAtMaker.lean: at the book that the maker returns, no
entry names a part of the attention segments' own rounds (kind K5: the label of that sub-protocol in
the description) as owner; and so Good stands at every row of the kind with no premise on the book.

  k5_owner_elsewhere  CONDITIONAL: h; hA: at each of the twelve groups no entry of the book that the
                      maker returns has its owner at the group's place of the kind
  k5_good_rows_at_maker   CONDITIONAL: h; hA; hG: Good at every row of the lot, at that book
  k5_good_rows_at_return  CONDITIONAL: h; hA: the same at what the maker returns, without hG

What Good says here is what k5_good_rows says, and no more. It stands at A := B := the empty sentence
(False), so plays and acc are met for nothing: nothing is said on the playing or on the verifier's
yes. fresh says nothing at this kind: its parts have no coin of their own (k5_parts_plain,
Honest/K5/Law/LendsOfBook.lean) and, by k5_owner_elsewhere, no entry names one as owner. exact is the
spender's half alone, one part at a time, all else fixed before the coins: it takes the blocks that
the part spends as uniform and independent. That they are so in a run is not stated here: it needs
fresh at the part that owns them and exact at every part that carries them behind this one, and
neither is shown in this file. exact holds at every job, right or wrong, so it does not say that the
job is the protocol's.

THE LOT MAY HAVE FEWER THAN TWELVE ROWS, OR NONE: cells and keyOf are free variables; at a keyOf of
wrong lengths every row falls away and k5_good_rows_at_maker holds of the empty list. Twelve rows are
had under KeysFitAll (rows_twelve, Honest/K5/Law/SLotTwelve.lean), which this file does not import;
at keyOfK3 they are there under h and hA (k5_lot_not_empty_at_return,
Honest/K5/Law/LotNotEmptyAtMaker.lean, which imports this file).
Of what the maker returns the theorem reads the book alone: that the rows' halves are sides of any
prover is not shown here.

The premises. h, the library's head, is a hypothesis: that it can be met is not shown here. hA: the
maker returns at the filling P. P is a free variable, and that the maker returns at any filling is
not shown here. Where h or hA fails, the three theorems say nothing. hG follows from h and hA at
G := A.G (k5_good_rows_at_return). No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookPlainOwner
import Johnson.Desc.ProofFile.Honest.K5.Law.BookFits5
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT EACH OF THE TWELVE GROUPS NO ENTRY OF THE BOOK THAT THE MAKER RETURNS HAS ITS OWNER AT THE
GROUP's PLACE OF THE KIND.** CONDITIONAL: h: the library's head; hA: the maker returns A at a filling
P, P a free variable. -/
theorem k5_owner_elsewhere (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {g : Nat} (hg : g < 12)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.owner.place ≠ ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  obtain ⟨m, -⟩ := parts_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := m.book
  rw [eF] at hB
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨blk, a', hm, -, Dc⟩ := k5_member h hg
  have hb : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  intro e he
  have key := plain_no_owner hB hp hb (k5_no_seed blk (parAt Zp g a') Dc.rounds) e he
  rw [Dc.place] at key
  exact key

variable {W₀ Rc Tr X₀ X W₀' Rc' Tr' X' Xi Pb : Type}

/-- **GOOD AT EVERY ROW OF THE LOT, AT THE BOOK THAT THE MAKER RETURNS, WITH NO PREMISE ON THAT BOOK;
AT A := B := THE EMPTY SENTENCE (False); fresh IS EMPTY.** exact IS THE SPENDER's HALF ALONE. THE LOT MAY
HAVE FEWER THAN TWELVE ROWS, OR NONE: WHERE seatAtK YIELDS NOTHING THERE IS NO ROW AND NOTHING IS SAID.
CONDITIONAL: h; hA; hG: G is the ground made of the head's public part. -/
theorem k5_good_rows_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E))
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') Pb) (ord : List Place)
    (chain firstTree : Nat) (fs₀ : List (Fall TS)) :
    ∀ r ∈ (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows Zp G,
      ∀ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ →
        Good pre φ σ₀ A.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
          r.On r.bud := by
  intro r hr σ₀ hσ
  obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hl, a, hA', hP⟩ := seat_facts hY
  have ha : (P5J.At.X Zp).A[g]? = some a := by
    rw [← hA', H2K5.Row.ground_W hG]
    rfl
  have hgl := List.mem_range.1 hg
  refine k5_good_seated_head h hgl ha hl hP pre φ A.B ord chain firstTree fs₀ hσ ?_
  intro e he
  have key := k5_owner_elsewhere h hgl hA e he
  show e.owner.place ≠ Y.place
  rw [show Y.place = (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) by
    show (⟨1, some Y.link, 3, .K5⟩ : Place) = _
    rw [hl]]
  exact key

/-- **The same at the public part and the ground that the maker returns**: hG is no longer a premise.
exact IS THE SPENDER's HALF ALONE; fresh IS EMPTY; THE LOT MAY HAVE FEWER THAN TWELVE ROWS, OR NONE.
CONDITIONAL: h; hA. -/
theorem k5_good_rows_at_return (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E))
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') Pb) (ord : List Place)
    (chain firstTree : Nat) (fs₀ : List (Fall TS)) :
    ∀ r ∈ (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows A.Z A.G,
      ∀ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ →
        Good pre φ σ₀ A.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
          r.On r.bud := by
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  rw [eZ]
  exact k5_good_rows_at_maker h hA hG cells keyOf pre φ ord chain firstTree fs₀

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owner_elsewhere
#print axioms ProofFile.Honest.K5.k5_good_rows_at_maker
#print axioms ProofFile.Honest.K5.k5_good_rows_at_return
