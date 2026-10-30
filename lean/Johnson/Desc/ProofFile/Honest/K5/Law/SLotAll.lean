-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SLotAll.lean: UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): WHAT THE FILES OF THIS FOLDER SAY OF THE LOT k5SLot
(Honest/K5/Law/SLot5.lean) OF THE ATTENTION SEGMENTS' OWN ROUNDS (kind K5: the label of that
sub-protocol in the description), IN ONE STATEMENT. A join: no new thought. Statements with their
proofs.

  rows_seated    CONDITIONAL: under the head, at the ground that the maker makes: at every row of
                 the lot, whatever keyOf, Side.seated makes a side (seated_head,
                 Honest/K5/Law/GoodHead.lean, at the row's seat)
  k5_lot_head    **CONDITIONAL: under the head and hk: a ground is there (ground_head) · at it the
                 lot at keyOfK3 has twelve rows (rows_twelve_K3) · at every row a side is there
                 (rows_seated) · Good at it, "AT A := B := THE EMPTY SENTENCE (False)", "BY WEIGHT
                 IT SAYS fits, exact (THE SPENDER's HALF) AND AN EMPTY fresh, AND NOTHING ON plays
                 OR acc" (k5_good_rows, Honest/K5/Law/SLotRows.lean) · no move of a member reads
                 anything of what has been seen (k5_rows_noneSeen)**

THE PREMISES THAT STAY, BY NAME. h: the head: A HYPOTHESIS of every statement that names it. (The
library has P5J.head_exists_at_name, Johnson/P5J/HeadExistsAtName.lean: a head is there under four
premises on the public files; no file of this folder calls it.) · hk: no entry of the book names a
part of a place of the kind K5 as owner. In this form hk is shown by no file. At the book that the
maker returns the form by places is (k5_owner_elsewhere), and k5_good_rows_at_return
(Honest/K5/Law/OwnsNothingAtMaker.lean) needs no hk.

Limits. A CONJUNCTION LAYS ITS PARTS BESIDE EACH OTHER AND SPENDS NONE. What each part says, and
what not, is said in the head of its own file, and binds here: Honest/K5/Law/GoodPaid.lean,
GoodHead.lean and SLotRows.lean for Good; Honest/K5/Law/NoneSeen5.lean for what a move reads;
Honest/K5/Law/SLotK3.lean for the rows' number. The twelve sides are taken one at a time: nothing is
said of two rows together. That the twelve plans bear one shape is not said. The library's full size
alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place)
open P5J (AtMgA TS)

variable {W₀ Rc Xi Tr X Pb : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **At every row of the lot Side.seated makes a side, beside the description's own member.**
CONDITIONAL: the head; G is the ground that the description's maker makes. General in keyOf. WHERE
THE LOT HAS NO ROW NOTHING IS SAID. -/
theorem rows_seated (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (fs₀ : List (Fall TS)) :
    ∀ r ∈ (k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOf).rows Zp G,
      ∃ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ := by
  intro r hr
  obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  exact seated_head h (List.mem_range.1 hg) cells (seat_facts hY).1 fs₀

/-- **FIVE STATEMENTS OF THIS FOLDER IN ONE, UNDER THE HEAD:** the description's maker yields a
ground; at it the lot, with the reader of the key points at keyOfK3, has twelve rows; at every row
Side.seated makes a side beside the description's own member; at that side Good, AT A := B := THE
EMPTY SENTENCE (False); fresh IS EMPTY; and no move of a member reads anything of what has been
seen. OF THE CONJUNCT ON Good ALONE, WHICH IS k5_good_rows', IN THAT THEOREM's OWN DOCSTRING's
WORDS: "BY TYPE IT IS WHAT THE FRAME's RULE TAKES FOR THE FIELD good OF THE STRUCTURE Owed AT THESE
ROWS; BY WEIGHT IT SAYS fits, exact (THE SPENDER's HALF) AND AN EMPTY fresh, AND NOTHING ON plays OR
acc." THE WHOLE IS A JOIN OF FIVE STATEMENTS: NO NEW THOUGHT; A CONJUNCTION SPENDS NOTHING.
CONDITIONAL: the head; hk: no entry of the book names a part of a place of the kind K5 as owner. -/
theorem k5_lot_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (cells : Tr → Cells)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (fs₀ : List (Fall TS))
    (hk : ∀ e ∈ Bk.ahead, e.owner.place.kind ≠ .K5) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧
      ((k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOfK3).rows Zp
        G).length = 12 ∧
      ∀ r ∈ (k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOfK3).rows Zp G,
        ∃ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ ∧
          Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
            r.On r.bud ∧
          ∀ u ∈ σ₀.members, u.part.readsNoneSeen := by
  obtain ⟨G, hG⟩ := ground_head h
  refine ⟨G, hG, rows_twelve_K3 h hG cells, fun r hr => ?_⟩
  obtain ⟨σ₀, hσ⟩ := rows_seated h hG cells keyOfK3 fs₀ r hr
  exact ⟨σ₀, hσ, k5_good_rows h hG cells keyOfK3 pre φ Bk ord chain firstTree fs₀ hk r hr σ₀ hσ,
    k5_rows_noneSeen hr hσ⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rows_seated
#print axioms ProofFile.Honest.K5.k5_lot_head
