-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionAtAFilling.lean: the law of the rows of the attention
segments' own rounds (kind K5: the label of that sub-protocol in the description) at a return of the
maker at any filling whose sides of the kind are their lot's halves. The index and the pads' types
are free variables, so this serves at every filling of that form, with no reading through in its text.

  LaysTheLotAlone     of a filling: its sides of the kind are the lot's halves, in order
  AttentionLawAt      what is stated of the rows at a return of the maker
  attention_law_at    CONDITIONAL: h; hA; hP: the statement

Of Good this speaks at every first condition that holds nowhere, so plays and acc are met for nothing.
fresh says nothing at this kind: its parts have no coin, and no entry of the book has its owner at a
row's place (Honest/K5/Law/AttentionBookAtAFilling.lean). exact is the spender's half: that the blocks
it takes as uniform are so in a run is the owner's condition, OwnerFresh in
E2E/AttentionSimulatorAtTheTerm.lean, and it is not here. This is not the structure Owed at these rows:
nothing here is on runs or on the state before a part. That exact's premises can meet, and that a part
shows something where they do, stand in other files. h, the library's head, is a hypothesis, and so is
that the maker returns.
No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionFacts
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnsNothingAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotK3
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotAll
import Johnson.Desc.ProofFile.Honest.K5.Law.KindFivePlaces
import Johnson.Desc.ProofFile.Honest.K5.Law.LotNotEmptyAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.CoinsAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionTells
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionRowSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place KindName)
open P5J (AtMgA TS)

variable {W₀ Rc X₀ X : Type}

/-- The rows at a return of the maker. -/
abbrev rowsOfReturn (A : OnlineProverWithDescription W₀ Rc Cells X₀ X) :
    List (Unlettered (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst) :=
  (k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3).rows A.Z A.G

/-- **A filling's sides of the kind are the lot's halves, in order.** -/
def LaysTheLotAlone (P : OnlineProverParts W₀ Rc Cells X₀ X) : Prop :=
  ∀ Z G, ((P.lots.flatMap fun L => L.halves Z G).filter
      fun h => decide (h.place.kind = KindName.K5)) =
    (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3).halves Z G

/-- **The law of the rows at a return of the maker.** -/
structure AttentionLawAt (A : OnlineProverWithDescription W₀ Rc Cells X₀ X) : Prop where
  /-- in the prover's list, the sides of this kind are the rows' halves, in order and in number -/
  count : (A.H.first.filter fun h => decide (h.place.kind = KindName.K5)) =
    (rowsOfReturn A).map (·.half)
  /-- one row at each of the twelve attention segments -/
  twelve : (rowsOfReturn A).length = 12
  /-- twelve places, of this kind, each with a part -/
  places : ((rowsOfReturn A).map (·.place)).Nodup ∧
    ∀ r ∈ rowsOfReturn A, r.place.kind = KindName.K5 ∧ r.row ≠ []
  /-- the blocks of this kind in the description are at the rows' places, in the first chain alone -/
  kindPlaces : (∀ b ∈ A.F.first.blocksInOrder, b.place.kind = KindName.K5 →
      ∃ r ∈ rowsOfReturn A, r.place = b.place) ∧
    (∀ b ∈ A.F.shared.blocksInOrder, b.place.kind ≠ KindName.K5) ∧
    (∀ b ∈ A.F.second.blocksInOrder, b.place.kind ≠ KindName.K5) ∧
    (∀ h ∈ A.H.shared, h.place.kind ≠ KindName.K5) ∧ ∀ h ∈ A.H.second, h.place.kind ≠ KindName.K5
  /-- On holds at all arguments -/
  on : ∀ r ∈ rowsOfReturn A, ∀ u ca m front, r.On u ca m front
  /-- at each row: a side; Good at it, at every list of declared rounds and all falls; and what its
  members read and tell -/
  rows : ∀ r ∈ rowsOfReturn A,
    (∃ σ, Side.seated A.F.first.blocksInOrder r.place r.row [] = some σ) ∧
    ∀ (falls : List (Fall A.F.S₁)) σ, Side.seated A.F.first.blocksInOrder r.place r.row falls = some σ →
      (∀ pre (P Q : Coins A.B → A.F.S₁ → Mid (Local W₀ Rc ProofFile.Inst Cells) X → Env → Prop),
        (∀ k s m E, ¬ P k s m E) → Good pre .own σ A.B (orderOf A.F) 0 0 P Q r.On r.bud) ∧
      (∀ pre, ExactAtOneTable σ r.On r.bud pre) ∧
      ∀ u ∈ σ.members,
        u.part.takes = ⟨0, 0⟩ ∧ u.part.carries = [] ∧ HasNoStop u.part ∧
        ReadsTheTraceAlone u.part ∧ u.part.readsNoneSeen ∧ ReadsItsCoinsAlone u.sim ∧
        TellsItsCoins u.sim (u.rounds.map fun x => (x.1.items.filter (· != .root)).length) ∧
        ∀ (tree : Nat → List Nat) (n : Nat) (ds : List Fmt.Drawn),
          r.bud u.number ds (asksFrom tree (u.rounds.map (·.2.length)) n)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A side that passes the maker's test on strays stands at a block of its chain. -/
theorem side_at_block {S Cl V W Y : Type} {bs : List (Block S Cl)} {hs : List (Placed V W Y)}
    (h : (strays bs hs).isEmpty = true) : ∀ q ∈ hs, ∃ b ∈ bs, b.place = q.place := by
  intro q hq
  by_contra hn
  have hm : q.place ∈ strays bs hs := by
    unfold strays
    refine List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, ?_⟩, rfl⟩
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    exact fun b hb e => hn ⟨b, hb, e⟩
  rw [List.isEmpty_iff] at h
  rw [h] at hm
  cases hm

/-- **The law at a return.** CONDITIONAL: h: the library's head at the return's public part; hA: the
maker returns; hP: the filling lays the lot alone. -/
theorem attention_law_at {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hP : LaysTheLotAlone P) :
    AttentionLawAt A := by
  obtain ⟨-, hG, e3, -, -, -, -, eH, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction A.Z Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  obtain ⟨-, -, t2, t3, -⟩ := atPure_tests hA
  have hcount : (A.H.first.filter fun h => decide (h.place.kind = KindName.K5)) =
      (rowsOfReturn A).map (·.half) := by
    rw [eH]
    refine (hP A.Z A.G).trans ?_
    rw [← k5SLot_toHLot]
    rfl
  obtain ⟨n1, n2, n3⟩ := k5_lot_not_empty_at_return h hA (W₀' := W₀) (Rc' := Rc) (Xi := ProofFile.Inst)
    (X' := X) (Pb := ProofFile.Inst) id [] (rowsOfReturn A) rfl
  have hK := keysFitAll_K3 h hG
  have hPl := k5_rows_places (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) h hG id
    hK
  have hRow : ∀ r ∈ rowsOfReturn A, r.place.kind = KindName.K5 := by
    intro r hr
    obtain ⟨_, _, e⟩ := k5_row_place h hG hr
    rw [e]
  refine ⟨hcount, n1, ⟨n2, fun r hr => ⟨hRow r hr, (n3 r hr).1⟩⟩, ?_, ?_, ?_⟩
  · rw [eF] at t2 t3 ⊢
    refine ⟨?_, kindFive_not_in_shared h, kindFive_not_in_second h, ?_, ?_⟩
    · intro b hb hk
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hb
      obtain ⟨g, hg, rfl⟩ := kindFive_only_at_borders h hj hk
      obtain ⟨blk, a, hm, -, Dc⟩ := k5_member h hg
      obtain rfl : blk = b := Option.some.inj (hm.symm.trans hj)
      have hmem : (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) ∈ (rowsOfReturn A).map (·.place) := by
        rw [hPl]
        exact List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩
      obtain ⟨r, hr, er⟩ := List.mem_map.1 hmem
      exact ⟨r, hr, by rw [er, Dc.place]; rfl⟩
    · intro q hq hk
      obtain ⟨b, hb, e⟩ := side_at_block t2 q hq
      exact kindFive_not_in_shared h b hb (e ▸ hk)
    · intro q hq hk
      obtain ⟨b, hb, e⟩ := side_at_block t3 q hq
      exact kindFive_not_in_second h b hb (e ▸ hk)
  · intro r hr u ca m front
    obtain ⟨_, _, Y, _, rfl⟩ := row_of_lot hr
    trivial
  · intro r hr
    obtain ⟨Z', G', F', B', H', rd', rw'⟩ := A
    dsimp only at eF hr hG h hA ⊢
    subst eF
    refine ⟨rows_seated h hG id keyOfK3 [] r hr, fun falls σ hσ => ?_⟩
    have good := fun pre => k5_good_rows_at_maker h hA hG id keyOfK3 pre
      (.own : Face (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) ProofFile.Inst)
      (orderOf (P5J.F0T OnBytes.secondHashFunction Z' Np cF)) 0 0 falls r hr σ hσ
    refine ⟨fun pre P' Q' hN => good_of_never (good pre) hN,
      fun pre => exactAtOneTable_of_good (good pre), fun u hu => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := k5_rows_read hr hσ u hu
    obtain ⟨ns, -, -, tells, -⟩ := attention_tells_at_row h hG hr hσ u hu
    obtain ⟨Y, p, er, hrow, hB, -⟩ := seat_of_row h hG hr hσ
    refine ⟨a1, a2, a3, a4, k5_rows_noneSeen hr hσ u hu, a5, tells, fun tree n ds => ?_⟩
    rw [er]
    exact bud_at hB hrow hu tree n ds

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.LaysTheLotAlone
#print axioms ProofFile.Honest.K5.AttentionLawAt
#print axioms ProofFile.Honest.K5.side_at_block
#print axioms ProofFile.Honest.K5.attention_law_at
