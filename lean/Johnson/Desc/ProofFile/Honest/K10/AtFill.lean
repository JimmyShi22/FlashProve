-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/AtFill.lean: the closing of a segment (kind K10) at a return of
`onlineProverFromPublicFiles`, at a filling that lays the closings' lot. What the prover's sides hold at the kind, and what the
kind owes at the description.

  `closing_good_of_plan`   `closing_good_at_book` (Honest/K10/AtBook.lean) at a description that passes its
                   tests on the plan: the premise on the block falls away
  `no_k10_later`   no sub-protocol of the shared or the second chain is of the kind
  `k10_numbers`, `k10_covered`   a sub-protocol of the kind is tied at one of the 25 links
  `ClosingInForm`, `closing_in_form`   all of it, as one statement, at a return of `onlineProverFromPublicFiles`
  `closing_hand_at`   the hypothesis `hand₁` of `file_owed_rows` at a row of the lot
  `closing_on`, `closing_bud`   the row's On and bud ask nothing
  `k10_ten`   none of the ten lots of `widerFillAt` has a half of the kind

`Good` here is stated at A := B := False: of it, `fits` and `exact` as the spender's half say something, and
`fresh` is empty since the part owns no coin. Beside them stands `ShowsSome`. Of `exact`, as Honest/K10/RowsOfClosings.lean says: what the part shows over the coins that it spends is what its
simulator says over coins of its own. That those coins are uniform given what stands in front is
`Good.fresh` of the part that owns them, and nothing here speaks of it. That the description passes its tests
on the plan is a premise.

NO COUNT AT ANY CLOSING RESTS ON THIS FILE ALONE. The rulings (Z2), (Z3) that stand at the head of
Honest/AtPureWiderK10.lean ask that a counted sentence hold, at its stands, that the filler returns, that
`closeAtHand` says yes at every move and that the data are made. Nothing here speaks of these three: where
the filler refuses the part sends the fold's words at empty tables, and every statement here stays true.

The sheet of the kinds. (a) The rows are one term of `Pub → Ground`, at the readers of the
filling; the tie at the base filling is in AtFullSide/Honest/K10AtTerm.lean. (d′) No fall: `fallsHead`
(Law/FallsHead.lean) has no record at a place of the kind, and the part has no stop. (e′) `ClosingOwnersAreFresh`
(K10/OwnersFresh.lean) is owed beside the row, by the owners K1 and K2. The part owns no coin, so no value of it is
carried by another part.

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K10.AtBook
import Johnson.Desc.ProofFile.Honest.K7.AtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

/-- **`closing_good_at_book` at a description that passes its tests on the plan.** -/
theorem closing_good_of_plan {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type}
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hplan : F.planOk = true) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c Z l p Q b ∧
      ∀ fs : List (Fall S),
        ∃ σ : Side S ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
          Side.seated c.blocksInOrder (closePlace Q) (closingPairs (closingJob readers rows stAt Z G Q)) fs =
            some σ ∧
          σ.block = b ∧
          ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place)
            (chain firstTree : Nat),
            Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False)
              (fun _ _ _ _ => False) (closeOn true (closingJob readers rows stAt Z G Q)) closeBud ∧
            ShowsSome pre Face.own σ chain firstTree
              (closeOn true (closingJob readers rows stAt Z G Q)) closeBud := by
  obtain ⟨p, Q, b, hT, hall⟩ := closing_good_at_book (X := X) readers rows stAt G hS hR O hw
    (plan_gives_places hplan) l hl
  have hb : b.planOk = true := by
    have hm : b ∈ c.blocksInOrder := List.mem_of_getElem? hT.2.2.1
    obtain rfl := O.desc
    exact (((FileDescription.planOk_ok _).1 hplan).blocks₁ b hm).1
  exact ⟨p, Q, b, hT, hall hb⟩

/-- **The same at the description's own first chain.** -/
theorem closing_good_of_desc {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type}
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hplan : F.planOk = true) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c Z l p Q b ∧
      ∀ fs : List (Fall F.S₁),
        ∃ σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
          Side.seated F.first.blocksInOrder (closePlace Q)
              (closingPairs (closingJob readers rows stAt Z G Q)) fs = some σ ∧
          ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place)
            (chain firstTree : Nat),
            Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False)
              (fun _ _ _ _ => False) (closeOn true (closingJob readers rows stAt Z G Q)) closeBud ∧
            ShowsSome pre Face.own σ chain firstTree
              (closeOn true (closingJob readers rows stAt Z G Q)) closeBud := by
  obtain ⟨p, Q, b, hT, hall⟩ := closing_good_of_plan (X := X) readers rows stAt G hS hR O hw hplan l hl
  refine ⟨p, Q, b, hT, ?_⟩
  obtain rfl := O.desc
  intro fs
  obtain ⟨σ, hσ, -, hg⟩ := hall fs
  exact ⟨σ, hσ, hg⟩

set_option maxRecDepth 1000000 in
/-- Of the written list of places, those of the kind stand at the closings' numbers. -/
theorem k10_numbers : ((List.range IM.placesW.length).all fun i =>
    (IM.placesW[i]?).all fun p => !(p.kind == .K10) ||
      (List.range 25).any fun l => i == 14 * l + (if l = 24 then 9 else 7) + 5) = true := by
  decide +kernel

/-- **A sub-protocol of the kind is tied at one of the 25 links.** -/
theorem k10_covered {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : b ∈ c.blocksInOrder) (hk : b.place.kind = .K10) :
    ∃ l p Q, l < 25 ∧ Tied c Z l p Q b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
  have hplaces := IM.places_scope hS hR O
  have hp : IM.placesW[i]? = some b.place := by
    rw [← hplaces, List.getElem?_map, hi]
    rfl
  have hlen : i < IM.placesW.length := (List.getElem?_eq_some_iff.1 hp).1
  have h1 := List.all_eq_true.1 k10_numbers i (List.mem_range.2 hlen)
  rw [hp] at h1
  have h2 : ((List.range 25).any fun l => i == 14 * l + (if l = 24 then 9 else 7) + 5) = true := by
    have h1' : (!(b.place.kind == .K10) ||
        (List.range 25).any fun l => i == 14 * l + (if l = 24 then 9 else 7) + 5) = true := h1
    rw [hk] at h1'
    exact h1'
  obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h2
  have hl' : l < 25 := List.mem_range.1 hl
  have e' : i = 14 * l + (if l = 24 then 9 else 7) + 5 := beq_iff_eq.1 e
  obtain ⟨p, Q, b', hT⟩ := tied_at_scope hS hR O l hl'
  have hb' := hT.2.2.1
  rw [← e', hi] at hb'
  obtain rfl := Option.some.inj hb'
  exact ⟨l, p, Q, hl', hT⟩

/-- **No sub-protocol of the shared or of the second chain is of the kind K10**, at a description that
passes its tests on the plan. -/
theorem no_k10_later {o : ProofFile.SecondHashFunctionArgument} {pol lay' KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hd : ProofFile.onlineDescription o pol lay' KL = .ok F) (hplan : F.planOk = true) :
    (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ .K10) ∧ ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ .K10 := by
  obtain ⟨Z', N, -, -, hs, -⟩ := ToldDesc.shared_fits_descPure hd hplan
  obtain ⟨hl, -⟩ := ToldDesc.last_fits_descPure hd
  have hs' := beq_iff_eq.1 hs
  have hl' := beq_iff_eq.1 hl
  refine ⟨fun b hb e => ?_, fun b hb e => ?_⟩
  · have hm : b.place ∈ VerifiableInference.Desc.Shared.sharedPlaces N.O.isSome := by
      rw [← hs']
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    rcases VerifiableInference.Desc.Sound.sharedPlaces_kinds _ _ hm with h | h | h | h <;>
      rw [e] at h <;> cases h
  · have hm : b.place ∈ VerifiableInference.Desc.Last.lastPlaces := by
      rw [← hl']
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    rcases VerifiableInference.Desc.Sound.lastPlaces_kinds _ hm with h | h | h <;>
      rw [e] at h <;> cases h

/-- **WHAT THE KIND HOLDS AT A RETURN OF `onlineProverFromPublicFiles`**, at the readers, rows and statements of a lot. Of the
sides: at each place that the lot reads the first half has the lot's part, and no half of the kind
stands in the other two chains. Of the description: each place that the lot reads is tied to a link,
each link to a place, every sub-protocol of the kind is so tied, and at each place `fits` and `exact` as
the spender's half hold at the returned book, at the chain c and at the description's first chain. -/
def ClosingInForm {W₀ Rc Tr X₀ X : Type} (R : OnlineProverWithDescription W₀ Rc Tr X₀ X)
    (readers : Local W₀ Rc Inst Tr → Readers) (rows : RowDataOf Inst) (stAt : StAtOf Inst)
    (c : Chain S ProofFile.Cl) : Prop :=
  ClosingsFirst R.H.first readers rows stAt R.Z R.G ∧
  (∀ x ∈ R.H.shared, x.place.kind ≠ .K10) ∧ (∀ x ∈ R.H.second, x.place.kind ≠ .K10) ∧
  (∀ b ∈ c.blocksInOrder, b.place.kind = .K10 → ∃ l p Q, l < 25 ∧ Tied c R.Z l p Q b) ∧
  (∀ Q ∈ closePars R.Z, ∃ l p b, l < 25 ∧ Tied c R.Z l p Q b) ∧
  (∀ l, l < 25 →
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c R.Z l p Q b ∧
      ∀ fs : List (Fall S),
        ∃ σ : Side S ProofFile.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst,
          Side.seated c.blocksInOrder (closePlace Q)
              (closingPairs (closingJob readers rows stAt R.Z R.G Q)) fs = some σ ∧
          σ.block = b ∧
          ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place)
            (chain firstTree : Nat),
            Good pre Face.own σ R.B ord chain firstTree (fun _ _ _ _ => False)
              (fun _ _ _ _ => False) (closeOn true (closingJob readers rows stAt R.Z R.G Q))
              closeBud ∧
            ShowsSome pre Face.own σ chain firstTree
              (closeOn true (closingJob readers rows stAt R.Z R.G Q)) closeBud) ∧
  ∀ l, l < 25 →
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c R.Z l p Q b ∧
      ∀ fs : List (Fall R.F.S₁),
        ∃ σ : Side R.F.S₁ R.F.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst,
          Side.seated R.F.first.blocksInOrder (closePlace Q)
              (closingPairs (closingJob readers rows stAt R.Z R.G Q)) fs = some σ ∧
          ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place)
            (chain firstTree : Nat),
            Good pre Face.own σ R.B ord chain firstTree (fun _ _ _ _ => False)
              (fun _ _ _ _ => False) (closeOn true (closingJob readers rows stAt R.Z R.G Q))
              closeBud ∧
            ShowsSome pre Face.own σ chain firstTree
              (closeOn true (closingJob readers rows stAt R.Z R.G Q)) closeBud

/-- **THE CLOSING**: it holds where `onlineProverFromPublicFiles` returns, in scope, at the chain that `onlineFirstChainAt` makes, at
a filling that has a lot Lc with the halves of `seatLotC` and whose other lots have no half of the
kind, and where the description passes its tests on the plan. -/
theorem closing_in_form {W₀ Rc Tr X₀ X : Type} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {Fl : OnlineProverParts W₀ Rc Tr X₀ X} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol lay P.KL Fl = .ok R) (hplan : R.F.planOk = true)
    {c : Chain S ProofFile.Cl} (hc : ProofFile.onlineFirstChainAt R.Z = .ok c)
    (readers : Local W₀ Rc Inst Tr → Readers) (rows : RowDataOf Inst) (stAt : StAtOf Inst)
    {Lc : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} (hL : Lc ∈ Fl.lots)
    (hLc : Lc.halves R.Z R.G = (seatLotC readers rows stAt).halves R.Z R.G)
    (ho : ∀ M ∈ Fl.lots, (∀ e ∈ M.halves R.Z R.G, e.place.kind ≠ KindName.K10) ∨
      M.halves R.Z R.G = Lc.halves R.Z R.G) :
    ClosingInForm R readers rows stAt c := by
  obtain ⟨hZ, hG, hF, -, -, -, -, hf, -⟩ := atPure_ok h
  obtain ⟨-, -, -, -, p0, p1, p2, -, hB⟩ := atPure_book h
  obtain ⟨Bs, base, c', Sh, Se, O⟩ := atPure_open (X := X) h
  obtain rfl : c' = c := Except.ok.inj ((ToldDesc.pureChainAt_of_open O).symm.trans hc)
  obtain ⟨-, h2, h3⟩ := atPure_strays h
  obtain ⟨n2, n3⟩ := no_k10_later hF hplan
  refine ⟨first_of_kinds O readers rows stAt R.G hf hL hLc ho,
    fun x hx e => ?_, fun x hx e => ?_, fun b hb hk => k10_covered hS hR O hb hk,
    fun Q hQ => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨b, hb, hpl⟩ := side_on_chain h2 hx
    exact n2 b hb (by rw [hpl]; exact e)
  · obtain ⟨b, hb, hpl⟩ := side_on_chain h3 hx
    exact n3 b hb (by rw [hpl]; exact e)
  · exact pars_tied hS hR O hQ
  · exact closing_good_of_plan (X := X) readers rows stAt R.G hS hR O hB hplan l hl
  · exact closing_good_of_desc (X := X) readers rows stAt R.G hS hR O hB hplan l hl

/-- **None of the ten lots has a half of the kind.** -/
theorem k10_ten {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAt I o Sz O).lots, ∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K10 := by
  intro M hM x hx e
  rw [widerFillAt_lots] at hM
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
  have hk := (FirstFill.widerKinds I o Sz O Zq G).all q hq x hx
  have hm : q.2 ∈ ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName) :=
    List.mem_map.2 ⟨q, hq, rfl⟩
  rw [← hk, e] at hm
  simp at hm

/-- **The hypothesis `hand₁` of `file_owed_rows` at a row of the lot**, from a side seated at any falls. -/
theorem closing_hand_at {Bk : ProverCoinCounts} {St Cl' W₀ Rc Xi Tr X : Type} {bs : List (Block St Cl')}
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (T : Local W₀ Rc Xi Tr →
            Thread Bk St Cl' (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Sd : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    {fs₀ fs : List (Fall St)} {σ₀ : Side St Cl' (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {ord : List Place} {chain ft : Nat}
    (hσ : Side.seated bs (closePlace Q) (closingPairs (closingJob readers rows stAt Z G Q)) fs₀ =
      some σ₀)
    (g : Good pre Face.own σ₀ Bk ord chain ft (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (closeOn true (closingJob readers rows stAt Z G Q)) closeBud) :
    ∀ σ, ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd bs).side bs fs = some σ →
      ∃ A₁ B₁, Good pre Face.own σ Bk ord chain ft A₁ B₁
        ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd bs).On
        ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd bs).bud :=
  hand_of_house (closingRow (X := X) readers rows stAt Z G Q) T Sd hσ g

/-- The row's On asks nothing. -/
theorem closing_on {W X Pb V : Type} (J : CloseJob W) (u : Member V W X Pb)
    (ca : CsAll u.part.carries) (m : Mid W X) (f : Before) : closeOn true J u ca m f :=
  fun h => by cases h

/-- The row's bud asks nothing. -/
theorem closing_bud (n : Nat) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    closeBud n ds asks := trivial

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closing_hand_at
#print axioms ProofFile.Honest.K10.closing_on
#print axioms ProofFile.Honest.K10.closing_bud
#print axioms ProofFile.Honest.K10.closing_good_of_plan
#print axioms ProofFile.Honest.K10.closing_good_of_desc
#print axioms ProofFile.Honest.K10.k10_numbers
#print axioms ProofFile.Honest.K10.k10_covered
#print axioms ProofFile.Honest.K10.no_k10_later
#print axioms ProofFile.Honest.K10.ClosingInForm
#print axioms ProofFile.Honest.K10.closing_in_form
#print axioms ProofFile.Honest.K10.k10_ten
