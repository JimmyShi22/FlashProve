-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OwnerKindAtMaker.lean: whose coins the attention segments' own
rounds (kind K5: the label of that sub-protocol in the description) spend: at the book that the maker
returns, the owner of every entry handed to the place of the kind at link 2g + 1 is part 0 of the
code switch (kind K2) at piece 1 of that link.

  maskRowHolder       the address of the sending labelled "link l, moment 0" in the written description
  holderAt, written_holder_test   a closed fact: at the twelve odd links that address is part 0 of
                      piece 1 of the link, of the kind K2
  written_holder_other_part, _other_kind, _other_link   at none of the twelve links is it part 1; of
                      the kind K1; of the next link: the test is not idle
  k5_owner_address    conditional: h; hA: the statement
  k5_owner_kind       conditional: h; hA: so the owner's place is of the kind K2, at the same link: a
                      reader's form of the statement; no file calls it

How. The owner of such an entry is the owner of the link's mask row (plain_spent_row,
Honest/BookPlainHolder.lean); the sendings under the head are the written ones (sends_in_scope); the
head's first chain is alike to the written one, round by round and place by place
(planAlike_at_head).

Kin. rawRows_all (AtFullSide/K14/RawFactsWritten.lean) evaluates the mask rows of all links as owners
at the written description, with their first coins and free entries; the closed fact here reads less
of it, the address alone.

Limits. h, the library's head, is a hypothesis: that it can be met is not shown here. hA: the maker
returns at the filling P, a free variable. The closed facts are decided by Lean's kernel by evaluation
at the written lists. Where no entry is handed to the place nothing is said: that there is one is
k5_spender_at_maker (Honest/K5/Law/LotNotEmptyAtMaker.lean). This file names an address and nothing
else: that the owner's coins are uniform, or that a side stands at that address and hands them on as
it should, is not said here. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookPlainHolder
import Johnson.Desc.ProofFile.Honest.BookAlike
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsAtBook
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnsNothingAtMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)

/-! ## 1 Closed facts at the written description -/

/-- The address of the round of the sending labelled "link l, moment 0", in the written first chain. -/
def maskRowHolder (l : Nat) : Option Addr :=
  (((seedRounds WP.first.blocksInOrder).zip proofSendsFull.1.sends).find? fun x =>
    x.2.label == s!"link {l}, moment 0").bind fun x => addrOfRound WP.first.blocksInOrder x.1

/-- At link l that address is the part number n of piece 1 of link m, of the kind k. -/
def holderAt (k : KindName) (m n l : Nat) : Bool :=
  maskRowHolder l == some ⟨⟨1, some m, 1, k⟩, n⟩

set_option maxRecDepth 1000000 in
/-- **At the twelve odd links the sending stands at part 0 of piece 1 of the link, of the kind K2.** A
closed fact. -/
theorem written_holder_test :
    ((List.range 12).all fun g => holderAt .K2 (2 * g + 1) 0 (2 * g + 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At none of the twelve is it part 1. A closed fact: the test is not idle. -/
theorem written_holder_other_part :
    ((List.range 12).any fun g => holderAt .K2 (2 * g + 1) 1 (2 * g + 1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At none of the twelve is it of the kind K1. A closed fact: the test is not idle. -/
theorem written_holder_other_kind :
    ((List.range 12).any fun g => holderAt .K1 (2 * g + 1) 0 (2 * g + 1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At none of the twelve is it at the next link. A closed fact: the test is not idle. -/
theorem written_holder_other_link :
    ((List.range 12).any fun g => holderAt .K2 (2 * g + 2) 0 (2 * g + 1)) = false := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE OWNER OF EVERY ENTRY HANDED TO THE PLACE OF THE KIND AT LINK 2g + 1 IS PART 0 OF THE CODE
SWITCH AT PIECE 1 OF THAT LINK.** CONDITIONAL: h; hA: the maker returns A at a filling P, P a free
variable. -/
theorem k5_owner_address (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {g : Nat} (hg : g < 12)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.spender.place = ⟨1, some (2 * g + 1), 3, .K5⟩ →
      e.owner = ⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩ := by
  have hB := K14.atPure_book_at_head h hA
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨blk, a', hm, -, Dc⟩ := k5_member h hg
  have hb : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  have hpl : blk.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := Dc.place
  have hl : blk.place.link = some (2 * g + 1) := by rw [hpl]
  have h5 : blk.place.kind = .K5 := by rw [hpl]
  intro e he hs
  obtain ⟨row, hrow, eo⟩ := plain_spent_row hB hp hb (k5_no_seed blk (parAt Zp g a') Dc.rounds)
    (k5_no_fold blk (parAt Zp g a') Dc.rounds) hl
    (fun a ea => ProofFile.Honest.Small.no_merge_of_kind _ a (by rw [ea, h5]; exact fun c => nomatch c)
      (by rw [ea, h5]; exact fun c => nomatch c)) e he (hs.trans hpl.symm)
  obtain ⟨y, hy, ha⟩ := ownerOf_found hrow
  have eS : Zp.made.proof = proofSendsFull :=
    VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h)
  rw [eS] at hy
  have A1 := (K14.planAlike_at_head h).first
  have hH : maskRowHolder (2 * g + 1) = some e.owner := by
    unfold maskRowHolder
    rw [seedRounds_alike A1, hy]
    show addrOfRound WP.first.blocksInOrder y.1 = _
    rw [addrOfRound_alike A1, eo]
    exact ha
  have ht := List.all_eq_true.1 written_holder_test g (List.mem_range.2 hg)
  unfold holderAt at ht
  rw [hH] at ht
  exact Option.some.inj (beq_iff_eq.1 ht)

/-- **So the owner's place is of the kind K2, at the same link.** CONDITIONAL: h; hA. -/
theorem k5_owner_kind (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {g : Nat} (hg : g < 12)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.spender.place = ⟨1, some (2 * g + 1), 3, .K5⟩ →
      e.owner.place.kind = .K2 ∧ e.owner.place.link = some (2 * g + 1) := by
  intro e he hs
  rw [k5_owner_address h hg hA e he hs]
  exact ⟨rfl, rfl⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.written_holder_test
#print axioms ProofFile.Honest.K5.written_holder_other_part
#print axioms ProofFile.Honest.K5.written_holder_other_kind
#print axioms ProofFile.Honest.K5.written_holder_other_link
#print axioms ProofFile.Honest.K5.k5_owner_address
#print axioms ProofFile.Honest.K5.k5_owner_kind
