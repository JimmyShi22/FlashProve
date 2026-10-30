-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondAll.lean: kind K14: "K14, second part" (the place
⟨3, none, 0, .K14⟩): THE TWO TESTS OF secondRest2 (Honest/K14/SecondTerms.lean), "adopt: statement
and book are in step" AND "join: no member twice", MET UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean), THE START's RETURN AND THE RETURN OF A FOLD OVER THE FIRST CHAIN's FLAT
LIST; so no test of secondDoor is left as a premise: it follows from these three, ThrS at the shared
chain's last border, and sW. Statements with their proofs: calls of the library's laws. No
definition.

  start_st_book   a state that the start of the last chain returns has the statement and the book of
                  the first chain's last state: by start_at_last (Honest/K14/SecondDoor.lean), the
                  library's start₃E_st (Johnson/Desc/Third/Law/Start.lean), start₃E_book
                  (Johnson/Desc/Third/Law/StartBook.lean) and firstOfS_parts
                  (Johnson/Desc/Last/ShapeRowZero.lean)
  adopt_at_fold   **"adopt: statement and book are in step" is true**: the library's bookHas_fold
                  (Johnson/IMR/AtReachFits.lean) at the fold
  join_at_fold    **"join: no member twice" is true**: noTwice_of_order
                  (Honest/K14/SecondDoor.lean) from the statement's being in order
                  (OnBytes.Means.InOrder): a field of Tidy, which the library's tidy_at_open_raw
                  (Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean) and tidy4B_iff give at the fold,
                  through its reach_of_fold (Johnson/Top/H0/Walk/Reach.lean). That law asks that the
                  state bears no mark: the start's return gives that: start_at_last's clause that
                  the first chain stands at its end, and the library's fin_clean
                  (Johnson/ToldDescR/StartClean.lean)
  rest2_at_fold   so the whole list secondRest2. (Its arm without a border is empty; at a start's
                  return there is a border)
  second_door_fold   **secondDoor from the head, ThrS at the shared chain's last border, the start's
                  return, the fold's return and sW**: second_door_two_fold's statement
                  (Honest/K14/SecondTerms.lean) without its premise on secondRest2

"FOLD" MEANS foldBlocks 0 cF.blocksInOrder FROM THE FIRST CHAIN's OWN START, AT ANY ROUNDS AND COLUMNS AT
WHICH IT RETURNS. NO RUN, NO PROVER AND NO INSTANCE's WITNESS IS NAMED.

What stays a premise in second_door_fold: the head; ThrS at the shared chain's last border at s₂;
the start's return at s₁ and s₂; hF: s₁ is that fold's return; sW (where W's pad lies).

What is not claimed. That one of these premises holds at any run, or that they can hold together:
THE FOLD's RETURN IS SHOWN OF NO ROUNDS. That the head holds at other files than those at which the
library shows it. That the sub-protocol accepts: secondDoor is a list of this kind's own (door_owed,
Honest/K14/SecondDoor.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondTerms
import Johnson.IMR.AtReachFits
import Johnson.Desc.AtSeats.Fit.TidyAtOpen
import Johnson.ToldDescR.StartClean
import Johnson.Desc.Third.Law.Start
import Johnson.Desc.Third.Law.StartBook
import Johnson.Desc.Last.ShapeRowZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linLayW)
open VerifiableInference.Desc (Chain Place foldBlocks OpenedColumn)
open VerifiableInference.Desc.Ground (ok has)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (start₃E_st start₃E_book)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

section fold
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)

/-- A state that the start of the last chain returns has the statement and the book of the first
chain's last state. -/
theorem start_st_book (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    s.st = s₁.st ∧ s.book = s₁.book := by
  obtain ⟨f, e, -, hf, -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  have e1 := start₃E_st _ _ _ _ _ _ _ _ _ _ _ hst
  have e2 := (start₃E_book _ _ _ _ _ _ _ _ _ _ _ hst).1
  have hp := VerifiableInference.Desc.Last.firstOfS_parts hf
  exact ⟨e1.trans hp.1, e2.trans hp.2.1⟩

variable {Zp Np cF}

/-- **"adopt: statement and book are in step" is true**: under the library's head, at the state that
the start of the last chain returns of s₁, where foldBlocks 0 cF.blocksInOrder returns s₁ of the first
chain's own start. -/
theorem adopt_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl)) :
    (s.st.oracles.size == s.book.place.size) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨e1, e2⟩ := start_st_book Zp Np cF x s₁ s₂ s hs
  have hb := Meaning.K2.bookHas_fold h.scope h.reads O (P5J.flat_ok h.toAtMg)
    (k := cF.blocksInOrder.length) (z := p) (s := s₁) (rs := rs) (r := r') (cols := cols) (q := cl)
    (by rw [List.take_length]; exact hF)
  rw [e1, e2, hb]
  exact beq_self_eq_true _

/-- **"join: no member twice" is true**, under the same. -/
theorem join_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl)) :
    has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨e1, -⟩ := start_st_book Zp Np cF x s₁ s₂ s hs
  obtain ⟨-, -, hfin, -⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  have ht := Meaning.K2.tidy_at_open_raw h.laid.value h.laid.planOk O cF.blocksInOrder.length (p, s₁)
    (Johnson.Desc.First.Walk.Tied.reach_of_fold cF.blocksInOrder.length (Nat.le_refl _) s₁ rs r' cols cl
      (by rw [List.take_length]; exact hF)) (ToldDesc.fin_clean hfin).1
  have hI : OnBytes.Means.InOrder s.st := by
    rw [e1]
    exact (OnBytes.Means.tidy4B_iff.1 ht).inOrder
  obtain ⟨-, G, -, -, hG, -⟩ := start_w_member Zp Np cF x s₁ s₂ s hs
  exact noTwice_of_order s hI G hG

/-- So the whole list secondRest2 is true there. -/
theorem rest2_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl)) :
    ok (secondRest2 s) = true := by
  unfold secondRest2
  cases hb : s.loc.border with
  | none => rfl
  | some b =>
    dsimp only
    rw [ok_cons, ok_cons, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨adopt_at_fold h x s₁ s₂ s hs p rs cols r' cl hF,
      join_at_fold h x s₁ s₂ s hs p rs cols r' cl hF, rfl⟩

end fold

section top
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **secondDoor, with no test of the list left as a premise**: from the library's head; ThrS at the
shared chain's last border at s₂; the start's return s at s₁ and s₂; hF: foldBlocks 0 cF.blocksInOrder
returns s₁ of the first chain's own start; and sW: where W's pad lies. -/
theorem second_door_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl))
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol)) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true :=
  second_door_two_fold Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h
    Said hA x s₁ s hs p rs cols r' cl hF sW (rest2_at_fold h x s₁ s₂ s hs p rs cols r' cl hF)

end top

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.start_st_book
#print axioms ProofFile.Honest.K14.adopt_at_fold
#print axioms ProofFile.Honest.K14.join_at_fold
#print axioms ProofFile.Honest.K14.rest2_at_fold
#print axioms ProofFile.Honest.K14.second_door_fold
