-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HalfAtW.lean: THE SHARED "SENDING" (the kind K1) AT W's PLACE
(number 356 of the first chain; ⟨1, none, 4, .K1⟩): THE RECORD's FIELD half (K1Seated,
Honest/K1/Seated.lean), AT THE PROVER THAT onlineProverFromPublicFiles MAKES OF ANY FILLING THAT HOLDS W's SIDE. THE
FILLING IS A LETTER. Four theorems; NO DEFINITION: NO NEW TEXT OF A SIDE.

W's SIDE IS AN HLot ALREADY: wSide wit no D (Honest/K1/PlaceW.lean). ITS LETTER no IS IDLE: wSide
wit no D = wSide wit no' D (wSide_any_no, Honest/K1/HalvesFree.lean): so it wants no numbers of the
public part, and whoever lays it hands any.

  - wHalves_head  UNDER h (the library's head: A HYPOTHESIS): at the head's public part W's side
                  has one half: placeHalf wit of the job wJobAt Zp.first (wGp Zp) 4 wMsgFull ‹any
                  number› (D Zp G): by msg_w_head (Honest/K1/Law/FitsAtW.lean).
  - wHalves_find_head   so the search at W's place in that list finds it.
  - half_w_of_lots   UNDER h, hA (onlineProverFromPublicFiles returns A AT A FILLING P: A LETTER), hex (SOME LOT OF P
                  HAS, AT A's PUBLIC PART AND GROUND, W's SIDE's HALVES: wHalves wit no D: the form
                  that another pen's HalfAtFill.lean has at the 51: a lot that ProofFile's HLot.byPub
                  wraps is no wSide … at any one reader, but has its halves there), ho (every lot
                  of P has there no half AT W's PLACE, or these halves: BY THE PLACE, NOT BY THE
                  KIND: K1's own lot stands at places of the kind K1 too): the search at W's place
                  in A.H.first finds placeHalf wit J, at the job J of Honest/K1/Law/RecordAtW.lean
                  with Dw := D Zp A.G: by ProofFile's atPure_first_find (Honest/FirstFind.lean), which
                  has the filling as a letter.
  - half_w_head_of_lots   THE FIELD, TO THE LETTER, at L := lettersHead h A.H ….

Limits. THAT ANY FILLING HOLDS W's SIDE IS A PREMISE. AT ProofFile's widerFillAt THE SEARCH AT W's PLACE
FINDS NOTHING (another house's k1_none_behind_all, Honest/Thread/FirstFillAll.lean, at c := 1, pc
:= 4; not called here): so hex and ho cannot both hold there, and these laws say nothing at that
filling. That onlineProverFromPublicFiles returns is a hypothesis; so is the head. Nothing on the data D: what they lay
is another file's. The record's fields member, hasCoins, msgs and pads stay as RecordAtW.lean
hands them on. THE FULL SIZE, THE FORMAT's EARLIER HASH. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K1.HalvesFree
import Johnson.Desc.ProofFile.Honest.K1.LotNoPure
import Johnson.Desc.ProofFile.Honest.FirstFind
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block Strs Place)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD W's SIDE HAS ONE HALF: THE JOB's.** -/
theorem wHalves_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X : Type}
    (wit : W → PlaceIn ProofFile.Inst) (no : Place → ℕ) (Dd : Pub → Ground → RowDataOf ProofFile.Inst)
    (G : Ground) :
    wHalves (V := V) (X := X) wit no Dd Zp G =
      [placeHalf wit (wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp G))] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  unfold wHalves
  rw [msg_w_head h O]
  rfl

/-- So the search at W's place finds it, whatever number the job's letter "first" holds. -/
theorem wHalves_find_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X : Type}
    (wit : W → PlaceIn ProofFile.Inst) (no : Place → ℕ) (Dd : Pub → Ground → RowDataOf ProofFile.Inst)
    (G : Ground) (first : ℕ) :
    (wHalves (V := V) (X := X) wit no Dd Zp G).find? (fun g => g.place == ⟨1, none, 4, .K1⟩) =
      some (placeHalf wit (wJobAt Zp.first (wGp Zp) 4 wMsgFull first (Dd Zp G))) := by
  rw [wHalves_any_no wit no (fun _ => first) Dd Zp G, wHalves_head h wit (fun _ => first) Dd G]
  rfl

/-- **THE SEARCH AT W's PLACE, AT THE PROVER OF ANY FILLING THAT HOLDS W's SIDE.** -/
theorem half_w_of_lots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → PlaceIn ProofFile.Inst) (no : Place → ℕ)
    (Dd : Pub → Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ g ∈ M.halves A.Z A.G, g.place ≠ ⟨1, none, 4, .K1⟩) ∨
      M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
      (Dd Zp A.G)) :
    (A.H.first.find? fun g => g.place == J.P.place) = some (placeHalf wit J) := by
  obtain ⟨hZ, -⟩ := atPure_at_laid h.laid hA
  subst hJ
  obtain ⟨M, hM, e⟩ := hex
  refine atPure_first_find hA hM (fun M' hM' => (ho M' hM').imp id fun e' => e'.trans e.symm) ?_
  rw [e, hZ]
  exact wHalves_find_head h wit no Dd A.G _

/-- **THE RECORD's FIELD half AT 356, TO THE LETTER**, at lettersHead at the prover A.H. -/
theorem half_w_head_of_lots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → PlaceIn ProofFile.Inst) (no : Place → ℕ)
    (Dd : Pub → Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ g ∈ M.halves A.Z A.G, g.place ≠ ⟨1, none, 4, .K1⟩) ∨
      M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
      (Dd Zp A.G))
    {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) :
    ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).hs.find? fun g =>
      g.place == J.P.place) = some (placeHalf wit J) :=
  half_w_of_lots h hA wit no Dd hex ho hJ

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.wHalves_head
#print axioms ProofFile.Honest.K1.wHalves_find_head
#print axioms ProofFile.Honest.K1.half_w_of_lots
#print axioms ProofFile.Honest.K1.half_w_head_of_lots
