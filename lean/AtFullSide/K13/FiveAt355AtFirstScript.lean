-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/FiveAt355AtFirstScript.lean: kind K13, the members' batching: THE FIVE STATEMENTS AT
NUMBER 355 OF THE PROOF FILE's FIRST CHAIN, AS ONE VALUE OF `FiveAtBorder`
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean), AT THE FIRST THREAD AS IT IS WRITTEN
(`firstThread`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) WITH THE WRITTEN SCRIPT OF
THE FIRST CHAIN IN THE SCRIPT's PLACE (`firstScriptAt`, AtFullSide/K1/FirstScript.lean), OVER THE
PROVER THAT THE MAKER RETURNS AT THE WIDE FILLING (`onlineProverPartsInUse`,
Johnson/Desc/ProofFile/Honest/K1/Law/WSideAtFill.lean). NO PREMISE ON THE SCRIPT IS LEFT. Statements
with their proofs: calls; no definition. THE FULL SIZE ALONE, AT THE FORMAT's SECOND HASH FUNCTION
ALONE.

Main names, each with ALL its premises:
  `k13_coinsTie_at_firstScript`: `CoinsTie` at 355 (the mask entries under the slots that the
    verifier takes are the coins that the book lends the kind's sumcheck's part) at that Script, at
    every other parameter of the thread: h (the library's one hypothesis at the full size, at A's
    public part) and hA (the maker returns A at the wide filling, at the format's second hash
    function in
    both places).
  `k13_matTie_at_firstScript`: `MatTie` (the Script's cells at the thread's one input are the matrix
    that the index's reader gives) at that Script and the filling's own reader: h alone.
  `k13_five_at_firstScript`: **`FiveAtBorder (firstThread hd ⟨firstScriptAt I S Op A hd.firstChain,
    numbers⟩ w) Said fall 355`**, at every Said, fall, numbers and w: hA · hd (the head at A) · hO:
    the filling's filler of the pile is the written one, `pileAnyK3`.

How. `CoinsTie`: kind K1's record of premises holds at that Script at the opening
(`k1Seated_first`, FirstScript.lean), at a job whose plan and ride are read off its text; then
`k13_coinsTie_at_maker` (CoinsTieAtMaker.lean of this folder). `MatTie`: the Script's cells are by
its text the library's matrix of cells of the reader's entries; then `k13_matTie_of_cellsOfF`
(Johnson/Desc/ProofFile/Honest/K13/MatTieOfReaderCells.lean). The five:
`k13_five_at_firstThread` (Johnson/Desc/ProofFile/Honest/K13/AtFirstThread355.lean).

Limits. ALL FIVE ARE PREMISES' FORMS, from "the thread and what is said stand in front of the
member": that the thread stands at any border of this chain at any run is shown neither here nor in
any file that this one imports, and
where it stands nowhere the five speak of nothing. `AcceptedS` at this member is on the shape of the
verifier's state and the sizes of what was sent; what is said of the values that were sent is the
item "pileOne" of `ExchangeS`. `CoinsTie` speaks at each run's coins one by one, and is no statement
on their distribution. ON WRITTEN NUMBERS beneath it: where the book's entry for the kind's row
begins, where the sender's mask entries of the index masks' message begin, and how many entries the
verifier has taken in front of the member are counted by three texts, which meet at the full size's
written data, each by its own evaluation in Lean's kernel: no law joins the texts, and no program
was compared (CoinsTieFive.lean of this folder, Limits). `MatTie` holds by the Script's own text: it
says nothing of what a prover stores or commits to. The wide filling is defined in
Honest/K1/Law/WSideAtFill.lean. THIS FILE DOES NOT SHOW THAT THE MAKER RETURNS AT IT; no statement
here is at a named Op:
that the honest prover's has the written filler is by its text (`openHonest`,
Johnson/Desc/ProofFile/Honest/OpenHonest.lean), and that filler lays placeholders in two of a row's
four fields.

What is not claimed. That a head stands at any A; that the maker returns. That a run of the honest
prover has this Script. What the kind owes beside this border: number 356 of the same chain, the
sending of the message W with a step of this kind joined behind it. Nothing on soundness,
completeness or hiding.
-/
import AtFullSide.K1.FirstScript
import AtFullSide.K13.CoinsTieAtMaker
import Johnson.Desc.ProofFile.Honest.K13.AtFirstThread355
import Johnson.Desc.ProofFile.Honest.K13.MatTieOfReaderCells
import Johnson.Desc.ProofFile.Honest.K1.Law.StartAtFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13 ProofFile.Honest.K1
open VerifiableInference.Desc (Chain Strs Place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`CoinsTie` AT 355, AT THE WRITTEN SCRIPT**: under the head and the maker's return alone.
weights, pile: any. -/
theorem k13_coinsTie_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) {weights : W₀ → Weights}
    {pile : PileOf ProofFile.Inst} :
    CoinsTie (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      355 weights pile h.𝔇.P13 (k13ReaderAt h) := by
  obtain ⟨⟨blk, K⟩, -, -⟩ := k1Seated_first h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact k13_coinsTie_at_maker h hA _ test carryX item n₁ n₂ b₀ Vd Rd Kp w K rfl
    (ride_of_job rfl)

/-- **`MatTie` AT THE WRITTEN SCRIPT**, at the filling's own reader of the index: under the head
alone. pile: any. -/
theorem k13_matTie_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) {pile : PileOf ProofFile.Inst} :
    MatTie (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (I.weights A.Z) pile h.𝔇.P13 (k13ReaderAt h) :=
  k13_matTie_of_cellsOfF h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w rfl

/-- **THE FIVE STATEMENTS AT 355, AT THE FIRST THREAD WITH THE WRITTEN SCRIPT**, at every Said and
every fall: from the maker's return at the wide filling, the head at it, and the written filler of
the pile. -/
theorem k13_five_at_firstScript
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (hd : HeadAtReturn Z A) (numbers : FallNumbers) (w : LocB W₀) (hO : Op.pile = pileAnyK3)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder (firstThread hd ⟨firstScriptAt I S Op A hd.firstChain, numbers⟩ w) Said fall
      355 := by
  have hM : MatTie (firstLetters hd ⟨firstScriptAt I S Op A hd.firstChain, numbers⟩ w)
      (I.weights A.Z) (pileAnyK3 A.Z A.G) hd.head.𝔇.P13 (k13ReaderAt hd.head) := by
    unfold firstLetters
    exact k13_matTie_at_firstScript hd.head _ _ _ _ _ _ _ _ _ w
  have hC : CoinsTie (firstLetters hd ⟨firstScriptAt I S Op A hd.firstChain, numbers⟩ w) 355
      (I.weights A.Z) (pileAnyK3 A.Z A.G) hd.head.𝔇.P13 (k13ReaderAt hd.head) := by
    unfold firstLetters
    exact k13_coinsTie_at_firstScript hd.head hA _ _ _ _ _ _ _ _ _ w
  exact k13_five_at_firstThread I OnBytes.secondHashFunction S Op hA hd
    ⟨firstScriptAt I S Op A hd.firstChain, numbers⟩ w Said hO hM hC fall

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_coinsTie_at_firstScript
#print axioms AtFullSide.K13.k13_matTie_at_firstScript
#print axioms AtFullSide.K13.k13_five_at_firstScript
