-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotsMask.lean: K5's EQUATION ON THE SCRIPT's MASK ROW
(`EMaskRaw`, ScriptQRaw.lean in this folder) IS THE FRAME's FORM "OWN ENTRIES OF A MESSAGE"
(`OwnMsgs`, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) AT ONE TEXT, BOTH WAYS. IT PAYS
NOTHING OF THE SCRIPT: both sides are premises' forms. Two definitions with code; two theorems.

What it is for. The frame's file lays a Script from lots, and proves that the laying meets `OwnMsgs`
at a lot with which the other lots of the same message agree. K5's laws spend `EMaskRaw`. With this
file a lot at K5's own slots of the mask row pays it.

Main names:
  `maskTxt Bk Z ν₅`: THE TEXT THAT K5 WOULD HAND IN AS A LOT's: in the mask table, row 0, at the
    place ν₅ + j: the value of member number j of the list `coins5 Bk k Z` (ScriptQ.lean in this
    folder), for j below that list's length; "none" everywhere else. With it go n := `maskNo5 h x₁
    kM hk` and fx := 0.
  `maskAnswers Z ν₅ mask row place`: a test with code on public data. `maskTxt_isSome`: UNDER THE
    BOOK's TEST the text answers just where that test says so. `eMaskRaw_iff_ownMsgs`: `EMaskRaw h Q
    Vd N x₁ kM hk Z ν₅` holds just if `OwnMsgs Q Vd N (maskNo5 h x₁ kM hk) 0 (maskTxt Bk Z ν₅)`
    does.

How. By the change of index place = ν₅ + j. `maskTxt_isSome`: where the lending returns the coins
are as many as the kind takes slots: `coins5_are` (CoinsFewOf.lean in this folder).

Limits. The text reads the coins and no challenge. The default zeroE of the text's `getD` is read at
no entry at which the text answers: the test place - ν₅ < (coins5 Bk k Z).length stands in the same
"if". How many entries it owns hangs on the coins by its text; UNDER THE BOOK's TEST (`Lends5`,
CoinsFewOf.lean) it does not: `maskTxt_isSome`: the text answers just where `maskAnswers`, a test on
public data, says so. That no other lot answers otherwise at these entries is not treated here.
`maskNo5` hangs on the hypothesis h and is no term with code. Through its imports the file stands
above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md,
L15): a fact on import lines.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQRaw
import Johnson.Desc.ProofFile.Honest.K5.Law.CoinsFewOf
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (sigListCalls)
open VerifiableInference.Desc.First.Att.P (slotsOf script)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open P5J (AtMgA TS CellsM)

/-- **K5's own entries of the message with the mask row**: the text of a lot, with n := `maskNo5 h
x₁ kM hk` and fx := 0. It reads the coins alone. -/
def maskTxt (Bk : ProverCoinCounts) {W : Type} (Z : Seat5) (ν₅ : ℕ) :
    Coins Bk → W → List Fmt.Drawn → Bool → ℕ → ℕ → Option OnBytes.Slice.GE :=
  fun k _ _ mask row place =>
    if mask = true ∧ row = 0 ∧ ν₅ ≤ place ∧ place - ν₅ < (coins5 Bk k Z).length then
      some (Reading.gl.val ((coins5 Bk k Z).getD (place - ν₅) zeroE))
    else none

/-- **Where K5's text answers**: a test with code on public data: the mask table, row 0, a place
from ν₅ on, below ν₅ and the number of slots that the kind takes. -/
def maskAnswers (Z : Seat5) (ν₅ : ℕ) (mask : Bool) (row place : ℕ) : Bool :=
  mask && decide (row = 0) && decide (ν₅ ≤ place) &&
    decide (place - ν₅ < slotsOf (script Z.P.x))

/-- **K5's TEXT ANSWERS JUST WHERE THAT TEST SAYS SO**, whatever the run's coins, the input and the
challenges. CONDITIONAL: hB: THE BOOK's TEST: at every run's coins the book's lending to K5's row
returns. -/
theorem maskTxt_isSome {W₀ Rc Xi X Tr W : Type} {Bk : ProverCoinCounts} {cells : Tr → Cells} {Z : Seat5}
    (hB : Lends5 W₀ Rc Xi X Bk cells Z) (ν₅ : ℕ) (k : Coins Bk) (w : W) (hd : List Fmt.Drawn)
    (mask : Bool) (row place : ℕ) :
    (maskTxt Bk Z ν₅ k w hd mask row place).isSome = maskAnswers Z ν₅ mask row place := by
  obtain ⟨u, hu⟩ := hB k
  have e := coins5_are hu
  unfold maskTxt maskAnswers
  rw [e]
  by_cases c : mask = true ∧ row = 0 ∧ ν₅ ≤ place ∧ place - ν₅ < slotsOf (script Z.P.x)
  · rw [if_pos c]
    obtain ⟨c1, c2, c3, c4⟩ := c
    symm
    simp only [Option.isSome_some, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩
  · rw [if_neg c]
    symm
    rw [Option.isSome_none, Bool.eq_false_iff]
    intro t
    simp only [Bool.and_eq_true, decide_eq_true_eq] at t
    exact c ⟨t.1.1.1, t.1.1.2, t.1.2, t.2⟩

variable {Z₀ : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z₀ D₀ r Zp Np cF x₀} {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- **K5's EQUATION ON THE MASK ROW IS THE FRAME's FORM AT THAT TEXT.** -/
theorem eMaskRaw_iff_ownMsgs {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z : Seat5} {ν₅ : ℕ} :
    EMaskRaw h Q Vd N x₁ kM hk Z ν₅ ↔
      OwnMsgs Q Vd N (maskNo5 h x₁ kM hk) 0 (maskTxt Bk Z ν₅) := by
  constructor
  · intro H k w hd hv hN mask row place y hy
    unfold maskTxt at hy
    split at hy
    · rename_i c
      obtain ⟨c1, c2, c3, c4⟩ := c
      subst c1
      subst c2
      have e := H k w hd hv hN (place - ν₅) c4
      rw [Nat.add_sub_of_le c3] at e
      exact e.trans (Option.some.inj hy)
    · cases hy
  · intro H k v hd hv hN j hj
    refine H k v hd hv hN true 0 (ν₅ + j) _ ?_
    unfold maskTxt
    rw [if_pos ⟨rfl, rfl, Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hj⟩,
      Nat.add_sub_cancel_left]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.maskTxt_isSome
#print axioms ProofFile.Honest.K5.eMaskRaw_iff_ownMsgs
