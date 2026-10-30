-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MaskFits.lean: WHICH COIN STANDS AT WHICH ENTRY OF A MESSAGE's
MASK ROWS (Honest/K2/Law/MaskCoin.lean), UNDER THE SHARED SENDING's PUBLIC TEST ALONE: the premise
"one run" of that file's two sentences is paid by `rowsAll_returns` (Honest/K2/Law/Laid.lean).
Statements with their proofs; no definition.

  `maskEntry_coin_fits`, `maskEntry_in_fits`   the two sentences at a sending that passes
                 `K1.sendFits`
  `switch_maskEntry_coin_fits`, `switch_maskEntry_in_fits`   the same at the switch's part

Limits. Those of Honest/K2/Law/MaskCoin.lean. Whether a sending of the plan passes the test is not
said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (Sizes zeroG)

/-- A sending that passes the public test has one run that returns: at a table and main rows of
zeros and coins of zeros. -/
theorem one_run {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) :
    ∃ table₀ data₀ c₀ V₀, rowsAll table₀ codes sent fresh data₀ c₀ = .ok V₀ := by
  obtain ⟨V, hV⟩ := rowsAll_returns hf (fun _ _ _ _ _ => zeroG) (fun _ _ _ => zeroG)
    ⟨fun _ => OnBytes.Slice.toF 0, fun _ => zeroG⟩
  exact ⟨_, _, _, V, hV⟩

/-- **The sender lays its own coin**, at a sending that passes the public test. -/
theorem maskEntry_coin_fits {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) {n : Nat}
    (hn : n < sent.size) (hfold : foldAt fresh n = none) (table : FreshTable)
    (data : Nat → Nat → Nat → Cb.Gl.E) :
    ∀ (cs : Cs (sendingDue codes sent fresh)) (ν : Nat), ν < maskLength codes sent n →
      maskEntry table codes sent fresh data n cs ν =
        (coinsE cs).getD (maskBase codes sent fresh n + ν) OnBytes.zeroE :=
  maskEntry_coin (one_run hf) hn hfold table data

/-- **These numbers lie below the sending's count.** -/
theorem maskEntry_in_fits {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) {n : Nat}
    (hn : n < sent.size) (hfold : foldAt fresh n = none) :
    ∀ ν : Nat, ν < maskLength codes sent n →
      maskBase codes sent fresh n + ν < (sendingDue codes sent fresh).e :=
  maskEntry_in (one_run hf) hn hfold

/-- **The sender lays its own coin, at the switch's part.** cs: the part's own coins. Of the part
its count alone is read, which hangs on no sender: the sentence is on `rowsAll`, not on Sd. -/
theorem switch_maskEntry_coin_fits (Sd : Sender) {Z : Sizes} {others : Array OnBytes.OracleNotice}
    {k : Nat} (carries : List (String × Due))
    (hf : K1.sendFits (sendingPar Z.codes (switchSent Z others))
      (rideOf (switchSent Z others) (switchFresh Z others k)) = true)
    {n : Nat} (hn : n < (switchSent Z others).size) (hl : n ≠ (switchSent Z others).size - 1)
    (table : FreshTable) (data : Nat → Nat → Nat → Cb.Gl.E) :
    ∀ (cs : Cs (switchPart Sd Z others k carries).takes) (ν : Nat),
      ν < maskLength Z.codes (switchSent Z others) n →
      maskEntry table Z.codes (switchSent Z others) (switchFresh Z others k) data n cs ν =
        (coinsE cs).getD (maskBase Z.codes (switchSent Z others) (switchFresh Z others k) n + ν)
          OnBytes.zeroE :=
  switch_maskEntry_coin Sd carries (one_run hf) hn hl table data

/-- **These numbers lie below the part's own count.** Of the part its count alone is read. -/
theorem switch_maskEntry_in_fits (Sd : Sender) {Z : Sizes} {others : Array OnBytes.OracleNotice}
    {k : Nat} (carries : List (String × Due))
    (hf : K1.sendFits (sendingPar Z.codes (switchSent Z others))
      (rideOf (switchSent Z others) (switchFresh Z others k)) = true)
    {n : Nat} (hn : n < (switchSent Z others).size) (hl : n ≠ (switchSent Z others).size - 1) :
    ∀ ν : Nat, ν < maskLength Z.codes (switchSent Z others) n →
      maskBase Z.codes (switchSent Z others) (switchFresh Z others k) n + ν <
        (switchPart Sd Z others k carries).takes.e :=
  switch_maskEntry_in Sd carries (one_run hf) hn hl

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.one_run
#print axioms ProofFile.Honest.K2.maskEntry_coin_fits
#print axioms ProofFile.Honest.K2.maskEntry_in_fits
#print axioms ProofFile.Honest.K2.switch_maskEntry_coin_fits
#print axioms ProofFile.Honest.K2.switch_maskEntry_in_fits
