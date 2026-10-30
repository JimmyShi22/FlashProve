-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/AlikeInScope.lean (kind K10): THE TWO SENTENCES OF SeatsOfLink.lean AT
THE COMPOSED MEANING's OWN LETTERS (`P5J.At.ms`, `P5J.At.N`, `P5J.At.pseats`:
Johnson/P5J/LettersAt.lean), IN THE GOALS' SCOPE, WHERE THE VERIFIER's OWN VALUE IS LAID
(`P5J.LaidAt`). Theorems: a joining: nothing is evaluated here.
How. AlikeFull.lean has the two sentences at the written values, by Lean's kernel. Three
joints carry the written values to the letters: the plan's seats and the table's numbers' core
(`LaidAt.seats`, `LaidAt.N_core`: Johnson/P5T/CoreAtMg.lean); the sendings (`sends_in_scope`:
Johnson/Goal/Numbers/MadeInScope.lean); the radii off the rows of the sendings (`rad_in_scope`:
Johnson/HB/LLHARD/RadiiInScope.lean).
  `rad_at_laid`: the letters' radii are the written ones. `ms_at_laid`: **`P5J.At.ms Zp Z.lay = msOf
    mlFull`.** `group_at_laid`: a link's group at `P5J.At.N Zp cF` is the written numbers'.
  `alike_at_laid`, `hit_at_laid`: **at every l < 26, lo the l-th written list: every member of
    `P5J.At.ms Zp Z.lay` at a tenant of the link's group is alike to a place of lo at `seatK10 lo
    (P5J.At.pseats Zp) l`; and every place of lo is alike to a member.**
PREMISES. hW: the scope. L: the value is laid, at the second hash function `OnBytes.secondHashFunction` (the
radii's joint is typed there alone). **hr: THE ROWS' MAKER RETURNS** (`Johnson.G.sendRowsOf Z.pol
Z.lay Z.KL = .ok R`): asked by no test of the verifier, given by no theorem.
Limits. The full size alone. Whether `LaidAt` and hr can be met at the release's own files is not
shown here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AlikeFull
import Johnson.HB.LLHARD.RadiiInScope
import Johnson.P5T.CoreAtMg
import Johnson.Desc.ProofFile.Law.CarryAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (msOf seatOf Alike)
open VerifiableInference.Desc.LinkJoin (rad_in_scope)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- The written first chain has 82 sendings. -/
theorem sends_82 : Johnson.G.proofSendsFull.1.sends.length = 82 := by decide +kernel

/-- **The letters' radii are the written ones.** -/
theorem rad_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {R : List Johnson.G.SendRow}
    (hr : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) : P5J.At.rad Zp Z.lay = radW := by
  funext k i
  obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files L.pub
  unfold P5J.At.rad P5T.radOf P5T.rowsAt? radW
  rw [e1, e2, hr]
  show (P5T.rad? R k i).getD 0 = _
  rw [rad_in_scope hW L.pub (P5J.pins_of_laid hW L).1 hr k i]

/-- **THE COMPOSED MEANING's MEMBERS ARE THE WRITTEN LISTS'.** -/
theorem ms_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {R : List Johnson.G.SendRow}
    (hr : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) : P5J.At.ms Zp Z.lay = msOf mlFull := by
  unfold P5J.At.ms P5T.msAtR mlFull
  rw [rad_at_laid hW L hr, L.seats hW, sends_in_scope hW L.pub (P5J.pins_of_laid hW L).1, sends_82]

/-- A link's group at the letters' numbers is the written numbers'. -/
theorem group_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (l : ℕ) :
    (P5J.At.N Zp cF).group l = P5T.N0Full.group l := by
  unfold VerifiableInference.Desc.First.Numbers.group
  rw [(L.N_core hW).1]

/-- The first sentence at whatever is equal to the written values. -/
theorem alike_gen (l : ℕ) (hl : l < 26) {ms : List VerifiableInference.Desc.Sound.Mem}
    {own : List (ℕ × ℕ)} {ps : List P5T.PSeat} (h1 : ms = msOf mlFull)
    (h2 : own = P5T.N0Full.group l) (h3 : ps = P5T.psFull) :
    ∀ x ∈ ms, seatOf x ∈ own →
      ∃ i : Fin (Johnson.G.linksFullLit.getD l []).length,
        Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
          seatK10 (Johnson.G.linksFullLit.getD l []) ps l⟩, i⟩ := by
  subst h1 h2 h3
  exact alike_full l hl

/-- The second. -/
theorem hit_gen (l : ℕ) (hl : l < 26) {ms : List VerifiableInference.Desc.Sound.Mem}
    {ps : List P5T.PSeat} (h1 : ms = msOf mlFull) (h3 : ps = P5T.psFull) :
    ∀ i : Fin (Johnson.G.linksFullLit.getD l []).length, ∃ x ∈ ms,
      Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
        seatK10 (Johnson.G.linksFullLit.getD l []) ps l⟩, i⟩ := by
  subst h1 h3
  exact hit_full l hl

/-- **THE FIRST SENTENCE AT THE LETTERS.** -/
theorem alike_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {R : List Johnson.G.SendRow}
    (hr : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) (l : ℕ) (hl : l < 26) :
    ∀ x ∈ P5J.At.ms Zp Z.lay, seatOf x ∈ (P5J.At.N Zp cF).group l →
      ∃ i : Fin (Johnson.G.linksFullLit.getD l []).length,
        Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
          seatK10 (Johnson.G.linksFullLit.getD l []) (P5J.At.pseats Zp) l⟩, i⟩ :=
  alike_gen l hl (ms_at_laid hW L hr) (group_at_laid hW L l) (L.seats hW)

/-- **THE SECOND.** -/
theorem hit_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {R : List Johnson.G.SendRow}
    (hr : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) (l : ℕ) (hl : l < 26) :
    ∀ i : Fin (Johnson.G.linksFullLit.getD l []).length, ∃ x ∈ P5J.At.ms Zp Z.lay,
      Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
        seatK10 (Johnson.G.linksFullLit.getD l []) (P5J.At.pseats Zp) l⟩, i⟩ :=
  hit_gen l hl (ms_at_laid hW L hr) (L.seats hW)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.sends_82
#print axioms VerifiableInference.Desc.First.Close.rad_at_laid
#print axioms VerifiableInference.Desc.First.Close.ms_at_laid
#print axioms VerifiableInference.Desc.First.Close.group_at_laid
#print axioms VerifiableInference.Desc.First.Close.alike_gen
#print axioms VerifiableInference.Desc.First.Close.hit_gen
#print axioms VerifiableInference.Desc.First.Close.alike_at_laid
#print axioms VerifiableInference.Desc.First.Close.hit_at_laid
