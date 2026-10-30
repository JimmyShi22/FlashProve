-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsAt.lean: the lookup on the digits of a segment's approximate range
proof: WHAT THE ITEM constr l lookDigits GIVES ITS SPENDER AT THE COMPOSED MEANING mgAll Dm Mg
(Johnson/Desc/Sound/MgAll.lean): the approximate range proof's
law's own sentence DigitsAt (Johnson/Desc/First/K8/LawItems.lean) at that law's one table of cells
cellsAhead (K8/CellsAhead.lean). One theorem: a joining. NO RESULT ON THE PROTOCOL.

Main name.
  digitsAt_mgAll: (mgAll Dm Mg).constr l .lookDigits (z, s) y w → K8.DigitsAt (K8.cellsAhead Dm.cs
    Dm.arr Dm.ms Dm.N l (z, s)) s w.
HOW. digPart_mgAll (MgAt/K3At.lean): the item is the lookups' sentence · digitsOf_of_part
(K3DigitsOfAt.lean): that sentence gives DigitsOf at the plan's parameters tl and the lookup's
reading digMu · digitsOf_cells (K3DigitsOfCongr.lean) with hE: at cellsAhead · hT: at the state's
own parameters.
WHAT IS LEFT, EACH BOOKED.
  THE PUBLIC PARAMETERS: hX (they are publicOf's) · hx (the digits' place).
  A TERM OF THE PARAMETERS: hD (Dm.digitsPart is the lookups' sentence).
  ON THE STATE, LEFT TO THE APPROXIMATE RANGE PROOF's FILES: hT (the state holds parameters ts
    at which DigitsOf follows from DigitsOf at the plan's tl: by digitsOf_six where NM, tau, mats,
    ix.ZZ, mz, off agree).
  ON THE STATE AND THE WITNESS: hE (the two readings are one AT THE CELLS THAT THE SENTENCE READS,
    and at no other): by digMu_cellsAhead under DigAheadOk (K3DigitsAhead.lean).
OBJECT. One term of the type Meaning; two sentences on a witness.
Used by DigitsAtDraw.lean (Johnson/P1K8R/).
LETTERS. Dm, Mg; l, x, tl; z, s, y, w.


Compiled with the whole library.
Limits. A rule over letters. hT and hE are shown at no state. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.First.Look.K3DigitsOfAt
import Johnson.Desc.First.Look.K3DigitsOfCongr
import Johnson.Desc.First.K8.CellsAhead
import Johnson.Desc.First.K8.LawItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **«THE DIGITS ARE IN THEIR TABLES» AT THE COMPOSED MEANING.** -/
theorem digitsAt_mgAll {pol KL : ByteArray} {layout : Option ByteArray}
    (hX : Verify.publicOf pol KL layout = .ok X)
    (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3) {l : ℕ} {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit (CellsQ rows cols) Tok MsgT)
    (hT : ∃ ts, s.tl? = some ts ∧
      ∀ A, Desc.First.K8.DigitsOf tl A → Desc.First.K8.DigitsOf ts A)
    (hE : ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      digMu x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1) Dm.l3.arr w
          (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i)) =
        Desc.First.K8.cellsAhead Dm.cs Dm.arr Dm.ms Dm.N l (z, s) w tl.ix.ZZ u
          ((tl.zzCol μ b 0).getD 0 + i)) :
    (mgAll Dm Mg).constr l .lookDigits (z, s) y w →
      Desc.First.K8.DigitsAt (Desc.First.K8.cellsAhead Dm.cs Dm.arr Dm.ms Dm.N l (z, s)) s w := by
  intro hc
  rw [digPart_mgAll Dm Mg hD l (z, s) y w] at hc
  obtain ⟨-, H⟩ := digitsOf_of_part hX Dm.sent Dm.l3 hx (z, s) y w hc
  obtain ⟨ts, hts, hT'⟩ := hT
  exact ⟨ts, hts, hT' _ (digitsOf_cells tl _
    (Desc.First.K8.cellsAhead Dm.cs Dm.arr Dm.ms Dm.N l (z, s) w)
    (fun μ hμ u hu i hi b hb => hE μ hμ u hu i hi b hb) H)⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digitsAt_mgAll
