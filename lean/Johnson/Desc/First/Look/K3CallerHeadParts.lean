-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
head_lookCalls, head_parts, head_means_at: that their premises can be met
together is shown at no record.
Johnson/Desc/First/Look/K3CallerHeadParts.lean: FROM THE JOINT IN FRONT OF THE LOOKUP ON THE HEAD's
LINK's CALLS, AT THE CALLER OF K3CallerHead.lean, TO FOUR OF THE SIX FIELDS OF K6's
RECORD HeadParts (lookCalls · rider · small · smallS), and with the two others as premises to what
that kind's head_means concludes: the head's and the final normalization's meaning in integers.
Statements and proofs. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

OBJECT: no text that runs: the joint in front of the library's lookup block at K3CallerHead.lean's
  caller.
USER: Johnson/Desc/First/Look/K3CallerHeadTests.lean.
LETTERS: those of K3CallerHead.lean; sT.
Compiled with the whole library.




Why. K6 has cut its relation on cells in four parts (Johnson/Desc/Kinds/HeadTablesLaw.lean:
HeadParts: idnSums | idnRows · lookCalls · rider · small | smallS) and proved that they mean Says ∧
SaysN (Law/TableTie.lean: head_means); and it has tied the tables (tie_law): where its test rowsOk
passes on the rows AS NUMBERS, a place of a call's table that is read as a row's number is a row in
its own sense InTable. The rows' numbers are the verifier's record's own: row c u := FoNums.tauN h c
u: the term to which the proved block's joint in front unfolds.

Main names:
  `rowH x`: the rows of the record's calls' tables, as numbers.
  `HeadTabs x sT`: premises on public data: K6's planOk and rowsOk at these rows; each call's k
    is K6's bitsOf.
  `head_lookCalls`: HeadParts.lookCalls at tab := tabOf (rowH x), at the token that was heard.
  `head_parts`: HeadParts, from the joint in front and the two fields that are not the lookup's.
  `head_means_at`: so: Says ∧ SaysN of the cells off the messages.
Limits. Those of K3CallerHead.lean: above all: small | smallS AND THE WEIGHTS' BOUND HOLD BY THE
CELLS' MAKE AND SAY NOTHING; adr is a letter; on what has been evaluated of HeadOK and HeadTabs see
that file's Limits. idnSums and idnRows are premises: other kinds' and the batching's matter. K6's
files are imported as this library has them. Says | SaysN speak of the cells cellsH, not
of a model's run: that these cells are what the earlier links hand on is the seams' matter.
Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerHead
import Johnson.Desc.Kinds.Law.TableTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE OracleShape)
open OnBytes.Model (HTailF2)
open Norm (lt ls d S2 T)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look

/-- The rows of the record's calls' tables, as numbers. -/
def rowH (x : First.Look.Place) : ℕ → ℕ → ℕ := fun c u => FoNums.tauN x.fs c u

variable [Sizes] [Policy] [Request]

/-- **What is asked of the public data for the tables.** -/
structure HeadTabs (x : First.Look.Place) (sT : ℕ) : Prop where
  /-- K6's tests on the plan -/
  plan : planOk sT = true
  /-- K6's test on the rows -/
  rows : rowsOk (rowH x) = true
  /-- each call's table has K6's number of rows -/
  bits : ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c

section
variable {set : OnBytes.Params.Setting} {adr : HeadAdr} {x : First.Look.Place} {floor sT : ℕ}
  {tl : HTailF2} {D : Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ} (Ex : Iop.ExtSpec) (Wp : Type)

/-- **HeadParts.lookCalls**, at the token that was heard. -/
theorem head_lookCalls (H : HeadOK set x floor) (HT : HeadTabs x sT) (a : ℕ × Ex.Str)
    (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).A
      (headRider adr x tl D rad oW wOf nr nc Ex Wp)).relR a w) :
    letI : Token := ⟨a.1⟩
    ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable (tabOf (rowH x)) call
        (keyTable (headCells adr x tl D rad oW wOf nr nc w.1) call col t) := by
  letI : Token := ⟨a.1⟩
  intro call hc col hcol t ht
  obtain ⟨u, hu, e⟩ := head_rows Ex Wp H a w h call hc col hcol t ht
  rw [HT.bits call hc] at hu
  exact Came.tie_law sT (rowH x) _ HT.plan HT.rows call hc col t u hu e

/-- **HeadParts**, from the joint in front and the two fields that are not the lookup's. -/
theorem head_parts (H : HeadOK set x floor) (HT : HeadTabs x sT) (a : ℕ × Ex.Str)
    (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).A
      (headRider adr x tl D rad oW wOf nr nc Ex Wp)).relR a w) :
    letI : Token := ⟨a.1⟩
    (meanAt (headCells adr x tl D rad oW wOf nr nc w.1).toCells = 0 ∧
      countAt (headCells adr x tl D rad oW wOf nr nc w.1).toCells = 0) →
    (∀ t, t < T → ∀ v, v ∈ rowsAt (headCells adr x tl D rad oW wOf nr nc w.1) (bits lt t) →
      v = 0) →
    HeadParts floor (tabOf (rowH x)) (headCells adr x tl D rad oW wOf nr nc w.1) := by
  letI : Token := ⟨a.1⟩
  intro hS hR
  have hs := cellsH_small adr (msgLay x tl D rad oW wOf nr nc w.1)
  exact ⟨hS, hR, head_lookCalls Ex Wp H HT a w h, head_guests Ex Wp a w h, hs.1, hs.2.1⟩

/-- **SO: what K6's head_means concludes**, of the cells off the messages, at the token that was
heard. -/
theorem head_means_at (H : HeadOK set x floor) (HT : HeadTabs x sT) (a : ℕ × Ex.Str)
    (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).A
      (headRider adr x tl D rad oW wOf nr nc Ex Wp)).relR a w) (hreq : Request.ok = true)
    (hy : a.1 < V) :
    letI : Token := ⟨a.1⟩
    (meanAt (headCells adr x tl D rad oW wOf nr nc w.1).toCells = 0 ∧
      countAt (headCells adr x tl D rad oW wOf nr nc w.1).toCells = 0) →
    (∀ t, t < T → ∀ v, v ∈ rowsAt (headCells adr x tl D rad oW wOf nr nc w.1) (bits lt t) →
      v = 0) →
    Says (headCells adr x tl D rad oW wOf nr nc w.1).toCells ∧
      SaysN (headCells adr x tl D rad oW wOf nr nc w.1) := by
  letI : Token := ⟨a.1⟩
  intro hS hR
  exact Came.head_means sT floor (tabOf (rowH x)) _ HT.plan hreq hy
    (Came.tables_law (rowH x) HT.rows).1
    (cellsH_small adr (msgLay x tl D rad oW wOf nr nc w.1)).2.2
    (head_parts Ex Wp H HT a w h hS hR)

end

#print axioms head_lookCalls
#print axioms head_parts
#print axioms head_means_at

end VerifiableInference.Desc.Kinds.Head.Law
