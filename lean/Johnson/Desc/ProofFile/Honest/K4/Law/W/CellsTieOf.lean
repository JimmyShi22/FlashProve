-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellsTieOf.lean: CONDITIONAL.

Not shown here. THAT THE MATRICES OFF THE DATA ARE THE IMAGES OF ANY LIST: hM is a hypothesis
(`mats_of_list`, Johnson/Road/K4/W/MatsOfList.lean, has it where the data's symbols are that list's
packing). THAT THE HONEST SIDE's CELL IS THAT LIST's ENTRY: `CellIsList` is a hypothesis on the
reader `cells` of the trace; asked at every continuation (hc), its left side reads no continuation:
so it forces the list to stand still inside the sizes, off the matrix of the planes, as elements of
the field. The data read 0 where no seat is listed for an array: that the seats are there is shown
here of no list. Of the two together no example is known. General in the thread and in the sizes.
Nothing on soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 2 under Johnson/Bridge/; it saw no module whose name holds RecCompile, none under
Johnson/Goal/, Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of the three names.
What lies behind the 2 is not counted: all the numbers are floors.

The hypothesis `K4CellsTieAt` (Law/ScriptAt.lean: the honest side's cell is the cell that the item's
sentence reads off the witness, at a stand in front of the member of the feed-forward layers' own
rounds, sub-protocol K4) from one sentence on the matrices off the data (they are the images of a
list L of integer matrices) and one on the honest side's reader. A definition, and one statement
with its proof: a rewriting.

  `CellIsList Q w L tl`   inside the plan's sizes, off the matrix of the lookup's planes: the image
      of the honest side's cell is the image of L's entry.
  `cellsTie_of_mats`   **`K4CellsTieAt`**, where at every open segment's part and every continuation
      of the challenges heard the matrices off the data are the images of L, and `CellIsList`.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ScriptAt
import Johnson.Road.K4.W.MatsOfList

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Reading)
open OnBytes.Road (Mats)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData)
open OnBytes.Road.Rows.Norms (castM)

/-- **The honest side's cell is the list's entry**, inside the plan's sizes, off the matrix of the
lookup's planes. w: the honest side's small input. This defines a hypothesis; the definition claims
nothing. -/
def CellIsList (Q : K4Pub) (w : K4In) (L : Mats ℤ) (tl : HTailF2) : Prop :=
  ∀ i r c, i < tl.NM → i ≠ (OnBytes.Model.Layer.matIx Q.P.y).iB →
    r < (tl.mats.getD i {}).m → c < (tl.mats.getD i {}).k →
      Reading.gl.val (OnBytes.ofF (w.cell i r c)) = ((L i r c : ℤ) : GQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {tl : HTailF2}
  {names : Array (Nat × String)} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X}

/-- **`K4CellsTieAt` WHERE THE MATRICES OFF THE DATA ARE THE IMAGES OF A LIST.** L: the list, which
may hang on the continuation. CONDITIONAL: on hM and hc. -/
theorem cellsTie_of_mats {L : List Fmt.Drawn → Mats ℤ}
    (hM : ∀ a, segAt? s = some a → ∀ ds,
      matsOfData tl names (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))) =
        castM (L ds))
    (hc : ∀ ds, CellIsList Q (k4Wit Q cells weights tokens (look Q) m.st.input) (L ds) tl) :
    K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m := by
  intro a ha ds i r c h1 h2 h3 h4
  rw [hM a ha ds]
  exact hc ds i r c h1 h2 h3 h4

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.cellsTie_of_mats
