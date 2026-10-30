-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LinkZeroFive.lean (kind K10): LINK 0's LIST WITHOUT ITS ONE MESSAGE
WITHOUT A MAIN ROW, AS A TERM, WITH THE CLOSED FACTS THAT K10's LAW WANTS OF IT. Definitions,
statements and proofs; evaluations by the kernel.

Why. At link 0 the written list has six messages, the group five: the index masks' message has no
main row. K10's law over the signature of the six asks a witness for that message's word, which the
table's relation behind the closing does not hold and, by the table's own text, need not.
GroupSub.lean, beside this file, has the typed group and the law at any list whose entries stand on
written lists.
  `loSix`: the first written list. `loFive`: its messages with a main row. `kbSix`, `kbFive`: the
    flags of link 0 of the written shape at the two lists (`kbAt`, ReqKept.lean: the joiners' flags,
    dealt to the messages with a main row in order).
  `loFive_written`: `Written loFive`. `five_length`, `six_length`: 5 and 6. `five_allMain`: every
    message of `loFive` has a main row; `six_notAllMain`: A NEGATIVE LINE: not every message of
    `loSix` has.
  THE TWO LISTS HAVE ONE GROUP: `five_entries`: the members' entries (shape, radius), in order, are
    the same; `five_flags`: so are their flags; `five_cornersM`, `five_cornersZ`: so are their first
    rows by the program's own layout; `five_kLay`: so is the number of row variables.
  `five_corners`: the test on the corners says yes at `loFive`, `kbFive`, at that number of row
    variables; `five_corners_tight`: A NEGATIVE LINE: at one row variable fewer it says no.
    `five_layout`: `LayoutAgrees loFive kbFive` (the program's `Statement.layout` says what
    Corners.lean's definitions say). `five_corners_at`: the test at gs.k, for a group in front with
    gs.k = kLay of THE SIX: the form in which the seated piece's number comes.
Limits. Closed facts on written values. THE LAW AT `groupSub loFive ..` IS NOT CALLED HERE. Nothing
on a verifier's state. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.GroupSub
import Johnson.Desc.First.Close.Law.ReqKept
import Johnson.Desc.First.Close.Law.LayoutDrawn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.ReqLit

/-- The first written list of the full size. -/
def loSix : List (OracleShape × ℕ) := linksFullLit.getD 0 []

/-- Its messages with a main row. -/
def loFive : List (OracleShape × ℕ) := loSix.filter fun x => x.1.mainRows != 0

/-- The flags of link 0 at the two lists. -/
def kbSix : Fin loSix.length → Bool := kbAt shapeFull 0 loSix

def kbFive : Fin loFive.length → Bool := kbAt shapeFull 0 loFive

theorem loSix_mem : loSix ∈ linksFullLit := by decide +kernel

theorem loFive_written : Written loFive := written_filter (written_of_mem loSix_mem) _

theorem five_length : loFive.length = 5 := by decide +kernel

theorem six_length : loSix.length = 6 := by decide +kernel

theorem five_allMain : ∀ i : Fin loFive.length, memMain loFive i := by decide +kernel

/-- A negative line. -/
theorem six_notAllMain : ¬ ∀ i : Fin loSix.length, memMain loSix i := by decide +kernel

theorem five_entries :
    (membersOf loFive).map (fun i => loFive.get i) =
      (membersOf loSix).map fun i => loSix.get i := by decide +kernel

theorem five_flags : (membersOf loFive).map kbFive = (membersOf loSix).map kbSix := by
  decide +kernel

theorem five_cornersM :
    (membersOf loFive).map (fun i => layAt (sizesM loFive kbFive) i.val) =
      (membersOf loSix).map fun i => layAt (sizesM loSix kbSix) i.val := by decide +kernel

theorem five_cornersZ :
    (membersOf loFive).map (fun i => layAt (sizesZ loFive) i.val) =
      (membersOf loSix).map fun i => layAt (sizesZ loSix) i.val := by decide +kernel

theorem five_kLay : kLay loFive kbFive = kLay loSix kbSix := by decide +kernel

theorem five_corners :
    Corners loFive (kLay loFive kbFive) (fun i => layAt (sizesM loFive kbFive) i.val)
      (fun i => layAt (sizesZ loFive) i.val) kbFive := by decide +kernel

/-- A negative line: one row variable fewer. -/
theorem five_corners_tight :
    ¬ Corners loFive (kLay loFive kbFive - 1) (fun i => layAt (sizesM loFive kbFive) i.val)
      (fun i => layAt (sizesZ loFive) i.val) kbFive := by decide +kernel

theorem five_layout : LayoutAgrees loFive kbFive := by decide +kernel

/-- The test at the number of row variables of a group in front that fits THE SIX. -/
theorem five_corners_at (gs : GroupSize) (hk : gs.k = kLay loSix kbSix) :
    Corners loFive gs.k (fun i => layAt (sizesM loFive kbFive) i.val)
      (fun i => layAt (sizesZ loFive) i.val) kbFive := by
  rw [hk, ← five_kLay]
  exact five_corners

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.loSix_mem
#print axioms VerifiableInference.Desc.First.Close.loFive_written
#print axioms VerifiableInference.Desc.First.Close.five_length
#print axioms VerifiableInference.Desc.First.Close.six_length
#print axioms VerifiableInference.Desc.First.Close.five_allMain
#print axioms VerifiableInference.Desc.First.Close.six_notAllMain
#print axioms VerifiableInference.Desc.First.Close.five_entries
#print axioms VerifiableInference.Desc.First.Close.five_flags
#print axioms VerifiableInference.Desc.First.Close.five_cornersM
#print axioms VerifiableInference.Desc.First.Close.five_cornersZ
#print axioms VerifiableInference.Desc.First.Close.five_kLay
#print axioms VerifiableInference.Desc.First.Close.five_corners
#print axioms VerifiableInference.Desc.First.Close.five_corners_tight
#print axioms VerifiableInference.Desc.First.Close.five_layout
#print axioms VerifiableInference.Desc.First.Close.five_corners_at
