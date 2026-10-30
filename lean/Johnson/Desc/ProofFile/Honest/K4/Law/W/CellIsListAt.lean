-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellIsListAt.lean: CONDITIONAL: IT MOVES A DEBT ON
THE SCRIPT AND THE TRACE; TWO PUBLIC PREMISES OF THE LAW BENEATH IT (hShape, hOwn) ARE PAID INSIDE.
AT EACH OF THE TWELVE GROUPS.

What is here. THE STONES OF THE BRIDGE JOINED: THE HYPOTHESIS `CellIsList` (Law/W/CellsTieOf.lean)
OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), AT A SCRIPT's WITNESS, at every input that
meets Vd and every list of at least N challenges, from: another house's premise's form «the script
lays the filling off the planes» (`LaysCells`, Honest/K5/Law/LaysCells.lean) at K4's own segment (L)
and, from the second group on, at the segment of the group before (L'); that the trace's cells are
small (hS: `K4CellsSmall`, Law/W/CellsOfSyms.lean); that the frame's reader of the cells is the
lot's (hrd); and public premises. One statement; its proof is five calls: `cellIsList_of_raw`
(Law/W/CellsOfSyms.lean) at `symsRoom_k4_all` (Law/W/SymsRoomK4.lean) and at `k4SymsRaw_all`
(Law/W/SymsOfLaysCells.lean), the last at `k4_shape_at_plan` (Law/W/ShapeK4.lean) and `k4Owner_at`
(Law/W/OwnerKeyK4.lean).

  `cellIsList_at`   **`CellIsList` at the script's witness, at each group.**

Not shown here. L, L': shown of no script here. ON L AND L': they are premises on what the script
holds of the private input: NOT IN FRONT OF A LAW OVER COINS.
Laws that end in this form at the Script joined
of K1's and K2's lots are no part of this library.
That the joined script is the honest prover's
is said nowhere.
hS: shown of no trace here;
Law/W/CellsSmallFullIn.lean, not imported here, has it at the frame's full-size choice of fields.
hrd: a premise here. hSz: Honest/K5/Law/SizesOffPlanes.lean
says where it is met. hQ: Qp is what `k4PubOf` returns at the member's parameters. h: the
library's hypothesis `P5J.AtMgA` on the public files; Lh and hx follow from it, as
Law/W/MatsAreHead.lean's head says. AT A Vd THAT HOLDS OF NO INPUT IT IS IDLE; N IS A FREE
LETTER. NOT TRIED FOR EMPTINESS: no instance of the premises together is exhibited. All limits of
the heads of the files that it imports hold here; among them: closed facts by evaluation in
Lean's kernel lie beneath; no independent checker that its writers know of has replayed them;
through its imports it stands over files under Johnson/Goal/. THE FULL SIZE ALONE, and the
format's second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one. Nothing on soundness, on completeness or on any
other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SymsOfLaysCells
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SymsRoomK4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OwnerKeyK4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ShapeK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.HonestTrace (Sz)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.K5 (LaysCells planesAtRef)
open ProofFile.Honest.FirstThread (Script)
open P5J (AtMgA TS CellsM)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- CONDITIONAL: on every hypothesis named; the head says of each what it is. **`CellIsList` AT THE
SCRIPT's WITNESS, AT EACH GROUP.** It moves the debt. -/
theorem cellIsList_at {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat seat' : MsgAddr → Option (ℕ × ℕ)} {heard heard' : MsgAddr → ℕ}
    (L : LaysCells h Q S Vd N rd seat heard (2 * g))
    (L' : g ≠ 0 → LaysCells h Q S Vd N rd seat' heard' (2 * (g - 1))) {cells : Tr → Cells}
    (hrd : ∀ v, (rd v).cells = cells v.trace) {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (hS : K4CellsSmall Vd x.2.hp.tl Qp cells weights tokens look)
    (kk : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn) (hv : Vd v)
    (hN : N ≤ hd.length) :
    CellIsList Qp (k4Wit Qp cells weights tokens (look Qp) v)
      ((h.𝔇.H.hid (Q.wit kk v hd)).MG g) x.2.hp.tl :=
  cellIsList_of_raw Lh hx (symsRoom_k4_all h Lh hx Qp) hS
    (k4SymsRaw_all Lh hx hQ hSz L L' hrd weights tokens look (k4_shape_at_plan h Lh hx)
      fun _ _ hμ => k4Owner_at h Lh hQ hμ) kk v hd hv hN

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.cellIsList_at
