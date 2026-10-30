-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/AtF2.lean: **THE LAW OF THE PROXIMITY TEST AT THE FIRST CHAIN's FINISH OF A
DESCRIPTION.** One statement and its proof: three calls.

For a description F with data (F.data file = .ok D) whose first chain's declared rounds are
pre ++ ((proximityTestKind guardedProximityTestParts π).rounds ++ (post ++ [r₀])): the piece `pieceF2` (the seat `atFinish π` on
the first chain's own state) over the frame of D, at the stretch in closed form, has the plain law
(`Reduction.Leads`):

  promise, at the record that the door lays (`recAt`): the record's count of roots is the number of
    roots declared in front (rootsOf pre); `FirstOpens`; `PayRec` (the test `combineAt` behind the
    batching's beginning);
  conclusion: the chain's state stood at its finish, nothing waited, nothing had failed; `QN` at
    `NTuple`: one witness within the radius of the group's word, of whose own words all batched rows
    hold, and whose parts are candidates at each sampled member; and of the chain's state only the
    running record, the book and the count of roots turn.
By `atPlace_first` (AtDesc.lean), `k12_lawRecFree` (FreeOff.lean), `leads_atFinish` (SeatF2.lean).
What is left as a premise: on the plan: early; answers = 1; planOk; spendOk; ownMask = false; the
written rounds exist; johOk at the radii; batOneOk. On numbers: `CodesAt`, `bears`. On the
description: the parting of the declared rounds; that the stretch's data are written dB :: dt.
Limits. NO SOUNDNESS IS CLAIMED. No member of the premises or of the promise is shown. That the
first error is small is not shown here. key and ft are free letters: at others than the chain's own
the piece refuses and the law is idle. Where a chain declares the same run of rounds twice, pre is
not fixed by the parting alone. That the tiling's piece at this block is this piece is another
file's.
-/
import Johnson.Desc.K12.Coin.AtDesc
import Johnson.Desc.K12.Coin.FreeOff
import Johnson.Desc.K12.Coin.SeatF2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK (recAt)
open H2K.Pin (NTuple PayRec)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk johOk batV0)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)

theorem k12_F2_at {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (W : Type) (π : P12) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (pre post : List Fmt.DeclaredRound)
    (r₀ : Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])))
    (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hcons : dB :: dt =
      (D.ds₁.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages) (ho : π.nums.ownMask = false) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt)
    (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true)
    (hb1 : batOneOk π = true) :
    (pieceF2 (frameAt D (allOf D) key ft) W π (0 + nTrees (D.ds₁.take pre.length)) dB dt
        (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → (recAt x.1 fo).roots = rootsOf pre ∧
        (FirstOpens π (numAt F.t₁ F.t₂ 0) no (0 + nTrees (D.ds₁.take pre.length)) (recAt x.1 fo) ∧
          PayRec π (recAt x.1 fo)))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        QN π (NTuple (frameAt D (allOf D) key ft) π no rad rd) (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (pieceF2 (frameAt D (allOf D) key ft) W π (0 + nTrees (D.ds₁.take pre.length)) dB dt
        (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt).err :=
  leads_atFinish _ W π _ dB dt _ εt _ _
    (k12_lawRecFree _ W π _ no L mC mS mW rad rd _ dB dt εt (rootsOf pre) early planOk
      (fun hfree => atPlace_first F file D h key ft π L mC mS mW rad pre post r₀ e dB dt εt hcons
        hfree early answers planOk spend codes ho w0 l hw bears) r hr hj hb1)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_F2_at
