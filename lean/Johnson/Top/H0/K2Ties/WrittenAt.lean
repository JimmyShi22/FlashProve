-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/WrittenAt.lean: the code switch's law at the closed constant: THE
TIES FROM THE WRITTEN VALUES TO THE CONSTANT's OWN PARAMETERS, AT THE CONSTANT's OWN NAMES, IN ONE
THEOREM: so that what Lean's kernel has shown at the written values can be spent at the constant.
  AtWritten    a structure of seventeen equations at P5J.At's names (Johnson/P5J/LettersAt.lean):
               the first chain's codes, the request's shape and the layout are the
               written ones (proofSizedFull.codes · proofSizedFull.request · layoutFull) · the
               plan's seats of the first chain and of all three chains are psFull and seatsAllFull ·
               so are what is made of them: seats · arr · num · the listed shapes of the first
               chain's messages are MW · EACH WRITTEN ENTRY OF THE CODE SWITCH's TABLE HAS THE
               CONSTANT's CODES (rowCs) · of the table's numbers At.N Zp cF: sent · keptOf · index ·
               w · inside · group are N0Full's; groupAt is the identity
  at_written   IT HOLDS IN SCOPE, WHERE THE VALUE IS LAID (LaidAt) AND THE PIN madePinnedAt
               ACCEPTS
  AtWritten.csW  the first two at FrontsFull.lean's names csW | shW (definitions of the same)
  smp_named    the constant's reader of OOD samples is the named one at its own codes and seats
CALLED: first_written_in_scope (Goal/Numbers/MadeInScope.lean) and
seats_in_scope (P5T/PlanSeatsTie.lean) · written_in_scope
(K2Hands/WrittenInScope.lean: at Z.first | Z.made) · N_sent_of | N_keptOf_of
| N_index_of | N_w_of | N_inside_of | N_group_of (P5J/NAtReaders.lean) · LPFD.Full.laidPOf_of. NOT
IN IT. At.N's indexNo · treesAt · msgsAt · rowsAt: these are laid off what the first chain's
sub-protocols tell and declare (withTold | withRows): they want «toldOf cF.blocksInOrder is the written
list»: another tie · «the typed structure at place m is tableFullLit[m]»: it hangs on the second
reading of the three public files.
LIMITS. A join. UNDER THE PIN madePinnedAt, which follows in scope from the accept of row 9 of the
proof file's entry tests (LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean), by P5J.pins_of_laid. That
the premises can be met together is not shown here. No soundness is claimed.
-/
import Johnson.P5J.LaidOpens
import Johnson.P5J.NAtReaders
import Johnson.P5T.PlanSeatsTie
import Johnson.Top.H0.K2Hands.WrittenInScope
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.First.K2Hands (csW shW MW written_in_scope)
open P5T (psFull seatsAllFull N0Full seats_in_scope)
open P5J (LaidAt TS)

/-- **THE CLOSED CONSTANT's OWN PARAMETERS ARE THE WRITTEN VALUES.** -/
structure AtWritten (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) : Prop where
  cs : P5J.At.cs Zp = proofSizedFull.codes
  shape : P5J.At.shape Zp = proofSizedFull.request
  layout : P5J.At.layout Zp = Johnson.G.layoutFull
  pseats : P5J.At.pseats Zp = psFull
  pseatsAll : P5J.At.pseatsAll Zp = seatsAllFull
  seats : P5J.At.seats Zp = psFull.map fun p => (p.j, p.t)
  arr : P5J.At.arr Zp = P5T.arrOf seatsAllFull
  num : P5J.At.num Zp = P5T.numOfPlan seatsAllFull
  msgs : K12.Door.msgsOfChain Zp.made.proof.1 = MW
  rowCs : ∀ (m : ℕ) (r : SwRow), tableFullLit[m]? = some r → r.cs = P5J.At.cs Zp
  sent : (P5J.At.N Zp cF).sent = N0Full.sent
  keptOf : (P5J.At.N Zp cF).keptOf = N0Full.keptOf
  index : (P5J.At.N Zp cF).index = N0Full.index
  w : (P5J.At.N Zp cF).w = N0Full.w
  inside : (P5J.At.N Zp cF).inside = N0Full.inside
  group : ∀ l, (P5J.At.N Zp cF).group l = N0Full.group l
  groupAt : (P5J.At.N Zp cF).groupAt = id

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **IN SCOPE, WHERE THE VALUE IS LAID AND THE PIN ACCEPTS.** -/
theorem at_written (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) : AtWritten Zp cF := by
  have hl := LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks
  obtain ⟨hps, hall, -⟩ := seats_in_scope hZ L.pub hy hl
  have f := first_written_in_scope hZ L.pub hy
  obtain ⟨-, -, hm, hr⟩ := written_in_scope hZ L.pub hy
  have hp : P5J.At.pseats Zp = psFull := hps
  have ha : P5J.At.pseatsAll Zp = seatsAllFull := hall
  exact
    { cs := f.1
      shape := f.2.2.1
      layout := f.2.2.2.2.2
      pseats := hp
      pseatsAll := ha
      seats := by unfold P5J.At.seats; rw [hp]
      arr := by unfold P5J.At.arr; rw [ha]
      num := by unfold P5J.At.num; rw [ha]
      msgs := hm
      rowCs := hr
      sent := funext fun l => funext fun k => P5J.At.N_sent_of Zp cF hp l k
      keptOf := funext fun l => P5J.At.N_keptOf_of Zp cF hp l
      index := P5J.At.N_index_of Zp cF hp
      w := P5J.At.N_w_of Zp cF hp
      inside := P5J.At.N_inside_of Zp cF hp
      group := fun l => P5J.At.N_group_of Zp cF hp l
      groupAt := rfl }

/-- The same at K2Hands/FrontsFull.lean's names for the written codes and shape. -/
theorem AtWritten.csW {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (h : AtWritten Zp cF) :
    P5J.At.cs Zp = csW ∧ P5J.At.shape Zp = shW := ⟨h.cs, h.shape⟩

/-- The constant's reader of OOD samples is the named one at its own codes and seats. -/
theorem smp_named (Zp : ProofFile.Pub) :
    P5J.At.smp Zp = VerifiableInference.Desc.Sound.smpNamed (P5J.At.cs Zp) (P5J.At.seats Zp) := rfl

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.at_written
#print axioms VerifiableInference.Desc.First.K2Ties.AtWritten.csW
#print axioms VerifiableInference.Desc.First.K2Ties.smp_named
