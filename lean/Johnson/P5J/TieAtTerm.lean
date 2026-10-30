-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TieAtTerm.lean: THE FACTS ON A START (TieStart, Johnson/P5J/TieStart.lean: eleven of the proof file's rows, none a law of a kind of block) AT THE SEATED DESCRIPTION's OWN TERM, One theorem, one term whose type is what Lean infers. A joint build of several files.

  dtK_reads_first: the first table's decoder at the term reads the pair's FIRST part alone (the public part): x'.1 = x.1 → dtK … c x' = dtK … c x: by its make (the shared chain's decoder at start₂ of the public part): what a kind's "the decoding rides past my block" asks of the decoder.
  tieStart_at_term: UNDER hpub (ProofFile.pubPlain o pol lay' KL = .ok Zp): TieStart.mk AT F₀ := F0T … · instP := the seated map · getS := the identity · reqB | asked | DT := Johnson/P5J/AtTerm.lean's · codes := the first chain's codes · rq := the request's words: FILLED: start_is_the_requests · requests_to_instances (three conjuncts) · fin_is_canonical; ARGUMENTS, in the structure's order: scope_reads ·
    scope_public · front_place_first · start_in_order · start_public_items · start_public_sentences · front_no_trees · front_no_messages.
  (The rule's premise "tie" at the term is then tie_of_start at this value: assembled in the tower's files, not here.)

Limits. The full size alone. The eight that are left: two are the scope's own; one is a kernel's evaluation at the written list; five hang on the first meaning's letters at a first record and on the plan's numbers at the front (other files' layers). NO MEMBER. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtTerm
import Johnson.P5J.TieStart

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open Desc.K14 (St first p14Of beforePointOf)
open Desc.K14.Law (descZ secondAt fullShapeB full_index decShared decK heldFull rankLib hd_at_seat tp_by_make pw_by_make)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)) (DP : WholeD)
  (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) (err : ℕ) {Tok : Type}
  (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning (F0T o Zp Np cF).XiPub (Wit (CellsM numsFull) Tok MsgT))
  (ps : List Place) {Xg : Type} (Gd : FileDescription Xg)
  (smp : (F0T o Zp Np cF).XiPub × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)

/-- **The first table's decoder at the term reads the public part alone.** -/
theorem dtK_reads_first (c : ℕ → Option (ℕ × List UInt64)) (x x' : (F0T o Zp Np cF).XiPub × TS)
    (h : x'.1 = x.1) : dtK E o Zp Np cF hs err c x' = dtK E o Zp Np cF hs err c x := by
  unfold dtK decShared
  rw [h]

/-- **The facts on a start, at the term, from what is left.** Its type is what Lean infers. -/
def tieStart_at_term {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp) :=
  fun b1 b2 b3 b5 b6 b7 b8 b9 =>
    (TieStart.mk (Z := Z) (lay := lay) (X := X) (N := numsFull) (E := E) (DP := DP) (F₀ := F0T o Zp Np cF)
      (instP := LPFD.Full.instanceAsPlainRecord) (getS := fun s => s) (reqB := fun q : ProofFile.InstPub => q.request)
      (DT := dtK E o Zp Np cF hs err) (asked := ProofFile.Inst.asked) (cs := cs) (arr := arr) (ms := ms) (Nn := Nn)
      (Mg := Mg) (ps := ps) (Gd := Gd) (smp := smp) (codes := Zp.made.p.chains.proof.first.codes)
      (rq := fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request)
      b1 b2 b3 (start_at_term o Zp Np cF hpub) b5 b6 b7 b8 b9
      ⟨hdec_at_term E DP o Zp Np cF hs err, LPFD.Full.instOf_request, fun _ => rfl⟩
      (fin_at_term o Zp Np cF))

end P5J

#check @P5J.tieStart_at_term
#print axioms P5J.dtK_reads_first
#print axioms P5J.tieStart_at_term
