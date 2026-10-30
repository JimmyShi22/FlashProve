-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean: "TIDY" AT EVERY REACHED STATE OF THE FIRST CHAIN, AT THE OPENING's
OWN PUBLIC PART AND CHAIN. tidy_field has the fact at a public part Z
and a first chain c that stand behind "there are". Whoever holds other facts at the Z and c of an
opening of the IOP as written in Lean (IM.Open) wants it at these very letters, so
that all meet at one chain. HERE: the two are the same: Z by the two returns of pub, c because one
IOP as written in Lean has one first chain.

  tidy_at         the fact at a given Z and c, from pub's return and the IOP's spelling at them.
  tidy_at_open    **the same at an opening's own Z and c.** Along the list in the wrap (c.blocksInOrder.map
                  below): "reached" as RchAt (Johnson/Top/H0/Walk/ReachAt.lean) has it.
  tidy_at_raw, tidy_at_open_raw   the two along the raw list c.blocksInOrder (from tidy_paid).
LEFT: F.planOk = true (a test with code; LPFD.Full.laidPOf_ok gives it). The fence "no mark" stands
in the statement and is not spent.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.Fit.TidyPaid
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach RchAt)
open OnBytes.Means (tidy4B_iff)
open ProofFile (Pub)

theorem tidy_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {c : Chain S ProofFile.Cl}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hd : F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) :
    ∀ (k : ℕ) (q : ProofFile.InstPub × S), Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k q →
      q.2.failed = none → OnBytes.Means.tidy4B q.2.st = true := by
  obtain ⟨Z', A', B', c', hZ', e', K⟩ := tidy_field h hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  have e := e'.symm.trans hd
  have h1 := congrArg (fun G : FileDescription ProofFile.Inst =>
    (⟨G.S₁, G.Cl, G.first⟩ : Σ (T C : Type), Chain T C)) e
  have h2 : (⟨S, ProofFile.Cl, c'⟩ : Σ (T C : Type), Chain T C) = ⟨S, ProofFile.Cl, c⟩ := h1
  have h3 := eq_of_heq (Sigma.mk.inj h2).2
  obtain rfl : c' = c := eq_of_heq (Sigma.mk.inj h3).2
  intro k q hr hm
  exact K Unit k (q, ()) hr hm

theorem tidy_at_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
    {Bs base} {c : Chain S ProofFile.Cl} {A B}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∀ (k : ℕ) (q : ProofFile.InstPub × S), Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k q →
      q.2.failed = none → OnBytes.Means.tidy4B q.2.st = true :=
  tidy_at h hF O.pub O.desc

theorem tidy_at_raw {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {c : Chain S ProofFile.Cl}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hd : F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) :
    ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a →
      a.2.failed = none → OnBytes.Means.tidy4B a.2.st = true := by
  obtain ⟨Z', A', B', c', hZ', e', K⟩ := tidy_paid h hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  have e := e'.symm.trans hd
  have h1 := congrArg (fun G : FileDescription ProofFile.Inst =>
    (⟨G.S₁, G.Cl, G.first⟩ : Σ (T C : Type), Chain T C)) e
  have h2 : (⟨S, ProofFile.Cl, c'⟩ : Σ (T C : Type), Chain T C) = ⟨S, ProofFile.Cl, c⟩ := h1
  have h3 := eq_of_heq (Sigma.mk.inj h2).2
  obtain rfl : c' = c := eq_of_heq (Sigma.mk.inj h3).2
  exact fun k a hr _ => tidy4B_iff.2 (K k a hr)

theorem tidy_at_open_raw {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : Pub} {Bs base} {c : Chain S ProofFile.Cl} {A B}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a →
      a.2.failed = none → OnBytes.Means.tidy4B a.2.st = true :=
  tidy_at_raw h hF O.pub O.desc

end Meaning.K2

#print axioms Meaning.K2.tidy_at
#print axioms Meaning.K2.tidy_at_open
#print axioms Meaning.K2.tidy_at_raw
#print axioms Meaning.K2.tidy_at_open_raw
