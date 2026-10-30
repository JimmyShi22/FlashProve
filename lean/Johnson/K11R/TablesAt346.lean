-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/TablesAt346.lean: at every state that the proof file's first chain's own sub-protocols
hand on to border 346, in front of the merge of the claims on the committed table (kind K11),
`TablesLaid` holds (Johnson/Top/H0/MergeLaw/SpeaksOfTables.lean): the reads' tables that lie in the
state are the ones that `tablesAt` computes there. The premises are the goals' scope and the opening
of the description's value, and nothing else. Three theorems with their proofs: one step back, two
calls.

How. "Reached" is inductive: a state at border 346 comes by an accepting step of sub-protocol number
345 from a state that is reached at border 345. Number 345 is the lookup on the digits at the output
head's segment, the lot's own, laid alone (`IM.k3_of`, Johnson/IMR/K3Seat.lean). At border 345
whatever tables lie are what the reads' quiet step would lay off that very state
(`K1.tables_behind_digits`, Johnson/Desc/AtSeats/TablesAtRch.lean). Behind the lookup's accepting
step `TablesLaid` holds (`tablesLaid_behind_digits`,
Johnson/Top/H0/MergeLaw/TablesBehindDigits.lean): its quiet step itself asks that tables lie.

Main names.
  `tablesLaid_346`: along `Reach 0 c.blocksInOrder start`, at every start.
  `tablesLaid_at_346`: along `RchAt` at the description, and so along every family Rch all of whose
    members at 346 are reached.
  `tablesLaid_at_346_pub`: the same at the public part's own record Z.p.X.

What it is for. `speaks_at_front` (Johnson/Top/H0/MergeLaw/SpeaksAtFront.lean) takes `TablesLaid`
and the table's condition at 346 to the five tests of `Speaks`.

Limits. Where sub-protocol 345 never accepts from a reached state nothing is reached at 346, and the
theorems speak of no state; no reached state is exhibited here. The public record is the opening's
own (Bs.G₀.W; `IM.Open.W` ties it to Z.p.X). Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.TablesBehindDigits
import Johnson.Desc.AtSeats.TablesAtRch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (TablesLaid tablesLaid_behind_digits)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`TablesLaid` AT EVERY STATE REACHED AT BORDER 346.** -/
theorem tablesLaid_346 {Q : Type} {start : Q → S} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (345 + 1) a) :
    TablesLaid (VerifiableInference.Desc.K9.phAt Bs.G₀.W 24) a.2 := by
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O 24 (by omega) true
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix 24 true)] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact tablesLaid_behind_digits Bs.G₀.W _ _ _ _ h3
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
      (VerifiableInference.Desc.K1.tables_behind_digits hS hR O 24 (by omega) (z, s) h1)

/-- **Along "reached at the description's first chain"**, and along every family whose members at
346 are reached. -/
theorem tablesLaid_at_346 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type}
    (Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop)
    (hsub : ∀ a, Rch 346 a → RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
      (fun s => s) (ProofFile.startS Z) c) 346 a)
    (a : (ProofFile.InstPub × S) × Str) (h : Rch 346 a) :
    TablesLaid (VerifiableInference.Desc.K9.phAt Bs.G₀.W 24) a.1.2 :=
  tablesLaid_346 hS hR O a.1 (rchAt_raw (hsub a h))

/-- The same at the public part's own record. -/
theorem tablesLaid_at_346_pub (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type}
    (Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop)
    (hsub : ∀ a, Rch 346 a → RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
      (fun s => s) (ProofFile.startS Z) c) 346 a)
    (a : (ProofFile.InstPub × S) × Str) (h : Rch 346 a) :
    TablesLaid (VerifiableInference.Desc.K9.phAt Z.p.X 24) a.1.2 := by
  rw [← O.W]
  exact tablesLaid_at_346 hS hR O Rch hsub a h

end K11

#print axioms K11.tablesLaid_346
#print axioms K11.tablesLaid_at_346
#print axioms K11.tablesLaid_at_346_pub
