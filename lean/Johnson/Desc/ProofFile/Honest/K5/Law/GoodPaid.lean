-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/GoodPaid.lean: Good (Honest/Side.lean) AT THE ROW OF AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5: the label of that sub-protocol in the description), AS ONE
TERM, WITH THE THREE SENTENCES ON THE FRAME's OWN PARTS NO LONGER PREMISES: each of the three forms
of Honest/K5/Law/GoodForms.lean is had from a theorem on that part. Statements with their proofs,
each one term.

  msForm_paid    MSForm at every bud: from exact_sumPart_field (Honest/SumLaw/SumExact.lean), its
                 third premise from betaMarked_of_like (Honest/SumLaw/BetaMarked.lean)
  loneForm_paid  LoneForm at every bud: from scalarsPart_exact_lift (Honest/Small/Scalars.lean)
  quietForm_paid QuietForm at every bud: from quietPart_exact_lift at one round
                 (Honest/Small/Quiet.lean); both through Honest/Small/StatedBy.lean
  k5_good_paid   CONDITIONAL: k5_good (Honest/K5/Law/Good.lean) with its three first premises struck
  k5_goodAt_paid the same at the row with its letters (k5Lettered, Honest/K5/Law/Bud.lean)

WHAT k5_good_paid SAYS, AND WHAT NOT. AT A := B := THE EMPTY SENTENCE (False): plays AND acc ARE MET
FOR NOTHING: nothing is said on the playing or on the verifier's yes. fits is shown. fresh is shown,
AND IS EMPTY: the row has no coin of its own; it alone spends hk: no entry of the book names a part
of this place as owner. exact is had, member by member, from the three theorems on the frame's own
parts, UNDER THE PREMISES THAT STAY: K5Block: four facts on the description's member at the place:
SHOWN IN THIS FILE OF NO DESCRIPTION's MEMBER (of the kind's own sub-protocol: block_kind,
Honest/K5/Law/RowIs.lean; of the description's own member, under the library's head: k5Block_head,
Honest/K5/Law/GoodHead.lean, WHICH THIS FILE DOES NOT IMPORT) · the side's row is K5's · hx: the
verifier's test on a call's shape says yes at every call of the row.

Every part of K5's row has takes = ⟨0, 0⟩; that no entry of the book names one as owner is the
premise hk. exact speaks, AT EACH MEMBER BY ITSELF, of the runs that it spends AS UNIFORM AND
INDEPENDENT of each other and of all that is fixed in the equation. That they are so in a run is not
stated here: it needs AT THE LEAST fresh at the part that owns them, the book's lending of just
these runs, and that no two of them share a coin. Of what stands in front the row's jobs read the
challenges alone.

NEVER LEFT OFF, as the theorem on the masked sumcheck's part has it (Honest/SumLaw/SumExact.lean):
the spender's half alone · the owners' sentences are typed by no file of this folder, and none is
called here · one part at a time, all else fixed before the coins · it holds at every job, right or
wrong, so it says nothing on whether the job is the protocol's · nothing on hiding. ("This folder"
is said here of Honest/K5/ and K5/Honest/.)

WHOEVER CARRIES A RUN BEHIND ITS SPENDER, as the theorem on the round of n scalars has it
(Honest/Small/Scalars.lean): the frame lets any part behind the spender carry it, and c to t + c is
one to one: what this part shows, together with the run, gives t at every coin: so such a carrier
has to meet its own exact at each fixed carried run, beside a simulator that is not handed it: not
shown here. At K5 the runs are entries of the segment's mask row: PAID BY NOBODY HERE.

THE CALLER's CONDITION, AND K5 IS THE CALLER. In these theorems a job may read the rounds shown in
front of the part: they are fixed before the coins there; where an item that a job reads was sent
under an entry which is spent here, that is not so in a run, and the theorems say nothing. THAT AT
K5's ROW NO MOVE OF A MEMBER OF THE SIDE READS ANYTHING OF WHAT HAS BEEN SEEN IS k5_members_noneSeen
(Honest/K5/Law/NoneSeen5.lean), WHICH THIS FILE DOES NOT IMPORT.
By the jobs' texts and types: what is handed on is Unit; there is no
point; of the input the trace alone is read. What was heard is handed on whole, a digest that stands
in a challenge too, and the seat's reader of the key points is a free field. ONE SLOT OF A JOB IS
HANDED COINS: the summand at Y is handed the run of the end values that the same job spends: the
frame's own letter, at every job.

Limits. No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Good
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact
import Johnson.Desc.ProofFile.Honest.Small.Scalars
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.Small.StatedBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (shapes)

/-! ## 1 The three forms -/

/-- **The form at the masked sumcheck's part holds, at every bud.** No premise. -/
theorem msForm_paid (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : MSForm bud :=
  fun _ _ _ _ _ _ _ _ φ σ chain firstTree see wit name endName J j rs hk hr hd =>
    SumLaw.exact_sumPart_field φ σ chain firstTree (fun _ _ _ _ => True) bud see wit (fun _ => ())
      (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl) name endName J hk rs hr
      (SumLaw.betaMarked_of_like _ _ hd) j ⟨σ.block.place, j⟩

/-- **The form at the round that sends n scalars holds, at every bud.** No premise. -/
theorem loneForm_paid (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    LoneForm bud :=
  fun _ _ _ _ _ _ _ _ φ σ chain firstTree see wit name n vals j rs hr =>
    Small.scalarsPart_exact_lift φ σ chain firstTree (fun _ _ _ _ => True) bud j n rs
      ⟨σ.block.place, j⟩ name vals see wit (fun _ => ()) (fun x _ => x)
      (Small.stated_scalars_of hr)

/-- **The form at the round that sends nothing holds, at every bud.** No premise. -/
theorem quietForm_paid (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    QuietForm bud :=
  fun _ _ _ _ _ _ _ _ φ σ chain firstTree see wit j rs hr =>
    Small.quietPart_exact_lift φ σ chain firstTree (fun _ _ _ _ => True) bud j 1 rs
      ⟨σ.block.place, j⟩ see wit (fun _ => ()) (fun x _ => x) (Small.stated_quiet_one_of hr)

/-! ## 2 Good at K5's row -/

variable {W₀ Rc Xi Tr X Pb S Cl : Type}
  {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells} {Z : Seat5}
  {p : P.Par}

/-- **Good at K5's row, as one term, AT A := B := THE EMPTY SENTENCE (False): SO ITS FIELDS plays
AND acc ARE MET FOR NOTHING: IT SAYS fits, exact AND fresh, AND NOTHING ON THE PLAYING OR ON THE
VERIFIER's YES; fresh IS EMPTY.** CONDITIONAL: on K5Block, the row, hx and hk: see the head. pre is
tied to no description; at each pre this says of exact no more than msForm_paid, loneForm_paid and
quietForm_paid. -/
theorem k5_good_paid (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat) (hB : K5Block σ.block Z p)
    (hr : σ.row = k5Pairs cells Z)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z.place) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) k5Bud :=
  k5_good (msForm_paid _) (loneForm_paid _) (quietForm_paid _) pre φ Bk ord chain firstTree hB hr hx
    hk

/-- **The same at the row with its letters**, at every list of earlier chains' declared rounds:
Good's pre is made there of earlier, bs and the place (preOf, Honest/Rule.lean); it is not read. BY
TYPE IT GIVES WHAT THE FIELD good OF THE STRUCTURE Owed ASKS AT K5's ROW THROUGH ONE CALL
(Lettered.goodAt_withField, Honest/FieldFree.lean), WHICH IS NOT MADE HERE; BY WEIGHT IT SAYS fits,
exact (THE SPENDER's HALF) AND AN EMPTY fresh, AND NOTHING ON plays OR acc. CONDITIONAL: as
k5_good_paid; hB: whichever member of the list stands at the place meets K5Block. -/
theorem k5_goodAt_paid (earlier : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts)
    (bs : List (Block S Cl)) (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S))
    (hB : ∀ τ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb,
      (k5Lettered Bk S Cl cells Z).side bs fs = some τ → K5Block τ.block Z p)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z.place) :
    (k5Lettered (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) Bk S Cl cells Z).goodAt earlier
      φ bs ord chain firstTree fs :=
  k5_goodAt (msForm_paid _) (loneForm_paid _) (quietForm_paid _) earlier φ Bk bs ord chain firstTree
    fs hB hx hk

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.msForm_paid
#print axioms ProofFile.Honest.K5.loneForm_paid
#print axioms ProofFile.Honest.K5.quietForm_paid
#print axioms ProofFile.Honest.K5.k5_good_paid
#print axioms ProofFile.Honest.K5.k5_goodAt_paid
