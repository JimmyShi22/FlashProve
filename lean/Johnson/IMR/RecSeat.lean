-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RecSeat.lean: AT THE PROOF FILE's SEAT: every block that the description lays in front of the
blocks behind the last link hands RecAll on (Johnson/Goal/Meaning/RecAll.lean), UNDER ONE NAMED
PREMISE ON KIND K2's OWN TEXTS. Johnson/IMR/SeatKeeps.lean at R := RecRel cs sh.

  K2Share cs sh: THE PREMISE: five clauses on K2's own texts (Johnson/Top/H0/Tw/K2C/): Whole
    (RecRel cs sh) (codeSwitchKind p); Fn (RecRel cs sh) of headFrontQ tl, headOpenQ P, finishFrontQ,
    finishBehindQ.
  seatKeeps_rec: K2Share cs sh → SeatKeeps (RecRel cs sh): the other clauses are framesOf_rec,
    firstAtS_rec, laterAt_rec, oneEquation_rec, closing_rec, shut_rec, batch_rec, and, through
    whole_rec, the Quiet makers' lemmas (Johnson/Goal/Meaning/RecSeated.lean, RecK7.lean).
  descPure_front: onlineDescription o pol lay KL = .ok F → F is fileDescBy … c, c.front = [], and every block
    of frontOf c (Johnson/Goal/Meaning/KeepsDriver.lean) is Decides (RecRel cs sh).
ON THE PREMISE: the five are through Lean on law files
(Johnson/Goal/Meaning/K2Share/K2Whole.lean: k2_recAll; RecFronts.lean), and k2Share
(Johnson/IMR/K2ShareAt.lean) proves K2Share cs sh at all cs and sh.
cs AND sh ARE LETTERS HERE: a keeping law: it bites at the plan's own pair, Z.first.codes and
Z.first.shape: Johnson/IMR/RecRun.lean states it there, with the start.
OBJECT: ProofFile.onlineDescription's value. USER: Johnson/IMR/RecRun.lean.
-/
import Johnson.IMR.SeatKeeps
import Johnson.Goal.Meaning.RecK9
import Johnson.Goal.Meaning.RecK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub)

variable {cs : Codes} {sh : ReqShape}

/-- **WHAT IS TAKEN ON KIND K2's OWN TEXTS** (Johnson/Top/H0/Tw/K2C/Kind.lean, Head.lean,
Finish.lean). -/
structure K2Share (cs : Codes) (sh : ReqShape) : Prop where
  k2 : ∀ p : K2.P2, Whole (RecRel cs sh) (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn (RecRel cs sh) (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, Fn (RecRel cs sh) (K2.headOpenQ P)
  finFront : Fn (RecRel cs sh) K2.finishFrontQ
  finBehind : Fn (RecRel cs sh) K2.finishBehindQ

theorem closeOf_whole (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Unit) p P, Whole (RecRel cs sh) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact oneEquation_rec p
  · exact closing_rec P
  · exact shut_rec p _

theorem seatKeeps_rec (H : K2Share cs sh) : SeatKeeps (RecRel cs sh) where
  refl := recRel_refl cs sh
  trans := recRel_trans cs sh
  frames := fun _ h => framesOf_rec h
  k1First := fun q gp _ => firstAtS_rec q gp
  k1Later := fun q gp l p m a _ => laterAt_rec q gp l p m a
  reads := fun h => whole_rec (readsQuietAt_quiet h)
  k3 := fun c r X cs' sh' a _ h => whole_rec (theStated_quiet c r X cs' sh' a h)
  k4 := fun p => whole_rec (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_rec (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_rec (seatedClaims_quiet h)
  k7 := fun W l => whole_rec (k7Of_quiet W l)
  k8 := fun p => whole_rec (k8Whole_quiet p)
  k11 := fun P => whole_rec (headMerge11_quiet P)
  closeOf := closeOf_whole
  batch := fun p _ hf => ⟨batch_rec p hf, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k2 := fun p _ => H.k2 p
  front := H.front
  openQ := fun P _ => H.openQ P
  finFront := H.finFront
  finBehind := H.finBehind

/-- **AT THE PROOF FILE's SEAT.** -/
theorem descPure_front (H : K2Share cs sh) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides (RecRel cs sh) b :=
  descPure_keeps (seatKeeps_rec H) (fun _ _ => trivial) h

#print axioms seatKeeps_rec
#print axioms descPure_front

end Meaning.K2
