-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GrowsSeat.lean: AT THE PROOF FILE's SEAT: behind every block that the description lays in front
of the blocks behind the last link the statement has only grown (Johnson/Desc/Grows.lean), UNDER ONE
NAMED PREMISE ON KIND K2's OWN TEXTS. Johnson/IMR/SeatKeeps.lean at R := GR
(Johnson/Goal/Meaning/GrowsSeated.lean: GrowsBy fun s => s.st).

  K2Grows: THE PREMISE: the five clauses of Johnson/IMR/RecSeat.lean's K2Share, at GR.
  seatKeeps_grows: K2Grows → SeatKeeps GR: the other clauses are framesOf_grows, firstAtS_grows,
    laterAt_grows, closeOf_grows, batch_grows, and, through whole_grows, the Quiet makers' lemmas.
  descPure_grows: onlineDescription o pol lay KL = .ok F → F is fileDescBy … c, c.front = [], and every block
    of frontOf c is Decides GR.
  descPure_growsRun: so for every cut frontOf c = l₁ ++ l₂ and every fold over l₁ from a record s
    that returns r: Grows s.st r.1.st.
IT IS NOT Johnson/Desc/StatementGrows.lean's owed premise ChainKeeps (GrowsBy st) c: that one also
asks the blocks behind the last link and the seal.
OBJECT: ProofFile.onlineDescription's value.
-/
import Johnson.IMR.SeatKeeps
import Johnson.Goal.Meaning.GrowsSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub)

/-- **WHAT IS TAKEN ON KIND K2's OWN TEXTS**, at "the statement grows". -/
structure K2Grows : Prop where
  k2 : ∀ p : K2.P2, Whole GR (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn GR (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, Fn GR (K2.headOpenQ P)
  finFront : Fn GR K2.finishFrontQ
  finBehind : Fn GR K2.finishBehindQ

theorem seatKeeps_grows (H : K2Grows) : SeatKeeps GR where
  refl := gr_refl
  trans := gr_trans
  frames := fun _ h => framesOf_grows h
  k1First := fun q gp _ => firstAtS_grows q gp
  k1Later := fun q gp l p m a _ => laterAt_grows q gp l p m a
  reads := fun h => whole_grows (readsQuietAt_quiet h)
  k3 := fun c r X cs' sh' a _ h => whole_grows (theStated_quiet c r X cs' sh' a h)
  k4 := fun p => whole_grows (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_grows (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_grows (seatedClaims_quiet h)
  k7 := fun W l => whole_grows (k7Of_quiet W l)
  k8 := fun p => whole_grows (k8Whole_quiet p)
  k11 := fun P => whole_grows (headMerge11_quiet P)
  closeOf := closeOf_grows
  batch := fun p _ hf => batch_grows p hf
  k2 := fun p _ => H.k2 p
  front := H.front
  openQ := fun P _ => H.openQ P
  finFront := H.finFront
  finBehind := H.finBehind

/-- **AT THE PROOF FILE's SEAT.** -/
theorem descPure_grows (H : K2Grows) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides GR b :=
  descPure_keeps (seatKeeps_grows H) (fun _ _ => trivial) h

theorem descPure_growsRun (H : K2Grows) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₁ s rs cols = .ok r → Grows s.st r.1.st := by
  obtain ⟨Z, A, B, c, h1, h2, h3, k⟩ := descPure_grows H h
  refine ⟨Z, A, B, c, h1, h2, flat_eq h3, fun l₁ l₂ hl ft s rs cols r hf => ?_⟩
  exact Keeps.foldBlocks_keeps GR gr_refl gr_trans ft l₁
    (fun b hb => k b (hl ▸ List.mem_append_left _ hb)) s rs cols r hf

#print axioms seatKeeps_grows
#print axioms descPure_grows
#print axioms descPure_growsRun

end Meaning.K2
