-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsChains
import Johnson.Desc.ProofFile.Lots.Later
/-
Johnson/Loose/H2K12/LaterSeatsN.lean: THE PROOF FILE's TWO LATER SEATS (the shared chain's; the last
chain's) AT THE NUMBERS N OF THE PROXIMITY TEST's FOUR PLACES: what ProofFile.laterShared |
ProofFile.laterSecond return where the maker's places are made (H2U.placesOfMade Z.made = .ok N). Cut out
of H2K12/SitsInPure.lean for the form over the library's own texts (Johnson/Desc/ProofFile/…).
NO
SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
HOW IT IS MADE, SO THAT A CHANGE OF OTHER FILES' TEXTS DOES NOT BREAK IT: no word of other files'
text is written out here. sharedN CALLS Desc.K14.sharedSeatOf; secondN IS P2Third.secondSeatOf Z N
with two fields laid anew (start · chain: at the parts X by which the own test decides): at X :=
guardedProximityTestParts it is that seat itself, by rfl (secondN_joined). What stands over these two should spend
the EQUATIONS below (sharedN_chain · secondN_chain · …), not unfold the seats' texts.
  sharedN · p14N · sharedN_chain | _start   the shared chain's seat at N; its chain IS
      Desc.K14.chainOf Z.p.chains (p14N Z N) (Seat.tests N) Seat.last
  p₁₄N · secondN · secondN_joined · secondN_chain | _start | _done   the last chain's seat at N
  laterShared_is | laterSecond_is: placesOfMade Z.made = .ok N ⇒ ProofFile.laterShared Z = some (sharedN
      Z N) · ProofFile.laterSecond Z = some (secondN guardedProximityTestParts Z N)
  laterShared_some | laterSecond_some   a seat is returned only where the places are made
  p12OfMade_is      H2U.p12OfMade Z.made = pL N there
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)

/-! ### the shared chain's seat -/

/-- The shared chain's seat (Desc.K14.sharedSeatOf), its «some» arm at N. -/
def sharedN (Z : ProofFile.Pub) (N : H2U.Places4) : ProofFile.SharedSeat :=
  _root_.Desc.K14.sharedSeatOf Z.p.chains (_root_.Desc.K14.beforePointOf N)
    (fun _ => Seat.tests N) [] Seat.last
    (VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains)

/-- The shared chain's public parameters as its seat makes them. -/
def p14N (Z : ProofFile.Pub) (N : H2U.Places4) : _root_.Desc.K14.P14 :=
  _root_.Desc.K14.p14Of Z.p.chains (_root_.Desc.K14.beforePointOf N)

/-- The seat's chain is the shared chain's own (Desc.K14.chainOf), with K12's two tests and end. -/
theorem sharedN_chain (Z : ProofFile.Pub) (N : H2U.Places4) :
    (sharedN Z N).chain =
      _root_.Desc.K14.chainOf Z.p.chains (p14N Z N) (Seat.tests N) Seat.last := rfl

theorem sharedN_start (Z : ProofFile.Pub) (N : H2U.Places4) :
    (sharedN Z N).start = fun x => _root_.Desc.K14.first (p14N Z N).codes x.key := rfl

theorem laterShared_is (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N) :
    ProofFile.laterShared Z = some (sharedN Z N) := by
  unfold ProofFile.laterShared _root_.Desc.K14.sharedSeatAt
  rw [hN]
  rfl

theorem laterShared_some (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (h : ProofFile.laterShared Z = some A) :
    ∃ N, H2U.placesOfMade Z.made = .ok N := by
  cases hN : H2U.placesOfMade Z.made with
  | ok N => exact ⟨N, rfl⟩
  | error w =>
    unfold ProofFile.laterShared _root_.Desc.K14.sharedSeatAt at h
    rw [hN] at h
    cases h

/-! ### the last chain's seat -/

/-- The last chain's public parameters as its seat makes them. -/
def p₁₄N (Z : ProofFile.Pub) : Third.P₁₄ :=
  Third.p₁₄Z Z.p.chains.made.sized.proof.set Z.p.chains.made.sized.proof.codes
    Z.p.chains.made.sized.proof.batch

/-- The last chain's seat at N, with its start and its chain laid at the parts X BY WHICH
THE OWN TEST DECIDES. All other fields are P2Third.secondSeatOf's own. -/
def secondN (X : Parts T12) (Z : ProofFile.Pub) (N : H2U.Places4) : ProofFile.SecondSeat :=
  { P2Third.secondSeatOf Z N with
    start := (Third.last (p₁₄N Z) Third.firstOfS Third.sharedOfEnd
      (onOwn (proximityTestKind X (pOwn N) : Blk'))).start
    chain := (Third.last (XiPub := ProofFile.InstPub) (p₁₄N Z) Third.firstOfS Third.sharedOfEnd
      (onOwn (proximityTestKind X (pOwn N) : Blk'))).chain }

/-- At the parts guardedProximityTestParts it is the seat P2Third.secondSeatOf itself. -/
theorem secondN_joined (Z : ProofFile.Pub) (N : H2U.Places4) :
    secondN guardedProximityTestParts Z N = P2Third.secondSeatOf Z N := rfl

theorem secondN_chain (X : Parts T12) (Z : ProofFile.Pub) (N : H2U.Places4) :
    (secondN X Z N).chain = (Third.last (XiPub := ProofFile.InstPub) (p₁₄N Z) Third.firstOfS
      Third.sharedOfEnd (onOwn (proximityTestKind X (pOwn N) : Blk'))).chain := rfl

theorem secondN_start (X : Parts T12) (Z : ProofFile.Pub) (N : H2U.Places4) :
    (secondN X Z N).start = (Third.last (p₁₄N Z) Third.firstOfS Third.sharedOfEnd
      (onOwn (proximityTestKind X (pOwn N) : Blk'))).start := rfl

theorem secondN_done (X : Parts T12) (Z : ProofFile.Pub) (N : H2U.Places4) :
    (secondN X Z N).done = Third.fin₃ := rfl

theorem laterSecond_is (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N) :
    ProofFile.laterSecond Z = some (secondN guardedProximityTestParts Z N) := by
  unfold ProofFile.laterSecond P2Third.secondSeat
  rw [hN]
  rfl

theorem laterSecond_some (Z : ProofFile.Pub) (B : ProofFile.SecondSeat) (h : ProofFile.laterSecond Z = some B) :
    ∃ N, H2U.placesOfMade Z.made = .ok N := by
  cases hN : H2U.placesOfMade Z.made with
  | ok N => exact ⟨N, rfl⟩
  | error w =>
    unfold ProofFile.laterSecond P2Third.secondSeat at h
    rw [hN] at h
    cases h

/-! ### the first chain's last test's parameters -/

theorem p12OfMade_is (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N) :
    H2U.p12OfMade Z.made = pL N := by
  unfold H2U.p12OfMade
  rw [hN]
  rfl

end H2K.JointK

#print axioms H2K.JointK.sharedN_chain
#print axioms H2K.JointK.laterShared_is
#print axioms H2K.JointK.laterShared_some
#print axioms H2K.JointK.secondN_joined
#print axioms H2K.JointK.secondN_chain
#print axioms H2K.JointK.laterSecond_is
#print axioms H2K.JointK.laterSecond_some
#print axioms H2K.JointK.p12OfMade_is
