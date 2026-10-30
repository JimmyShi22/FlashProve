-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/LPFK10R/HandsK10At.lean:
K10's 25 OF THE 358 «Hands», IN SCOPE, IN THE FORM THAT COUNTS, AT THE COMPOSED PUBLIC TESTS: IM.HandsR UNDER ONE FENCE; NO OPEN BINDER ON A STATE. A definition, statements and proofs.
  OutFence k s      THE FENCE: the index masks' message is a member of no group of s.st (at every k; under no «no mark»). It is part 1's second clause outOfGroupsB (Johnson/P1L20R/RoomFold.lean), by outOfGroupsB_iff.
  pubFitK_w         pubFitK moreAll LW PW = true (Johnson/Desc/First/Close/Law/EPubAtK10.lean's test on the table's lists; LW, PW: CloseShare.lean): BY THE KERNEL. pubFitK_bent: A NEGATIVE TEST: with the place number 11 (the one in front of link 0's K10, which stands at number 12) taken out of PW it says no: by the kernel.
  more_k10          the field «more» at K10's 25 numbers, fenced, at E := fun k s => ePubAt (pubAll D bs) moreAll LW PW k (z, s): from e_k10.
  close_k10R_at     InScope P · readFiles P = .ok pp · IM.Open … · hb (the base's tests answer alike at any two states): ∀ l < 25, p, Q, x: (K9.closeOf p Q)[1]? = some x → IM.HandsR OutFence (N.withTold PW (toldC c)) LW PW E ft (14 * l + nA l + 4 + 1) x.retype.
LIMITS. THE FENCE IS OWED AT EVERY REACHED STATE (`x_at_cutR` asks it behind each cut of the fold): part 1's room_both has it at the reached states 3 ≤ k ≤ 355 UNDER RoomOwes, of whose shares few are paid: not imported here. hb is a premise: at the base that says no to every public test it holds by rfl. D, bs, z, N are letters. In scope, at OnBytes.secondHashFunction.
IT STANDS OVER «v6 + laws.3» WITH part 5's mgAll version 9 (second laying) AND OUR LINK PEN's EPubRides FAMILY (the seal ob-seed-n-5-laws-3-mg9b: not whole-built), with files laid (the pack's page lists them). No soundness statement.

-/
import Johnson.LPFK10R.CloseShareR
import Johnson.Desc.First.Close.Law.EPubAtK10

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place Oracle KindName)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll ePubAt)
open VerifiableInference.Desc.First.Close (Par K10Step pubFitK e_k10)
open ProofFile (Cl)
open IM

/-- The fence: the index masks' message is a member of no group of the statement. -/
def OutFence (_ : Nat) (s : S) : Prop := ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members

set_option maxRecDepth 1000000 in
/-- **The test on the table's lists says yes at the 25 sorts' list of places.** -/
theorem pubFitK_w : pubFitK moreAll LW PW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with the first K10 place's neighbour in front taken out of the list of places it says no. -/
theorem pubFitK_bent : pubFitK moreAll LW (PW.eraseIdx 11) = false := by decide +kernel

section
variable {Pz : Type} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
  {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **«more» AT K10's 25, FENCED, AT THE COMPOSED PUBLIC TESTS.** -/
theorem more_k10 (D : PubData) (bs : Pub → Pz × S → Bool) (z : Pz)
    (hb : ∀ q (s s' : S), bs q (z, s') = bs q (z, s)) (N : Numbers) :
    ∀ l < 25, ∀ s s', OutFence (14 * l + nA l + 5) s → K10Step s s' → s.failed = none →
      IM.XK N LW PW (fun k s => ePubAt (pubAll D bs) moreAll LW PW k (z, s))
        (14 * l + nA l + 5) s = true →
      ePubAt (pubAll D bs) moreAll LW PW (14 * l + nA l + 5 + 1) (z, s') = true := by
  intro l hl s s' hf hs _ hx
  obtain ⟨p, hp, hk⟩ := k10_place_w hl
  exact e_k10 D bs LW PW z hb _ p pubFitK_w hp hk s s' hs hf (IM.xk_parts hx).2.2.2.2

/-- **K10's 25 OF THE 358, IN SCOPE: HandsR UNDER THE FENCE, AT THE COMPOSED PUBLIC TESTS: NO OPEN BINDER ON A STATE.** -/
theorem close_k10R_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (D : PubData)
    (bs : Pub → Pz × S → Bool) (z : Pz) (hb : ∀ q (s s' : S), bs q (z, s') = bs q (z, s))
    (N : Numbers) (ft : Nat) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      IM.HandsR OutFence (N.withTold PW (toldC c)) LW PW
        (fun k s => ePubAt (pubAll D bs) moreAll LW PW k (z, s)) ft (14 * l + nA l + 4 + 1)
        x.retype :=
  close_k10R_scope hS hR O OutFence N _ ft (more_k10 D bs z hb _)

end

end LPFK10

#print axioms LPFK10.pubFitK_w
#print axioms LPFK10.pubFitK_bent
#print axioms LPFK10.more_k10
#print axioms LPFK10.close_k10R_at
