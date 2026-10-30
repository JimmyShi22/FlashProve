-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsFile.lean: THE ROW K10_sits FOR THE WHOLE PROOF FILE's DESCRIPTION: EVERY BLOCK OF THE KIND K10, IN ANY OF ITS THREE CHAINS, IS THE SECOND BLOCK OF A LINK's CLOSING IN THE FIRST CHAIN, SEATED ALONE OVER THE KIND's OWN
BLOCK; THE TWO LATER CHAINS HOLD NONE. No premise on scope; every o for the second hash function; any row of segments.
  no_k10_elsewhere   O : IM.Open o pol lay KL F Z Bs base c A B: no block of F.shared.blocksInOrder and none of F.second.blocksInOrder is of the kind K10: no_k10_later (Johnson/Desc/ProofFile/Law/LaterKinds.lean) at Open's letters.
  k10_sits_file      with HeadIsTwo Z: (0) c is the first chain of the term that F is (first_is, SitsLaw.lean); (1) at every block b of c.blocksInOrder of the kind K10: l, sub, Lk, p, Q as in k10_sits_every (SitsEvery.lean, beside this file), with the law at b (K10LawAt b Q); (2) and (3): none in the two later chains.
LIMITS. HeadIsTwo Z is a premise (shown in scope, at OnBytes.secondHashFunction). That onlineDescription returns is a premise (Open). THE PROOF FILE ALONE: the key file's description is not here. All limits of Sits.lean and SitsLaw.lean but scope, size
and secondHashFunction. Nothing on soundness.
Statements and proofs.
-/
import Johnson.LPFK10R.SitsEvery
import Johnson.Desc.ProofFile.Law.LaterKinds

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Close (Par K10LawAt k10LawAt_of)
open ProofFile (Cl)
open IM

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **No block of the two later chains is of the kind K10.** -/
theorem no_k10_elsewhere (O : Open o pol lay KL F Z Bs base c A B) :
    (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ KindName.K10) ∧
      (∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ KindName.K10) := by
  have h := ProofFile.Law.no_k10_later (o := o) (mk := ProofFile.pureRoad.links) (get := fun s => s)
    (start := ProofFile.startS Z) (c := c) O.shared O.second
  rw [O.desc]
  exact h

/-- **K10_sits FOR THE WHOLE PROOF FILE's DESCRIPTION.** The first chain is said of the term that
Open.desc names (F's own field has F's own types): first_is (SitsLaw.lean). -/
theorem k10_sits_file (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) :
    (F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).first = c) ∧
    (∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ (l : ℕ) (sub : ModelPart) (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        (ProofFile.subsOf Z)[l]? = some sub ∧ c.links[l]? = some Lk ∧ k9At Z l = some p ∧
        ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ Lk.close[1]? = some b ∧
        LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype b.name
          (cAt l sub 1 KindName.K10) ∧ K10LawAt b Q) ∧
    (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ KindName.K10) ∧
      ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ KindName.K10 := by
  refine ⟨first_is O, fun b hb hk => ?_, (no_k10_elsewhere O).1, (no_k10_elsewhere O).2⟩
  obtain ⟨l, sub, Lk, p, Q, h0, h1, h2, h3, h4, h5⟩ := k10_sits_every O hk2 b hb hk
  exact ⟨l, sub, Lk, p, Q, h0, h1, h2, h3, h4, h5, k10LawAt_of h5 (by simp)⟩

end LPFK10

#print axioms LPFK10.k10_sits_file
#print axioms LPFK10.no_k10_elsewhere
