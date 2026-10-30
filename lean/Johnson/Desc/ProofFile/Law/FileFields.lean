-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/FileFields.lean: what the last test of the proof file's IOP as written in
Lean says of the token that is asked about. Four small theorems on the text of `fileDescBy`
(Frames1.lean), `Inst.asked` (Pub.lean) and `S.finAsked` (Johnson/Desc/First/State.lean). No file of
that IOP imports this one.
Whose. They are taken over from Johnson/Desc/Plain/Leaves/PureHears.lean
and SeatHears.lean (a file that is not in this library), names
and statements to the letter, in the namespace `ProofFile`, so that little has to lie beneath whoever
calls them. One proof is this file's own: `descPure_fin` goes through `descPure_parts`
(PureMade.lean), not, as there, through `descPure_hears_at`.
  `fileDescBy_fin`   where the last test accepts, `S.finAsked` accepts at the element asked about
  `finAsked_reply`   where `S.finAsked a` accepts, the state's reply is `a`
  `asked_of_y`       the element asked about is the first 32-bit word of the reply file's bytes
  `descPure_fin`     the first of these at `onlineDescription`'s value
This file's own, beside them:
  `fileDescBy_fin_parts`, `finAsked_fin`   all four conjuncts of the last test; `S.fin` among them
  `finPub`, `fileDescBy_finPub`   the part of the last test that reads the public part alone, and
                     that the last test gives it: `FinGives` (Johnson/Desc/Sound/DescFin.lean)
                     written out

-/
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First

variable {σ : Type}

/-- **Where the last test accepts, `S.finAsked` accepts at the element that is asked about**, at
every structure that `fileDescBy` returns: by its text. -/
theorem fileDescBy_fin (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat) (B : SecondSeat)
    (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl) (x : Inst) (s₁ : σ) (s₂ : A.σ) (s₃ : B.σ)
    (hf : (fileDescBy o mk Z A B get start c).fin x s₁ s₂ s₃ = true) :
    (get s₁).finAsked x.asked = true := by
  have hf' : ((get s₁).finAsked x.asked && (get s₁).req == Verify.words32 x.pub.request &&
    (A.ended s₂).isSome && B.done s₃) = true := hf
  simp only [Bool.and_eq_true] at hf'
  exact hf'.1.1.1

/-- All four conjuncts of the last test. -/
theorem fileDescBy_fin_parts (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat)
    (B : SecondSeat) (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl) (x : Inst) (s₁ : σ)
    (s₂ : A.σ) (s₃ : B.σ) (hf : (fileDescBy o mk Z A B get start c).fin x s₁ s₂ s₃ = true) :
    (get s₁).finAsked x.asked = true ∧
      ((get s₁).req == Verify.words32 x.pub.request) = true ∧ (A.ended s₂).isSome = true ∧
      B.done s₃ = true := by
  have hf' : ((get s₁).finAsked x.asked && (get s₁).req == Verify.words32 x.pub.request &&
    (A.ended s₂).isSome && B.done s₃) = true := hf
  simp only [Bool.and_eq_true] at hf'
  exact ⟨hf'.1.1.1, hf'.1.1.2, hf'.1.2, hf'.2⟩

/-- Where `S.finAsked` accepts, so does `S.fin`. -/
theorem finAsked_fin (a : E) (s : S) (h : s.finAsked a = true) : s.fin = true := by
  unfold S.finAsked at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- **The part of the last test that reads the public part alone**: not the token that is asked
about. -/
def finPub (A : SharedSeat) (B : SecondSeat) (get : σ → S) (p : InstPub) (s₁ : σ) (s₂ : A.σ)
    (s₃ : B.σ) : Bool :=
  (get s₁).fin && (get s₁).req == Verify.words32 p.request && (A.ended s₂).isSome && B.done s₃

/-- Where the last test accepts, so does that part, at the instance's public part. This is
`FinGives F g` (Johnson/Desc/Sound/DescFin.lean), written out, at `g := finPub A B get`, without its
premise on the test on the instance. -/
theorem fileDescBy_finPub (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat)
    (B : SecondSeat) (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl) (x : Inst) (s₁ : σ)
    (s₂ : A.σ) (s₃ : B.σ) (hf : (fileDescBy o mk Z A B get start c).fin x s₁ s₂ s₃ = true) :
    finPub A B get ((fileDescBy o mk Z A B get start c).pub x) s₁ s₂ s₃ = true := by
  obtain ⟨h1, h2, h3, h4⟩ := fileDescBy_fin_parts o mk Z A B get start c x s₁ s₂ s₃ hf
  show ((get s₁).fin && (get s₁).req == Verify.words32 x.pub.request && (A.ended s₂).isSome &&
    B.done s₃) = true
  rw [finAsked_fin _ _ h1, h2, h3, h4]
  rfl

/-- Where `S.finAsked` accepts, the state's reply is the element that is asked about. -/
theorem finAsked_reply (a : E) (s : S) (h : s.finAsked a = true) : s.out.reply = some a := by
  unfold S.finAsked at h
  simp only [Bool.and_eq_true] at h
  exact eq_of_beq h.1.2

/-- The element that is asked about is the first word of the reply file's bytes: the text of
`Inst.asked`. -/
theorem asked_of_y (x : Inst) (bs : ByteArray) (e : x.y = bs) :
    x.asked = ofNat ((Verify.words32 bs).getD 0 0).toNat := by
  rw [← e]
  rfl

/-- **The last test at `onlineDescription`'s value**: where it accepts, `S.finAsked` accepts at the element
that is asked about, read at the first chain's last state itself. -/
theorem descPure_fin (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst)
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (c : Chain S Cl) (A : SharedSeat) (B' : SecondSeat),
      F = fileDescBy o pureRoad.links Z A B' (fun s => s) (startS Z) c ∧
      ∀ (x : Inst) (s₁ : S) (s₂ : A.σ) (s₃ : B'.σ),
        (fileDescBy o pureRoad.links Z A B' (fun s => s) (startS Z) c).fin x s₁ s₂ s₃ = true →
          s₁.finAsked x.asked = true := by
  obtain ⟨Z, _, _, c, A, B', _, _, _, _, _, _, _, _, e⟩ := Law.descPure_parts h
  exact ⟨Z, c, A, B', e, fun x s₁ s₂ s₃ hf => fileDescBy_fin _ _ Z A B' _ _ c x s₁ s₂ s₃ hf⟩

end ProofFile

#print axioms ProofFile.fileDescBy_fin
#print axioms ProofFile.finAsked_reply
#print axioms ProofFile.asked_of_y
#print axioms ProofFile.descPure_fin
#print axioms ProofFile.fileDescBy_fin_parts
#print axioms ProofFile.fileDescBy_finPub
