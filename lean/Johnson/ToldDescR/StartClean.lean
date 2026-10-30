-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/ToldDescR/StartClean.lean: NO SOUNDNESS IS CLAIMED.
(START), THE EIGHTH OF THE ELEVEN NAMED PREMISES OF part 5's seat 5's tablesGlued (Johnson/Desc/Sound/TablesGlued.lean):
    ∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → (get (p, s₁)).2.failed = none
AT EVERY DESCRIPTION THAT ProofFile's FRAME MAKES (fileDescBy, Johnson/Desc/ProofFile/Frames1.lean: it takes the format's second hash function as a letter o, and the first chain at the file's type of claims ProofFile.Cl), SO AT EVERY F THAT onlineDescription MAKES.
WHY IT HOLDS. The last chain's house says of its own start (Third.start₃F) that it reads neither the mark nor the debt. ProofFile's frame asks in front of it: Frames1.lean:218: «if !(get s₁).fin then .error …»; S.fin's first clause is «no mark» (Johnson/Desc/First/State.lean:767-768: s.failed.isNone && s.noneWaits && …).
  fin_clean             S.fin s = true → s.failed = none ∧ s.noneWaits = true
  start₃_fin            (fileDescBy o mk Z A B get start c).start₃ p s₁ s₂ = .ok s → (get s₁).fin = true
  **start_fileDescBy**  (START) at fileDescBy, general in get, at start₃ := fun p a b => (F.start₃ p a b).toOption
  start₃_ended          beside it: there the shared chain has ended: ∃ e, A.ended s₂ = some e ∧ B.start p (get s₁) e = .ok s
  **start_pureZ** | **start_descPure**   at what onlineDescriptionFromPublicPart | onlineDescription makes: the description IS fileDescBy … (fun s => s) (startS Z) c: so get := the identity, and (START) holds there
WHO READS EACH LETTER. get: the frame's one test. mk Z start c: nobody here. ∃ in start_pureZ | start_descPure: Z mk A B c: the public part that the road has made, its maker of the links, the seat's own shared and second chain and the first chain that onlineDescriptionFromPublicPart has made. Z stands with its equation (pureRoad.pub o pol lay KL = .ok Z: kept on part 5's reader's C3: so that whoever joins this with shared_fits_descPure at one F has ONE Z); mk A B c stand in the one equation F = fileDescBy ….
DOES NOT SHOW. Anything on the other ten premises. Nothing on soundness.
-/
import Johnson.ToldDescR.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open VerifiableInference.Desc (FileDescription Chain)
open VerifiableInference.Desc.First (S)

/-- What the fold's last test holds: no mark; no count waits. -/
theorem fin_clean {s : S} (h : s.fin = true) : s.failed = none ∧ s.noneWaits = true := by
  unfold S.fin at h
  simp only [Bool.and_eq_true] at h
  exact ⟨Option.isNone_iff_eq_none.1 h.1.1, h.1.2⟩

section
variable {σ : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat) (B : SecondSeat) (get : σ → S)
  (start : InstPub → σ) (c : Chain σ ProofFile.Cl)

/-- The frame's start of the last chain says yes only where the first chain stands at its end. -/
theorem start₃_fin (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : (fileDescBy o mk Z A B get start c).start₃ p s₁ s₂ = .ok s) : (get s₁).fin = true := by
  have h' : (if !(get s₁).fin then
      (.error "the first chain does not stand at its end" : Except String B.σ)
    else
      match A.ended s₂ with
      | none => .error "the shared chain has not ended"
      | some e => B.start p (get s₁) e) = .ok s := h
  cases hf : (get s₁).fin with
  | true => rfl
  | false =>
    rw [hf] at h'
    exact nomatch h'

/-- **(START) at ProofFile's frame.** -/
theorem start_fileDescBy (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : ((fileDescBy o mk Z A B get start c).start₃ p s₁ s₂).toOption = some s) :
    (get s₁).failed = none := by
  cases hs : (fileDescBy o mk Z A B get start c).start₃ p s₁ s₂ with
  | error e =>
    rw [hs] at h
    exact nomatch h
  | ok s' => exact (fin_clean (start₃_fin o mk Z A B get start c p s₁ s₂ s' hs)).1

/-- Beside it: there the shared chain has ended, and the seat's own start has said yes. -/
theorem start₃_ended (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : (fileDescBy o mk Z A B get start c).start₃ p s₁ s₂ = .ok s) :
    ∃ e, A.ended s₂ = some e ∧ B.start p (get s₁) e = .ok s := by
  have hf := start₃_fin o mk Z A B get start c p s₁ s₂ s h
  have h' : (if !(get s₁).fin then
      (.error "the first chain does not stand at its end" : Except String B.σ)
    else
      match A.ended s₂ with
      | none => .error "the shared chain has not ended"
      | some e => B.start p (get s₁) e) = .ok s := h
  rw [hf] at h'
  cases he : A.ended s₂ with
  | none =>
    rw [he] at h'
    exact nomatch h'
  | some e =>
    rw [he] at h'
    exact ⟨e, rfl, h'⟩

end

/-- **(START) at what `onlineDescriptionFromPublicPart` makes**: the description is the frame's at the identity. -/
theorem start_pureZ {Z : ProofFile.Pub} {T : PureSeat} {F : FileDescription ProofFile.Inst} (h : onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ A B c, F = fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c ∧
      ∀ (p : InstPub) (s₁ : S) (s₂ : A.σ) (s : B.σ),
        ((fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c).start₃ p s₁ s₂).toOption = some s →
          s₁.failed = none := by
  obtain ⟨A, B, c, -, -, e⟩ := pureZ_make h
  exact ⟨A, B, c, e, fun p s₁ s₂ s hs =>
    start_fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c p s₁ s₂ s hs⟩

/-- **(START) at every description that `onlineDescription` makes.** -/
theorem start_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (mk : LinksBy) (A : SharedSeat) (B : SecondSeat) (c : Chain S ProofFile.Cl),
      pureRoad.pub o pol lay KL = .ok Z ∧ F = fileDescBy o mk Z A B (fun s => s) (startS Z) c ∧
      ∀ (p : InstPub) (s₁ : S) (s₂ : A.σ) (s : B.σ),
        ((fileDescBy o mk Z A B (fun s => s) (startS Z) c).start₃ p s₁ s₂).toOption = some s →
          s₁.failed = none := by
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, e, k⟩ := start_pureZ h
  exact ⟨Z, _, A, B, c, hZ, e, k⟩

end ToldDesc

#print axioms ToldDesc.start_pureZ
#print axioms ToldDesc.start_descPure
#print axioms ToldDesc.fin_clean
#print axioms ToldDesc.start₃_fin
#print axioms ToldDesc.start_fileDescBy
#print axioms ToldDesc.start₃_ended
