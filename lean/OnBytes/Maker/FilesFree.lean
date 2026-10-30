-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/FilesFree.lean: the data at which a file's reduction stands (OnBytes/Maker/Files.lean)
do not hang on the table's key, as far as a dry run does not read it.

`keyIOR` and `proofIOR` take their rounds from dry runs of the program's blocks at the key of a
fixed record. A dry run reads of a key its item's number, the record's size, the number of seeds
and the length of each seed's point (`KeyAlike`, OnBytes/TypedOracleCompiler/Laws/LawDry.lean), and at two keys that
are alike in these the shared chain's block has one dry run (`shared_dryRun_eq`). The key enters the
three lists of rounds through that block alone.

  `keyAlike_of_fits`   two keys with one item's number whose sizes fit one shape (`TableKey.fits`,
        OnBytes/Iop/Foldeq.lean) are alike
  `dry3_keyAlike`, `dryKey_keyAlike`, `dryProof_keyAlike`   the three lists of rounds are the same
        at two keys that are alike
  `keyIOR_free`   so a key file's reduction is the same, whichever record it was made at, if the
        two records' keys are alike
  `proofIOR_free`   a proof file's reduction is the same at two records with keys that are alike
        and ONE instance

Not claimed. That a proof file's rounds do not hang on the instance (the request and the reply):
the first chain's block is made at it, and its dry run reads the request's words. That a key which
the program makes fits the shape. Nothing on soundness.


-/
import OnBytes.Maker.Files
import OnBytes.TypedOracleCompiler.Laws.LawDry

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ OnBytes.Proof OnBytes.TwoLaws

/-- Two lists of seeds of one length, all of whose points have one length, are alike. -/
theorem seedsAlike (n : ℕ) : ∀ (l l' : List SampleSeed), l.length = l'.length →
    (l.all fun x => x.z.length == n) = true → (l'.all fun x => x.z.length == n) = true →
    LAlike (fun a b : SampleSeed => a.z.length = b.z.length) l l'
  | [], [], _, _, _ => .nil
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | a :: l, b :: l', h, ha, hb => by
    rw [List.all_cons, Bool.and_eq_true] at ha hb
    exact .cons ((beq_iff_eq.1 ha.1).trans (beq_iff_eq.1 hb.1).symm)
      (seedsAlike n l l' (Nat.succ.inj h) ha.2 hb.2)

/-- **Two keys with one item's number whose sizes fit one shape are alike.** -/
theorem keyAlike_of_fits (s : Params.IndexShape) {key key' : TableKey} (hi : key.item = key'.item)
    (h : key.fits s = true) (h' : key'.fits s = true) : KeyAlike key key' := by
  unfold TableKey.fits at h h'
  simp only [Bool.and_eq_true, beq_iff_eq] at h h'
  exact ⟨hi, h.1.1.trans h'.1.1.symm,
    seedsAlike s.cubeBits _ _ (h.1.2.trans h'.1.2.symm) (by simpa using h.2) (by simpa using h'.2)⟩

variable {key key' : TableKey} (hk : KeyAlike key key')
include hk

/-- The key enters the three lists of rounds through the shared chain's block alone. -/
theorem dry3_keyAlike (p : TailPublic) (x₁ : Params.Rounds × FirstEnd) :
    Three.dry3 p key x₁ = Three.dry3 p key' x₁ := by
  unfold Three.dry3
  rw [shared_dryRun_eq p hk]

theorem dryKey_keyAlike (k : Params.KeyChains) : dryKey k key = dryKey k key' := by
  unfold dryKey
  exact congrArg _ (funext fun x₁ => dry3_keyAlike hk _ x₁)

theorem dryProof_keyAlike (c : Params.ProofChains) (b : Blk FirstEnd) :
    dryProof c key b = dryProof c key' b := by
  unfold dryProof
  exact congrArg _ (funext fun x₁ => dry3_keyAlike hk _ x₁)

omit hk

section
variable (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **A key file's reduction does not hang on the record at which it was made**, if the two records'
keys are alike. -/
theorem keyIOR_free {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (rec₀ rec₁ : R) (h : KeyAlike (key rec₀) (key rec₁)) :
    keyIOR C a tF tJ t3 silent key k rec₀ = keyIOR C a tF tJ t3 silent key k rec₁ := by
  unfold keyIOR
  rw [dryKey_keyAlike h k]

/-- **A proof file's reduction is the same at two records with keys that are alike and one
instance.** -/
theorem proofIOR_free {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk FirstEnd) (x : X) (rec₀ rec₁ : R)
    (h : KeyAlike (key rec₀) (key rec₁)) :
    proofIOR C a tF tJ t3 silent key c block (x, rec₀) =
      proofIOR C a tF tJ t3 silent key c block (x, rec₁) := by
  unfold proofIOR
  rw [dryProof_keyAlike h c (block x)]

end

end OnBytes.Maker
