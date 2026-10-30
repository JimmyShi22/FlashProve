-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontItems.lean: the test on the typed field for the instance in the first query
of a proof file's first chain, general in the object with records: it names no page and no file.

The first chain's statement holds the instance through a function into two strings: the value of the
statement's item `request`, then the request file's bytes. At the typed interface an instance is an
instance of the object or none, and two records (`XC`, Johnson/RecCompile/Cms.lean); the two strings
are read off the first alone (`reqOf`, Johnson/Maker/Page/ReqAt.lean); the early part of what
`xinBA` gives is the early part of the object's instance and the fixed record twice (`early_xinBA`,
there). The test pins what the two strings do not hold, so that "the pair of strings is one to one
on what passes" comes down to a premise on the spelling sp of an instance of the object.

1. What the file contains.
    `okItems okS isR`: the test on an instance of the interface: it holds an instance of the object
      that passes okS, and both its records pass isR.

2. What is checked when the file compiles. The proofs.

3. Theorems.
    `hreq_items`: `reqOf sp` is one to one on what passes `okItems okS isR`, if sp is one to one on
      what passes okS and isR lets no record through but r₀.
    `okItems_run`: a triple (some (L.early x), r₀, r₀) passes, if the early part passes okS and the
      fixed record passes isR. No statement of this file names a verifier: that the early part of
      what `xinBA` gives is such a triple is `early_xinBA`. The rest is text and one statement on a
      header, none on a run: a session's verifier is the compiled verifier at `xinBA r₀` (`verifyOnlineProof`,
      Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean); a chain makes its first round's header of the early part
      of the instance that it is given (`recomputeChain`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean); what
      that header is at `xinBA r₀ (x, rec)` is said in `qS_head` (Johnson/Thin/Link/SessFirst.lean).
    `okList_run`: the same where okS is "stands on the list Rq" (OnBytes/K/Arm/ListApart.lean): the
      list holds early parts of instances, not the instances of which they are the early parts.

4. What is not claimed.
   sp, okS and isR are letters. okS names a set of instances, and the premise on sp says that no two
   of that set are spelt alike. A test okS that says no everywhere meets the premise on sp, and an
   isR that says no everywhere meets the premise on isR; at either nothing passes: the empty set.
   That a triple passes is `okItems_run`, which asks a yes of both. That they are chosen before a
   hash function is drawn and before a run does not follow from anything here: a bound over a random
   function has to ask it as a condition.
   sp gives a pair, and the premise speaks of the pair: two instances are spelt alike only if both
   strings are the same. Where both strings held a request by digests of the second hash function
   alone, no such set would hold all requests, by counting, at the programs' sizes. That the second
   string is a request file's bytes is said of no sp here.
   That two different instances that pass okS stand for two different request files: that is owed
   where the type of instances, the early part and sp are laid.
   Nothing on any page, on any hash, on soundness.

Terms: lean/GLOSSARY.md.


-/
import Johnson.Maker.Page.ReqAt
import OnBytes.K.Arm.ListApart

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open _root_.Iop (HolographicProtocol)
open OnBytes.Maker.Page

section Letters
variable {I X : Type} {L : HolographicProtocol I X}

/-- **The test on an instance of the interface.** -/
def okItems (okS : X → Bool) (isR : L.Rec → Bool) (z : L.XC) : Bool :=
  (match z.1 with
    | some x => okS x
    | none => false) && isR z.2.1 && isR z.2.2

/-- **The spelling is one to one on what passes.** -/
theorem hreq_items (sp : X → ByteArray × ByteArray) (okS : X → Bool) (isR : L.Rec → Bool)
    (r₀ : L.Rec)
    (hsp : ∀ x y, okS x = true → okS y = true → sp x = sp y → x = y)
    (hR : ∀ r, isR r = true → r = r₀) (z z' : L.XC) (h : okItems okS isR z = true)
    (h' : okItems okS isR z' = true) (e : reqOf (L := L) sp z = reqOf (L := L) sp z') : z = z' := by
  obtain ⟨a, r1, r2⟩ := z
  obtain ⟨a', r1', r2'⟩ := z'
  cases a with
  | none => simp [okItems] at h
  | some x =>
    cases a' with
    | none => simp [okItems] at h'
    | some x' =>
      simp only [okItems, Bool.and_eq_true] at h h'
      have e' : sp x = sp x' := e
      rw [hsp x x' h.1.1 h'.1.1 e', hR r1 h.1.2, hR r2 h.2, hR r1' h'.1.2, hR r2' h'.2]

/-- **The early part of an instance with the fixed record twice passes.** -/
theorem okItems_run (okS : X → Bool) (isR : L.Rec → Bool) (r₀ : L.Rec) (x : X)
    (h1 : okS (L.early x) = true) (h2 : isR r₀ = true) :
    okItems okS isR ((some (L.early x), r₀, r₀) : L.XC) = true := by
  simp only [okItems, h1, h2, Bool.and_self]

end Letters

end OnBytes.K.Arm.ProofFront

namespace OnBytes.K.Arm.ProofFrontList

open _root_.Iop (HolographicProtocol)
open OnBytes.K.Arm.ProofFront

/-- **The early part of an instance with the fixed record twice passes**, if the early part stands
on the list. -/
theorem okList_run {I X : Type} [DecidableEq X] {L : HolographicProtocol I X} (Rq : List X) (isR : L.Rec → Bool)
    (r₀ : L.Rec) (x : X) (h1 : L.early x ∈ Rq) (h2 : isR r₀ = true) :
    okItems (okList Rq) isR ((some (L.early x), r₀, r₀) : L.XC) = true :=
  okItems_run (okList Rq) isR r₀ x (decide_eq_true h1) h2

end OnBytes.K.Arm.ProofFrontList
