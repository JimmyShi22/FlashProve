-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/WitOwnerFull.lean: the honest side of the kind "lookup" (K3).
Conditional: at the full size, at the trace's own reader of cells, the filling that reads a borrowed
matrix under its owner's segment and name (Honest/K3/WitOwner.lean) is the filling at which the
theorems on keys and bits stand (Honest/K3/WitFill.lean). One definition of a hypothesis, and
theorems.

Terms. Honest/K3/GLOSSARY.md: see there owner and borrowed matrix, seated filling, sources, keys and
bits are honest, trace's bundles, cells and full size. In this file: X is the verifier program's
public structure, T a trace, i an index, x a request; `cellOf X T` (Johnson/HonestTrace/Full.lean)
is the trace's own reader of cells.

What is shown.
  `PlanOwners`: the public hypothesis: at each of the 25 links the list of where the matrices are
    read, made of the plan's own marks (`matsOwn`, WitOwner.lean), is the list of the trace's files
    (`matsOf`).
  `cellOf_owner`: at an entry of a link's list, the reader's cell under the owner's segment and name
    is the trace's entry at the link.
  `atOwn_cellOf`, `atOwn_atNo`: the reading at a matrix's number is the trace's entry, in the
    extension field; it is the reading by labels under the link's own number.
  `ownG_eq`, `ownA_eq`, `ownH_eq`: the three equations of readings, as functions on names.
  `zzOwn_eq`: ZZ is the full size's.
  `ownG_meets`, `ownA_meets`, `ownH_meets`: keys and bits are honest at the filling's own terms.
The theorems on keys and bits (`lookG_meets`, `lookA_meets`, `lookH_meets`, WitFill.lean) stand at
the readings `fromG`, `fromA`, `fromH` of Johnson/HonestTrace/FromCells.lean, which read a borrowed
matrix under the borrower's segment and label; the reader `cellOf X T` answers there too. The
filling that reads under the owner's segment and name comes to the same values at that reader,
because owner and borrower hold the same entries of the trace (`cellsAtOf_matsOf`,
Johnson/HonestTrace/DigitsAtTrace.lean).

Hypotheses that remain.
  `B`, `O`: `PlanLabels X` (Honest/K3/WitPlan.lean) and `PlanOwners X`: public both.
  `N`, `M`: `NamesFit X T` and `MeetsAll X i x T`.
  `Q`, `L`: (for the last three) `LookPub X` and `PlanesLaid X i x T`.
  `hk`, `hg`, `hy`: the link is below 25; the group is below 12; in `ownH_meets`, the letter pubH
    yields the trace's files' structure at the request.
  `hE`: (in `cellOf_owner`) E is entry a of the link's list of matrices.

Imported. Honest/K3/WitDigits.lean, which lies beneath this file, imports
Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Honest/K3/Law/WitOwnerMarks.lean [not in this library] calls each theorem of this file.
Honest/K3/Law/MeetsNamed.lean calls `ownG_eq`, `ownA_eq` and `ownH_eq`.
Honest/K3/Law/WitOwnerMember.lean [not in this library] and Honest/K3/Law/Thread/LeftAtCallsMid.lean
import this file too.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At the full size alone: `NamesFit` fixes its numbers (twelve groups; the parts 3, 1, 1, 4). The
library has a theorem for each of the trace's four bundles at its own honest trace, in files that
this one does not import (Honest/K3/GLOSSARY.md, "trace's bundles").
On the two public hypotheses: `planOwners_marks` (WitOwnerMarks.lean [not in this library; so here
read: not proved in this library]) shows `PlanOwners X` from two other hypotheses, `PlanMarks X` and
`PartsFit X`, and that file states each theorem of this one at these two.
Honest/K3/Law/WitOwnerMember.lean [not in this library; so here read: not proved and not tested in
this library] has `PlanLabels` and `PlanOwners` as tests with code, each with a theorem from its
acceptance; both accept, by evaluation, at one synthetic public part at the full size's numbers.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (fromG fromA fromH fsAt pubHAt cellOf entryOf atNo labelAt matsOf cellsC
  NamesFit LookPub MeetsAll PlanesLaid Tr)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref)
open ProofFile.Honest.K8 (cellsAtOf signedOf)

/-- **The public hypothesis on the plans' marks.** -/
def PlanOwners (X : OnBytes.Model.Verify.Public) : Prop := ∀ k < 25, matsOwn X k = matsOf X k

section
variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- At an entry M of the list of link k: the reader's cell under the segment and name of the owner
of M is the trace's entry at link k. Conditional on `PlanOwners X`, `NamesFit X T`,
`MeetsAll X i x T`, k < 25. No instance of these hypotheses is exhibited in this file. -/
theorem cellOf_owner (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ}
    (hk : k < 25) {a : ℕ} {E : OnBytes.Model.TMat} (hE : (tlOf X k).mats[a]? = some E) (r c : ℕ) :
    cellOf X T (ownerOf X k E).1 (ownerOf X k E).2 r (E.ttOff + c) = ((T k a r c : ℤ) : Cb.Gl.F) :=
      by
  have h1 := OnBytes.HonestTrace.cellsAtOf_matsOf N M hk a r c
  have h2 : (matsOf X k)[a]? = some ((ownerOf X k E).1, (ownerOf X k E).2, E.ttOff) := by
    rw [← O k hk]
    unfold matsOwn
    rw [List.getElem?_map, Array.getElem?_toList, hE]
    rfl
  unfold cellsAtOf at h1
  rw [h2] at h1
  obtain ⟨z, hz, e⟩ := OnBytes.HonestTrace.cellOf_int X T M.small (ownerOf X k E).1
    (ownerOf X k E).2 r (E.ttOff + c)
  have h3 : signedOf (cellOf X T (ownerOf X k E).1 (ownerOf X k E).2 r (E.ttOff + c)) = T k a r c :=
    h1
  rw [e, OnBytes.HonestTrace.signedOf_cast z hz] at h3
  rw [e, h3]

/-- The reading at a matrix's number is the trace's entry. Conditional on `PlanLabels X`,
`PlanOwners X`, `NamesFit X T`, `MeetsAll X i x T`, k < 25. No instance of these hypotheses is
exhibited in this file. -/
theorem atOwn_cellOf (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T)
    (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25) (a r c : ℕ) :
    atOwn X (cellOf X T) k a r c = ((T k a r c : ℤ) : Cb.Gl.E) := by
  unfold atOwn
  cases hE : (tlOf X k).mats[a]? with
  | none =>
    have hl : labelAt X k a = none := by
      rw [← B.names k hk a]
      unfold nameAt
      rw [hE]
      rfl
    rw [N.beyond k hk a r c hl]
    simp
  | some E =>
    show algebraMap Cb.Gl.F Cb.Gl.E
      (cellOf X T (ownerOf X k E).1 (ownerOf X k E).2 r (E.ttOff + c)) = _
    rw [cellOf_owner O N M hk hE r c]
    exact map_intCast _ _

/-- It is the reading by labels under the link's own number. -/
theorem atOwn_atNo (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T)
    (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25) (a r c : ℕ) :
    atOwn X (cellOf X T) k a r c = atNo X (cellOf X T) k a r c := by
  rw [atOwn_cellOf B O N M hk, OnBytes.HonestTrace.atNo_cellOf N hk]

/-- **A group's layers: the two readings are one.** Conditional on `PlanLabels X`, `PlanOwners X`,
`NamesFit X T`, `MeetsAll X i x T`, g < 12. No instance of these hypotheses is exhibited in this
file. -/
theorem ownG_eq (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) :
    ownG X (cellOf X T) (entryOf i) (linkG X g) = fromG X (cellOf X T) (entryOf i) g := by
  have e : linkG X g = 2 * g := by unfold linkG; rw [step_full B]
  rw [e]
  funext n
  cases n with
  | cell a r c => exact atOwn_atNo B O N M (by omega) a r c
  | w r c => rfl

/-- **A group's attention.** Conditional on the same. No instance of these hypotheses is exhibited
in this file. -/
theorem ownA_eq (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) :
    ownA X (cellOf X T) (linkA X g) = fromA X (cellOf X T) g := by
  have e : linkA X g = 2 * g + 1 := by unfold linkA; rw [step_full B]
  rw [e]
  funext n
  exact atOwn_atNo B O N M (by omega) n.M n.r n.c

/-- **The head.** Conditional on the same. No instance of these hypotheses is exhibited in this
file. -/
theorem ownH_eq (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T) :
    ownH X (cellOf X T) (entryOf i) (linkH X) = fromH X (cellOf X T) (entryOf i) := by
  have e : linkH X = 24 := by unfold linkH; rw [step_full B, B.groups]
  rw [e]
  funext n
  cases n with
  | cell a r c => exact atOwn_atNo B O N M (by omega) a r c
  | w r c => rfl

/-- **ZZ is the full size's**, at every reader of cells and every sampled matrix. Conditional on
`PlanLabels X`, `PlanOwners X`, k < 25. No instance of these hypotheses is exhibited in this file.
-/
theorem zzOwn_eq (B : PlanLabels X) (O : PlanOwners X) {k : ℕ} (hk : k < 25) (C : Cells)
    (ts : List Int) : zzOwn X k C ts = zzFull X k C ts := by
  unfold zzOwn zzFull
  rw [O k hk, tlOf_eq B]

/-- **The keys and bits of a group's layers, at the filling's own term, are honest.** Conditional on
`PlanLabels X`, `PlanOwners X`, `NamesFit X T`, `LookPub X`, `MeetsAll X i x T`,
`PlanesLaid X i x T`, g < 12: at the full size alone. No instance of these hypotheses is exhibited
in this file. -/
theorem ownG_meets {W₀ Xi Tr' : Type} (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T)
    (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) :
    ((ownSources X cells weights pubH).layers g ⟨cellOf X T⟩ ⟨entryOf i⟩).Meets X.y.fo X.y.h.lmb :=
      by
  have e : (ownSources X cells weights pubH).layers g ⟨cellOf X T⟩ ⟨entryOf i⟩ =
      lookG X g ⟨cellOf X T⟩ ⟨entryOf i⟩ := by
    show (⟨fun theta n => OnBytes.Ends.G.keyG X.layers g
        (ownG X (cellOf X T) (entryOf i) (linkG X g)) theta n,
      fun u j => OnBytes.Ends.G.bitsG X.y (ownG X (cellOf X T) (entryOf i) (linkG X g))
        (u * 32 + j)⟩ : LookIn) = _
    rw [ownG_eq B O N M hg]
    rfl
  rw [e]
  exact lookG_meets N Q M L hg

/-- **A group's attention.** Conditional on the same: at the full size alone. No instance of these
hypotheses is exhibited in this file. -/
theorem ownA_meets {W₀ Xi Tr' : Type} (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T)
    (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) :
    ((ownSources X cells weights pubH).attention g ⟨cellOf X T⟩).Meets (fsAt X g)
      (Hd.shapeA X g).cf.lmb := by
  have e : (ownSources X cells weights pubH).attention g ⟨cellOf X T⟩ = lookA X g ⟨cellOf X T⟩ := by
    show (⟨fun theta n => OnBytes.Ends.A.keyA (Hd.shapeA X g) (fsAt X g)
        (ownA X (cellOf X T) (linkA X g)) theta n,
      fun u j => OnBytes.Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (ownA X (cellOf X T) (linkA X g))
        (u * 32 + j)⟩ : LookIn) = _
    rw [ownA_eq B O N M hg]
    rfl
  rw [e]
  exact lookA_meets N Q M L hg

/-- **The head**, at a letter that yields the trace's files' structure at the request. Conditional
on the same, and on pubH y = pubHAt X x: at the full size alone. No instance of these hypotheses is
exhibited in this file.
Limit: `hy` is not shown of the filling that reads the request by `reqAt` (Honest/K3/WitReq.lean).
There the head's public data are `headPub X` of what `reqAt` returns: another term than
`pubHAt X x`, and the equality of the two is not shown. At that filling a sentence of the same kind
(`Meets`, at the row's own witness) is had without `hy`:
`honestKeysAndBitsAtTheHead` (Honest/K3/Term/LookupDataAtTheHonestTrace.lean), over
`headKeysAtTheRequest` (Honest/K3/Term/HeadPublicDataAgree.lean): the keys are the same at both. -/
theorem ownH_meets {W₀ Xi Tr' : Type} (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T)
    (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (y : Xi)
    (hy : pubH y = pubHAt X x) :
    ((ownSources X cells weights pubH).head y ⟨cellOf X T⟩ ⟨entryOf i⟩).Meets X.HLy.fs X.hS.lmbH :=
      by
  have e : (ownSources X cells weights pubH).head y ⟨cellOf X T⟩ ⟨entryOf i⟩ =
      lookH X (pubHAt X x) ⟨cellOf X T⟩ ⟨entryOf i⟩ := by
    show (⟨fun theta n => OnBytes.Ends.H.keyH (pubH y)
        (ownH X (cellOf X T) (entryOf i) (linkH X)) theta n,
      fun u j => OnBytes.Ends.H.bitsH (pubH y).h (pubH y).L.fs
        (ownH X (cellOf X T) (entryOf i) (linkH X)) (u * 32 + j)⟩ : LookIn) = _
    rw [ownH_eq B O N M, hy]
    rfl
  rw [e]
  exact lookH_meets N Q M L

end

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.cellOf_owner
#print axioms ProofFile.Honest.K3.atOwn_cellOf
#print axioms ProofFile.Honest.K3.atOwn_atNo
#print axioms ProofFile.Honest.K3.ownG_eq
#print axioms ProofFile.Honest.K3.ownA_eq
#print axioms ProofFile.Honest.K3.ownH_eq
#print axioms ProofFile.Honest.K3.zzOwn_eq
#print axioms ProofFile.Honest.K3.ownG_meets
#print axioms ProofFile.Honest.K3.ownA_meets
#print axioms ProofFile.Honest.K3.ownH_meets
