-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ObjectGuards.lean: guards and ties for E2E/ObjectAtFiles.lean, E2E/WholeView.lean and
E2E/WholeViewTables.lean: small facts without which their statements could hold for a silly reason,
or be about another object than a reader takes them for.

What is shown.
  `ownProvers_silent`: the provers that the library lays into the object from which `VerifierAndGoals.verify`
    is compiled are the placeholder provers (`Files.fixedMessageProvers`). So `objAt Z (filesAt Z).fixedMessageProvers`, of
    which E2E/WholeViewTables.lean speaks, differs from that object in the index type alone.
  `v_objAt`: the verifier's side of `objAt Z P` is that of the library's own object, for every P.
  `conf_D_inRange`, `dec_cutObj_eq_none`, `dec_objAt_eq_none`: the library's decoder returns
    matrices in range alone, so the cut decoder says "none" only where the library's does.
  `ixOf`, `ixOf_injective`: every index of the integer model gives a matrix in range, and two
    indices give two matrices.
  `ix_two`: the matrices in range have two different members (all entries 0; one entry 1).
  `course_fits`: the bounds of the protocol's course fit the numbers 44,040,191 | 62 | 62 | 62 | 64:
    one run of the key file's protocol, on the first table; c copies, each with one link; s batches
    on each copy and none on the first table; no single reads; for c ≤ 710,324 and s ≤ 688,127.
  `course_copies_tight`, `course_batches_tight`: both numbers are tight: 710,325 copies, or 688,128
    batches on a copy, do not fit.
  `crowded_does_not_fit`: bounds that lay a run of the key file's protocol, a link and 688,127
    batches on one copy do not fit.

Limits. Two members are few: how many matrices are in range is not counted here. That the two named
matrices are weights of any use is not said.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.WholeViewTables

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles (Flat.matrixOf Flat.holds_matrixOf)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

/-! ## 1. The library's own provers -/

/-- The provers that the library lays at Z. -/
def ownProvers (Z : PublicFiles) : (filesAt Z).Provers := (dataAtFiles flashProveData Z).P

/-- **They are the placeholder provers.** -/
theorem ownProvers_silent (Z : PublicFiles) : ownProvers Z = (filesAt Z).fixedMessageProvers := rfl

/-- **The verifier's side of `objAt Z P` is that of the library's own object, for every P**: word
length, symbols, OOD seeds and answers, the three protocols, the number of requests in a batch,
`early`, `late` (`HolographicProtocol.v`, Hiop/RecSide.lean). -/
theorem v_objAt (Z : PublicFiles) (P : (filesAt Z).Provers) :
    (objAt Z P).v = ((filesAt Z).withProvers (ownProvers Z)).v := rfl

open Classical in
/-- The index decoder of a committed table's configuration returns matrices in range alone. -/
theorem conf_D_inRange {D : OnBytes.Slice.DecR} {X : Type} (A : D.Claims X) (R : D.RelationsAndEncoding A)
    (y : Fin (2 ^ D.T.a) → Run.PQ.SgX) (rec : D.Rec) (M : A.Mat)
    (h : (OnBytes.Slice.DecR.configurationOfStoredTable A R).D y rec = some M) : A.inRange M := by
  rw [OnBytes.Slice.DecR.conf_D] at h
  by_cases hc : D.coll y rec.1
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    obtain ⟨u, _, hu⟩ := Option.bind_eq_some_iff.1 h
    have hu' : (if A.inRange (A.mat u) then some (A.mat u) else none) = some M := hu
    by_cases hr : A.inRange (A.mat u)
    · rw [if_pos hr] at hu'
      exact Option.some.inj hu' ▸ hr
    · rw [if_neg hr] at hu'
      cases hu'

/-- **The cut loses nothing of the decoder**: at `cutObj F P` it says "none" only where the
library's does. -/
theorem dec_cutObj_eq_none {X : Type} {pp : Inst.Model.ScalesAndPolicy}
    {req : X → Inst.Model.Instance Inst.Model.ppref} (F : Files (ConfAt pp req)) (P : F.Provers)
    (y : Fin (F.withProvers P).wordLength → (F.withProvers P).Symbol) (rec : (F.withProvers P).Rec) :
    (cutObj F P).decodeIndex y rec = none ↔ (F.withProvers P).decodeIndex y rec = none :=
  dec_cut_eq_none (I := FullSizeMatrix) (X := X) (F.withProvers P) inRange
    (fun y rec M h =>
      conf_D_inRange
        (OnBytes.Flat.claimsLedgerOnAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
          VerifiableInference.OnPublicFiles.numsRef pp req)
        (OnBytes.Flat.relationsAndEncodingOfClaims _
          (OnBytes.Flat.codingCells OnBytes.Slice.frS OnBytes.Slice.frZ 402653181
            VerifiableInference.OnPublicFiles.numsRef pp req)) y rec M h) y rec

theorem dec_objAt_eq_none (Z : PublicFiles) (P : (filesAt Z).Provers)
    (y : Fin ((filesAt Z).withProvers P).wordLength → ((filesAt Z).withProvers P).Symbol) (rec : ((filesAt Z).withProvers P).Rec) :
    (objAt Z P).decodeIndex y rec = none ↔ ((filesAt Z).withProvers P).decodeIndex y rec = none :=
  dec_cutObj_eq_none (filesAt Z) P y rec

/-! ## 2. The matrices in range -/

/-- The matrix of an index of the integer model, as a member of the matrices in range. -/
def ixOf (i : Cm.Idx) : Ix := ⟨Flat.matrixOf i, i, Flat.holds_matrixOf i⟩

/-- **Two indices give two matrices.** -/
theorem ixOf_injective : Function.Injective ixOf := fun i i' h => by
  have e : Flat.matrixOf i = Flat.matrixOf i' := congrArg Subtype.val h
  have h' := Flat.holds_matrixOf i'
  rw [← e] at h'
  exact VerifiableInference.OnPublicFiles.Flat.holds_unique le_rfl le_rfl (Flat.holds_matrixOf i) h'

/-- A matrix of the index's shape with entries 0 and 1 alone is well formed. -/
theorem wfw_of_bits (M : Cm.Shape) (h : ∀ y c, M y c = 0 ∨ M y c = 1) :
    Inst.Model.Layout.WFW Inst.Model.ppref kRef (Cm.ext M) hRef := by
  have e : ∀ y c, 0 ≤ Cm.ext M y c ∧ Cm.ext M y c ≤ 1 := by
    intro y c
    unfold Cm.ext
    split
    · rename_i hh
      rcases h ⟨y, hh.1⟩ ⟨c, hh.2⟩ with h0 | h0 <;> rw [h0] <;> constructor <;> norm_num
    · constructor <;> norm_num
  have key : ∀ r r' c, -2 ^ 12 ≤ Cm.ext M r c + 256 * Cm.ext M r' c ∧
      Cm.ext M r c + 256 * Cm.ext M r' c < 2 ^ 12 := fun r r' c => by
    have a := e r c
    have b := e r' c
    constructor <;> omega
  exact ⟨fun y _ c _ => ⟨by have a := e y c; omega, by have a := e y c; omega⟩,
    fun _ _ _ _ _ _ _ c _ => key _ _ c⟩

/-- The index with all entries 0. -/
def idxA : Cm.Idx := ⟨fun _ _ => 0, wfw_of_bits _ fun _ _ => Or.inl rfl⟩

/-- The index with the entry 1 in row 0, column 0, and 0 elsewhere. -/
def idxB : Cm.Idx :=
  ⟨fun y c => if y.val = 0 ∧ c.val = 0 then 1 else 0, wfw_of_bits _ fun y c => by
    by_cases h : y.val = 0 ∧ c.val = 0
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)⟩

theorem idxA_ne_idxB : idxA ≠ idxB := fun h => by
  have e : idxA.val ⟨0, by decide +kernel⟩ ⟨0, Nat.two_pow_pos _⟩ =
      idxB.val ⟨0, by decide +kernel⟩ ⟨0, Nat.two_pow_pos _⟩ := by rw [h]
  have e' : (0 : ℤ) = 1 := e
  norm_num at e'

/-- **The matrices in range have two different members.** -/
theorem ix_two : ∃ i i' : Ix, i ≠ i' :=
  ⟨ixOf idxA, ixOf idxB, fun h => idxA_ne_idxB (ixOf_injective h)⟩

/-! ## 3. The budget -/

/-- The bounds of the protocol's course: c copies, s batches on each copy. -/
def courseB (c s shown : ℕ) : BoundsR where
  nenc := c
  tests := fun e => if e = 0 then 1 else 0
  links := fun e => if e = 0 then 0 else 1
  sess := fun e => if e = 0 then 0 else s
  reads := fun _ => 0
  shown := shown

theorem sum_links (c : ℕ) :
    ∑ j ∈ Finset.range (c + 1), (if j = 0 then 0 else 1 : ℕ) = c := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp

/-- **The protocol's course fits**, up to 710,324 copies and 688,127 batches a copy. -/
theorem course_fits (c s shown : ℕ) (hc : c ≤ 710324) (hs : s ≤ 688127) :
    (courseB c s shown).Fits 44040191 62 62 62 64 := by
  intro e _
  have hsum : (courseB c s shown).sum (courseB c s shown).links = c := sum_links c
  rw [hsum]
  by_cases h0 : e = 0
  · subst h0
    simp only [courseB, if_true]
    omega
  · simp only [courseB, if_neg h0]
    omega

/-- **A copy on which the key file's protocol is run as well does not fit** at 688,127 batches. -/
theorem crowded_does_not_fit :
    ¬ (⟨1, fun _ => 1, fun e => if e = 0 then 0 else 1, fun e => if e = 0 then 0 else 688127,
      fun _ => 0, 1⟩ : BoundsR).Fits 44040191 62 62 62 64 := fun h => by
  have h1 := h 1 le_rfl
  simp at h1

/-- **The first number is tight**: with 710,325 copies the first table's budget is passed. -/
theorem course_copies_tight (s shown : ℕ) :
    ¬ (courseB 710325 s shown).Fits 44040191 62 62 62 64 := fun h => by
  have h0 := h 0 (Nat.zero_le _)
  have hsum : (courseB 710325 s shown).sum (courseB 710325 s shown).links = 710325 :=
    sum_links 710325
  rw [hsum] at h0
  simp only [courseB, if_true] at h0
  omega

/-- **The second number is tight**: with 688,128 batches on a copy that copy's budget is passed. -/
theorem course_batches_tight (c shown : ℕ) (hc : 1 ≤ c) :
    ¬ (courseB c 688128 shown).Fits 44040191 62 62 62 64 := fun h => by
  have h1 := h 1 hc
  have h10 : ¬ (1 : ℕ) = 0 := by decide
  simp only [courseB, if_neg h10] at h1
  omega

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.course_copies_tight
#print axioms AtPublicFiles.AtFiles.course_batches_tight
#print axioms AtPublicFiles.AtFiles.ownProvers_silent
#print axioms AtPublicFiles.AtFiles.v_objAt
#print axioms AtPublicFiles.AtFiles.conf_D_inRange
#print axioms AtPublicFiles.AtFiles.dec_cutObj_eq_none
#print axioms AtPublicFiles.AtFiles.dec_objAt_eq_none
#print axioms AtPublicFiles.AtFiles.ixOf_injective
#print axioms AtPublicFiles.AtFiles.ix_two
#print axioms AtPublicFiles.AtFiles.course_fits
#print axioms AtPublicFiles.AtFiles.crowded_does_not_fit
