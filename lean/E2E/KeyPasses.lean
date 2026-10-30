--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPasses.lean: FOUR PUBLIC TESTS OF THE KEY FILE's IOP AS WRITTEN IN LEAN (below: the
description) THAT NO PART OF A PROVER PLAYS, each from a theorem that the library has already:
calls, and the ties of variables that the calls want. Statements and proofs. These are single tests
of the verifier's: NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on what a view shows.

What is shown.
  **`okStart_named`**: THE TEST ON THE INSTANCE ACCEPTS THE WRITTEN KEY OF EVERY OOD SAMPLE: for X,
    N, P with `KeyNamed Z X N P` (E2E/KeyProtocolOverDescription.lean), where Z is in scope. By the library's
    `okStart_in_scope` (Johnson/RunOne/Law/OkStartInScope.lean). The sample is not read: the test
    hangs on three numbers of the table's shape. `okStart_pulled`: the same of the description
    pulled back to OOD samples.
  `Passes m p k`: the three tests that the rows on the table ask of the claim k on the keys of a
    lookup's part p: the point's length; no weight has a written-out factor; THE WEIGHTS ADD UP TO
    THE SUM OF THE EQUALITY VECTOR OVER THE PLACES THAT THE PART's RUNS COVER.
  **`passes_keysOf`**: they accept the claim that the lookup itself makes (`Lkp.keysOf` at
    `Wf.lookupOf`), AT EVERY POINT of the right length and all θ, α: by the library's
    `Wf.Proved.pendOkKeys` (OnBytes/Tie/Pv/Lookup/PendOkKeys.lean). The third test reads field
    values that are made of challenges.
  `tableRowsOf_of_passes`: where each part's claim passes, the rows on the table of that lookup are
    made (`Key.tableRowsOf` returns).
  `takenSources_passes`: the sub-protocol without a round "the taken trees' sources" accepts and
    hands its state on as it is, where the library's `Third.Law.Tied` holds of that state: one
    direction of the library's `takenSources_exact`.
  `fin_eq`, **`fin_of_shape`**: the description's last test is `firstEndOk` of the first chain's
    last state and `fin₃` of the third's; the first follows from the library's test `shape₁` on that
    state's book-keeping at its border 19 (`finD_of_shape`, Johnson/RunOne/KeyTenAt.lean).

THE DIRECTION. The library's laws on the sub-protocols without a round say what an accepting step
GIVES ("the book-keeping in front and the step's acceptance give the book-keeping behind"). An
honest run wants the other direction: the book-keeping in front GIVES the acceptance. The four here
are cases in which the library has that direction. That there is no fifth is not claimed.

Limits.
- `passes_keysOf` speaks of `Lkp.keysOf`'s value. That the claims which the first chain's state
  holds when the rows are laid ARE such values, at the lookup's own θ and α, is not shown here. Its
  three premises on the parameters (`lookupOk`, `m.ok`, `fitsMatrix`) are shown at no public file
  here.
- `takenSources_passes` and `fin_of_shape` are conditional: that `Tied`, `shape₁` at border 19 and
  `fin₃` hold of the states of a run is not shown.
- `shape₁` is taken at the library's own variables (`plan₁`, `readers₁`, `book₁`, `slots₁` of the
  one-time chain's public values).
- "In scope" is a test on the public files; that it accepts any files is not shown here.


-/
import E2E.KeyProtocolOverDescription
import Johnson.RunOne.Law.OkStartInScope
import OnBytes.Tie.Pv.Lookup.PendOkKeys
import Johnson.Desc.Third.Law.Sources
import Johnson.RunOne.KeyTenAt
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Flat (RecFull)
open OnBytes.Params (WfLookup WfPart)
open VerifiableInference.Desc (FileDescription Block)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample descriptionFromPlan descAt sourceOf tableRowsOf firstEndOk)
open VerifierAndGoals (PublicFiles)

/-! ## 1. The test on the instance -/

/-- **The test on the instance accepts the written key of every OOD sample**, in scope. -/
theorem okStart_named {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hn : KeyNamed Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (rec : RecFull) :
    (keyFileDescription X N P).okStart (keyInstanceOfOutOfDomainSample rec) = true := by
  obtain ⟨X₀, m, h0, hm, hd, -⟩ := hn.named
  have hd' : descriptionFromPlan m = .ok (keyFileDescription X N P) := by
    unfold descAt at hd
    rw [hm] at hd
    exact hd
  obtain ⟨X', N', P', hX, -, -, e₀⟩ := VerifiableInference.Desc.Key.descOfMade_is m _ hd'
  have e : keyFileDescription X N P = keyFileDescription X' N' P' := e₀
  have hp : (keyFileDescription X' N' P').planOk = true := by
    rw [← e]
    exact hn.plan
  rw [e]
  exact Johnson.RunOne.Law.OkStartInScope.okStart_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hp rec

/-- A pulled-back description's test on the instance is the description's, behind the map: by
unfolding. -/
theorem pull_okStart {Xi Y : Type} (F : FileDescription Xi) (f : Y → Xi) (y : Y) :
    (F.pull f).okStart y = F.okStart (f y) := rfl

/-- The same of the description pulled back to OOD samples. -/
theorem okStart_pulled {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hn : KeyNamed Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (rec : RecFull) :
    ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample).okStart rec = true :=
  (pull_okStart (keyFileDescription X N P) keyInstanceOfOutOfDomainSample rec).trans (okStart_named hn scope rec)

/-! ## 2. The rows on the table -/

/-- The three tests on the claim k on the keys of the part p. -/
def Passes (m : Wf.Matrix) (p : WfPart) (k : Lkp.Keys) : Bool :=
  k.point.length == m.kCol + p.logPlaces && k.weights.tensors.all (·.denseVars.isEmpty) &&
    Wf.sumOfForm k.weights == Wf.coveredSum p (Wf.eqPlaces m k.point)

/-- **They accept the claim that the lookup itself makes, at every point of the right length.** -/
theorem passes_keysOf (fBits messageId : Nat) (m : Wf.Matrix) (l : WfLookup) (i : Nat) (p : WfPart)
    (theta alpha : E) (c : PointClaim) (hl : Wf.lookupOk fBits l = true) (hm : m.ok = true)
    (hf : Wf.fitsMatrix m l = true) (hp : l.parts[i]? = some p)
    (hc : c.point.length = m.kCol + p.logPlaces) :
    Passes m p (Lkp.keysOf (Wf.lookupOf messageId m l) theta alpha i c) = true := by
  obtain ⟨h1, h2⟩ := Wf.Proved.pendOkKeys fBits messageId m l i p theta alpha c hl hm hf hp hc
  have h0 : ((Lkp.keysOf (Wf.lookupOf messageId m l) theta alpha i c).point.length ==
      m.kCol + p.logPlaces) = true := beq_iff_eq.2 hc
  unfold Passes
  rw [h0, h1]
  exact h2

/-- A list is mapped through a partial function where every member has a value. -/
theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome = true) → (l.mapM f).isSome = true
  | [], _ => by simp
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a (List.mem_cons_self ..))
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1
      (mapM_isSome f l fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.mapM_cons, hb, hbs]
    rfl

/-- **Where each part's claim passes, the rows on the table of the lookup are made.** -/
theorem tableRowsOf_of_passes (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys)
    (hn : l.parts.length = keys.length)
    (h : ∀ x ∈ l.parts.zip keys, Passes m x.1 x.2 = true) :
    (tableRowsOf m l keys).isSome = true := by
  unfold tableRowsOf
  rw [if_pos (beq_iff_eq.2 hn), zipT_eq]
  refine mapM_isSome _ _ fun x hx => ?_
  have hx' := h x hx
  unfold Passes at hx'
  show (if _ then _ else _ : Option TensorRow).isSome = true
  rw [if_pos hx']
  rfl

/-! ## 3. The taken trees' sources -/

/-- **The sub-protocol without a round accepts, and hands its state on, where the sources are
tied.** -/
theorem takenSources_passes {Cl : Type} (own : Block VerifiableInference.Desc.Third.S₃ Cl)
    (s : VerifiableInference.Desc.Third.S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : VerifiableInference.Desc.Third.Law.Tied own s) :
    (VerifiableInference.Desc.Third.takenSources own).decide s rs gs = .ok s :=
  (VerifiableInference.Desc.Third.Law.takenSources_exact own s rs gs s).2 ⟨rfl, h⟩

/-! ## 4. The last test -/

section Fin
variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- The description's last test, written out: by unfolding. -/
theorem fin_eq (x : KeyInst) (s₁ : (keyFileDescription X N P).S₁) (s₂ : (keyFileDescription X N P).S₂)
    (s₃ : (keyFileDescription X N P).S₃) :
    (keyFileDescription X N P).fin x s₁ s₂ s₃ =
      (firstEndOk X.Y.k.oneTime s₁ && VerifiableInference.Desc.Third.fin₃ s₃) := rfl

open Johnson.RunOne.KeyRows1 in
/-- **The last test accepts where the first chain's last state has the book-keeping of border 19
and the third chain's last state passes `fin₃`.** -/
theorem fin_of_shape (x : KeyInst) (s₁ : (keyFileDescription X N P).S₁) (s₂ : (keyFileDescription X N P).S₂)
    (s₃ : (keyFileDescription X N P).S₃)
    (h₁ : VerifiableInference.Desc.Key.shape₁ (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime)
      (book₁ X.Y.k.oneTime) 2 (slots₁ X.Y.k.oneTime) 19 s₁ = true)
    (h₃ : VerifiableInference.Desc.Third.fin₃ s₃ = true) :
    (keyFileDescription X N P).fin x s₁ s₂ s₃ = true := by
  rw [fin_eq, finD_of_shape X.Y.k.oneTime s₁ h₁, h₃]
  rfl

end Fin

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.okStart_named
#print axioms AtPublicFiles.AtFiles.pull_okStart
#print axioms AtPublicFiles.AtFiles.okStart_pulled
#print axioms AtPublicFiles.AtFiles.passes_keysOf
#print axioms AtPublicFiles.AtFiles.mapM_isSome
#print axioms AtPublicFiles.AtFiles.tableRowsOf_of_passes
#print axioms AtPublicFiles.AtFiles.takenSources_passes
#print axioms AtPublicFiles.AtFiles.fin_eq
#print axioms AtPublicFiles.AtFiles.fin_of_shape
