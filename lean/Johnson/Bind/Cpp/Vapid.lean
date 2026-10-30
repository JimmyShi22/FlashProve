-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Vapid.lean: THE TIE (TieAt, Johnson/Bind/Cpp/Defs.lean) CAN BE MET: some letters
meet it at all public files: THE WRITTEN COMMITTER ITSELF, READ OFF THE TABLE. Three definitions,
five theorems.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.

Why. The theorems of Johnson/Bind/Cpp/OfTie.lean on binding (the opening form, BindsWith: defined in
the head of Johnson/Bind/Cpp/Defs.lean) take the tie at a letter T: at one Z (TieAt T Z), or at all
Z at once (Tie T, the premise of g9bits_cpp; TieLive T, Johnson/Bind/Cpp/AtLive.lean). If no T met
it they would speak of nothing. And a reader should see how little the tie says while T is a letter:
the member that is shown here is no program's and cannot be run.

Main names (namespace Bind.Cpp).
  cellsOfEntries: the matrix of cells that a table's plain entries spell. cellsOfEntries_back: at
    the entries of given weights it is backThe's matrix.
  vapid Z: the written committer read off the table: the letters whose id asks the files' digest c
    and then is the written committer at Z, at that matrix, the table's coins read in the field, and
    the typed salts "c, then the salt bytes". It does not read the three files that it is handed.
  **tie_has_member**: TieAt (vapid Z) Z, at every Z: no premise.
  vapidAll: one pair of letters for all Z: its id is vapid's at the three files that it is handed.
    **tie_has_member_whole**: TieAt vapidAll Z at every Z; so Tie vapidAll (tie_vapidAll).
Limits. IT SHOWS NOTHING OF THE RUNNING COMMITTER: for that see tieAt
(Johnson/Bind/Cpp/TheTie.lean). At these letters the theorems under the tie ALONE
(bindsWith_of_tieAt) say what Johnson/Goal/Conditions/BindsTold.lean says already; those that take
the count as well (bindsAtZ_cpp, g9bits_cpp, the forms in Guards.lean and Extracts.lean) are not
reached: the count (CountAt) is not shown here: the library's bound on the written committer's
queries has a term 2 (K + 1), K the frame's number of blocks (commitAtCoins_within,
Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean).
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.ColumnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
/- The terms beneath are large: Lean's default depth of recursion does not suffice to compare them.
-/
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice

/-- The matrix of cells that a table's plain entries spell. -/
def cellsOfEntries (entry : ℕ → ℕ → UInt64) : Cells (frS.toDecR frZ 402653181) numsRef :=
  cellsOf (frS.toDecR frZ 402653181) numsRef
    (honestMsgs frS fun b => (List.range frS.P.T.l).map (entry b))

/-- At the entries of given weights it is backThe's matrix. -/
theorem cellsOfEntries_back (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    cellsOfEntries (entryOf s w) = backThe Z s w := by
  rw [entryIs Z s w, backThe_eq]
  exact cellWords_mat frS frZ 402653181 numsRef full_fits.1 full_fits.2
    (Flat.matrixOf (idxOf s w)) ⟨idxOf s w, Flat.holds_matrixOf _⟩ (fun _ _ => 0)

/-- The written committer, read off the table. Its generator is a filler (coins of 0, empty salts):
the tie does not read it; at a seed the commit field of theCpp (vapid Z) would. -/
def vapid (Z : PublicFiles) : Letters :=
  ⟨fun _ _ _ _ t => .query (configString Z) fun c =>
      (T₀ Z).commitAtCoins (placeHolderNumberCoins.b₀ Z) (cellsOfEntries t.entry)
        (riOf Z ⟨t.tail, t.pad, t.salt⟩) (saltOf Z c ⟨t.tail, t.pad, t.salt⟩),
    fun _ _ _ _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ => ByteArray.empty⟩⟩

/- From here on Lean compares these by their names: opened, the table's lists have the full size's
lengths. -/
attribute [local irreducible] cellsOfEntries entryOf riOf saltOf T₀ LayoutsByPublicReading.commitAtCoins

/-- Its value at a hash function, at any table. -/
theorem evaluate_vapid (Z : PublicFiles) (sh : Bind.Twin.Shape) (p l K : ByteArray) (t : Bind.Twin.Table)
    (hash : Hash) :
    ((vapid Z).id sh p l K t).evaluate hash =
      ((T₀ Z).commitAtCoins (placeHolderNumberCoins.b₀ Z) (cellsOfEntries t.entry)
        (riOf Z ⟨t.tail, t.pad, t.salt⟩)
        (saltOf Z (hash (configString Z)) ⟨t.tail, t.pad, t.salt⟩)).evaluate hash := rfl

/-- **The tie has a member at every Z.** -/
theorem tie_has_member (Z : PublicFiles) : TieAt (vapid Z) Z := fun s w x b hash => by
  rw [evaluate_vapid]
  show _ = ((T₀ Z).commitAtCoins (placeHolderNumberCoins.b₀ Z) (cellsOfEntries (entryOf s w))
    (riOf Z x) (saltOf Z (hash (configString Z)) x)).evaluate hash
  rw [cellsOfEntries_back Z s w,
    commitAtCoins_filling (T₀ Z) b (placeHolderNumberCoins.b₀ Z) (leaves_R₀ Z)]

/-- One pair of letters for all Z: its id is vapid's at the three files that it is handed. -/
def vapidAll : Letters :=
  ⟨fun sh p l K t => (vapid ⟨p, l, K⟩).id sh p l K t,
    fun _ _ _ _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ => ByteArray.empty⟩⟩

/-- **One member at all Z.** -/
theorem tie_has_member_whole (Z : PublicFiles) : TieAt vapidAll Z := tie_has_member Z

/-- So the tie, whole, has a member. -/
theorem tie_vapidAll : Tie vapidAll := fun Z _ => tie_has_member_whole Z

end Bind.Cpp

end

#print axioms Bind.Cpp.cellsOfEntries_back
#print axioms Bind.Cpp.evaluate_vapid
#print axioms Bind.Cpp.tie_has_member
#print axioms Bind.Cpp.tie_has_member_whole
#print axioms Bind.Cpp.tie_vapidAll
