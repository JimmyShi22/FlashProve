-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/CarriedHold.lean: THE CLAIM THAT A CODE SWITCH CARRIES OVER SAYS TRUE
OF THE HONEST NEW MESSAGES, where the claim in front is true of what the fold left (`ClaimTrue`,
Inner/Statement.lean). Statements and proofs.

  `worthOf_zero`, `worthOf_list`   the worth of no piece; of a list of pieces
  `fold_addKept`    the coefficients of a row to which forms on kept members were carried over
  `Lists.mapM_mem`        a loop that can fail: its length, and entry by entry
  `place_at`        the entry that the program's search finds for a kept form
  `keptShare`, `worth_share`   one kept form's share of the claim, as `ClaimTrue` writes it; the
                    form carried over is worth it
  `carried_pieces`  the carried row's coefficients, piece by piece
  `mask_term`       a written vector on a mask row's message
  `carried_holds`   the carried row says true

By: `switchCarried_iff` (Johnson/Top/H0/K2Hands/RowsOrder.lean); `addKept_add`, `map_zip_fst`
(Johnson/Top/H0/K2Hands/ClaimJoin.lean); `coefAt_restE_at` (OnBytes/Slice/BlkCsStretch.lean);
Inner/KeptRows.lean, Inner/GenRows.lean.

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.KeptRows
import Johnson.Top.H0.K2Hands.ClaimJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE readE readV coefAt formAt stretchAt)
open OnBytes.Means (Words Says value)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc.First.K2Hands (placeOf carriedOf)
open Finset (range)

theorem worthOf_zero (S : Statement) (w : Words GE) (g : Nat) (anew : Array Nat) :
    worthOf S w g anew (fun _ _ _ => 0) = 0 := by
  unfold worthOf
  simp

/-- The worth of a list of pieces. -/
theorem worthOf_list {α : Type} (S : Statement) (w : Words GE) (g : Nat) (anew : Array Nat)
    (κ : α → Nat → Part → Nat → GE) : ∀ l : List α,
    worthOf S w g anew (fun o p J => (l.map fun x => κ x o p J).sum) =
      (l.map fun x => worthOf S w g anew (κ x)).sum
  | [] => worthOf_zero S w g anew
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [worthOf_add S w g anew (κ x) (fun o p J => (l.map fun x => κ x o p J).sum),
      worthOf_list S w g anew κ l]

/-- The coefficients of a row to which forms on kept members were carried over. -/
theorem fold_addKept (Fr : SwitchFrame) (o : Nat) (p : Part) (J : Nat) :
    ∀ (l : List (KeptForm × KeptPlace)) (r : OnBytes.Row),
    coefAt (l.foldl (fun (r : OnBytes.Row) x => Fr.addKept r x.2 x.1.c) r) o p J =
      coefAt r o p J + (l.map fun x => coefAt (Fr.addKept {} x.2 x.1.c) o p J).sum
  | [], r => by simp
  | x :: l, r => by
    rw [List.foldl_cons, fold_addKept Fr o p J l, List.map_cons, List.sum_cons,
      VerifiableInference.Desc.First.K2Hands.addKept_add, add_assoc]

/-- A loop that can fail, entry by entry. -/
theorem Lists.mapM_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (ks : List β),
    l.mapM f = some ks → ks.length = l.length ∧ ∀ x ∈ l.zip ks, f x.1 = some x.2
  | [], ks, h => by
    have : ks = [] := by simpa using h.symm
    subst this
    simp
  | a :: l, ks, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | none => rw [hl] at h; cases h
      | some bs =>
        rw [hl] at h
        have e : ks = b :: bs := (Option.some.inj h).symm
        subst e
        obtain ⟨h1, h2⟩ := Lists.mapM_mem f l bs hl
        refine ⟨by simp [h1], ?_⟩
        intro x hx
        rw [List.zip_cons_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact h2 x hx

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- The entry that the program's search finds for a kept form. -/
theorem place_at {Fr : SwitchFrame} (f : KeptForm) (k : KeptPlace) (h : placeOf Fr f = some k) :
    k.old = f.oracle ∧ ∃ a : Nat, Fr.kept[a]? = some k := by
  unfold placeOf at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨by simpa using h1, List.mem_iff_getElem?.1 h2⟩

/-- One kept form's share of the claim, as `ClaimTrue` writes it. -/
def keptShare (Z : Sizes) (old : SingleRows) (W : Left) (f : KeptForm) : GE :=
  match (switchKept old).toList.idxOf? f.oracle with
  | some a =>
    ∑ i ∈ range
        (2 ^ (ceilLog2 (Z.kept.getD a {}).mainRows + (Z.codes.base.getD Z.code default).logEll)),
      formAt f.c i * (W.kept a).entryIn (Z.kept.getD a {}) i
  | none => 0

/-- A kept form carried over is worth its share of the claim. -/
theorem worth_share (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (f : KeptForm) (k : KeptPlace)
    (h : placeOf Fr f = some k) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew (coefAt (Fr.addKept {} k f.c)) =
      keptShare (sizesAt S old T) old W f := by
  obtain ⟨ho, a, hk⟩ := place_at f k h
  obtain ⟨s, _, hs, _, _, _, _, _, e5, e6, e7⟩ := kept_at hFr a k hk
  have hidx := Lists.idxOf_at _ a k.old A.fits.once e6
  have hget : (sizesAt S old T).kept.getD a {} = s := by
    rw [List.getD_eq_getElem?_getD, hs]
    rfl
  rw [worth_addKept A hFr a k hk]
  unfold keptShare
  rw [← ho, hidx]
  show _ = ∑ i ∈ range (2 ^ (ceilLog2 ((sizesAt S old T).kept.getD a {}).mainRows +
    (S.codes.base.getD old.code default).logEll)),
      formAt f.c i * (W.kept a).entryIn ((sizesAt S old T).kept.getD a {}) i
  rw [hget, e5, ← e7]

/-- The carried row's coefficients, piece by piece. -/
theorem carried_pieces (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (ks : List KeptPlace) :
    coefAt (carriedOf Fr old ks) = fun o p J =>
      ((liftPiece S old T g old.c o p J +
        ((old.kept.toList.zip ks).map fun x => coefAt (Fr.addKept {} x.2 x.1.c) o p J).sum) +
        stretchPiece S T g ((switchParts S old).maskAt.getD 0 0) (old.d.getD 0 #[]).size
          (readV (old.d.getD 0 #[])) o p J) +
        stretchPiece S T g ((switchParts S old).maskAt.getD 1 0) (old.d.getD 1 #[]).size
          (readV (old.d.getD 1 #[])) o p J := by
  have I := frameIs hFr
  funext o p J
  have hinc := fun a n =>
    VerifiableInference.Desc.First.K2Hands.places_inc S old T g anew Fr hFr A.check a n
  have e : coefAt (carriedOf Fr old ks) o p J =
      coefAt (switchAddRestE (switchAddRestE
        ((old.kept.toList.zip ks).foldl (fun (r : OnBytes.Row) x => Fr.addKept r x.2 x.1.c)
          (({} : OnBytes.Row).addForm Fr.g
            (switchLift old.c Fr.code.logEll Fr.mainCut Fr.rowBits Fr.tableBits)))
        Fr.g Fr.restPart
        (switchPieces Fr.places (Fr.parts.maskAt.getD 0 0) (old.d.getD 0 #[]).size)
        (old.d.getD 0 #[]))
        Fr.g Fr.restPart
        (switchPieces Fr.places (Fr.parts.maskAt.getD 1 0) (old.d.getD 1 #[]).size)
        (old.d.getD 1 #[])) o p J := by
    unfold carriedOf
    rw [A.target.masks]
    rfl
  rw [e, OnBytes.Slice.coefAt_restE_at _ _ _ _ _ _ (hinc _ _),
    OnBytes.Slice.coefAt_restE_at _ _ _ _ _ _ (hinc _ _), fold_addKept,
    OnBytes.Slice.coefAt_addForm, OnBytes.Slice.coefAt_empty, zero_add, I.gIs, I.restPart,
    I.places, I.parts, I.code, I.mainCut, I.rowBits, I.tableBits]
  rfl

/-- A written vector on a mask row's message. -/
theorem mask_term (A : AtSwitch S old T g anew W V) (j : Nat) (hj : j < 2)
    (hd : (old.d.getD j #[]).size ≤ (S.codes.mask.getD old.maskCode default).ell) :
    ∑ i ∈ range (old.d.getD j #[]).size, readV (old.d.getD j #[]) i *
        (rest (sizesAt S old T) W).getD ((switchParts S old).maskAt.getD j 0 + i) zeroG =
      ∑ i ∈ range (S.codes.mask.getD old.maskCode default).ell,
        readE ((old.d.getD j #[]).getD i zeroE) * W.mask j i := by
  have R := (restIsParts S old T W A.target.masks A.fits).2.1
  have h1 : ∑ i ∈ range (old.d.getD j #[]).size, readV (old.d.getD j #[]) i *
        (rest (sizesAt S old T) W).getD ((switchParts S old).maskAt.getD j 0 + i) zeroG =
      ∑ i ∈ range (old.d.getD j #[]).size,
        readE ((old.d.getD j #[]).getD i zeroE) * W.mask j i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← R j i hj (Nat.lt_of_lt_of_le (Finset.mem_range.1 hi) hd)]
    rfl
  rw [h1]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.2 (Nat.lt_of_lt_of_le (Finset.mem_range.1 hi) hd)
  · intro i _ hn
    have hge : (old.d.getD j #[]).size ≤ i :=
      Nat.le_of_not_lt fun h => hn (Finset.mem_range.2 h)
    have hz : (old.d.getD j #[]).getD i zeroE = zeroE := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge]
      rfl
    rw [hz, OnBytes.Slice.readE_zero, zero_mul]

/-- **The carried row.** -/
theorem carried_holds (A : AtSwitch S old T g anew W V)
    (hn : ∀ o ∈ anew.toList, o < S.oracles.size) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (ks : List KeptPlace)
    (hks : old.kept.toList.mapM (placeOf Fr) = some ks)
    (hc : ClaimTrue (sizesAt S old T) old W) :
    Says rdE S (carriedOf Fr old ks) (newWords (sizesAt S old T) g anew V) := by
  obtain ⟨hlen, hmem⟩ := Lists.mapM_mem _ _ _ hks
  have f0 := (mask_fits A 0 (by omega)).1
  have f1 := (mask_fits A 1 (by omega)).1
  have d0 := A.fits.d0
  have d1 := A.fits.d1
  have h1 := value_worth A hn (carriedOf Fr old ks)
  rw [carried_pieces A hFr ks,
    worthOf_add S _ g anew (fun o p J => (liftPiece S old T g old.c o p J +
        ((old.kept.toList.zip ks).map fun x => coefAt (Fr.addKept {} x.2 x.1.c) o p J).sum) +
        stretchPiece S T g ((switchParts S old).maskAt.getD 0 0) (old.d.getD 0 #[]).size
          (readV (old.d.getD 0 #[])) o p J),
    worthOf_add S _ g anew (fun o p J => liftPiece S old T g old.c o p J +
        ((old.kept.toList.zip ks).map fun x => coefAt (Fr.addKept {} x.2 x.1.c) o p J).sum),
    worthOf_add S _ g anew (liftPiece S old T g old.c),
    worth_liftPiece A _ A.fits.mainVars,
    worthOf_list S _ g anew (fun x : KeptForm × KeptPlace => coefAt (Fr.addKept {} x.2 x.1.c)),
    worth_stretchPiece A _ _ _ (by omega), worth_stretchPiece A _ _ _ (by omega),
    mask_term A 0 (by omega) d0, mask_term A 1 (by omega) d1] at h1
  have hk : ((old.kept.toList.zip ks).map fun x =>
      worthOf S (newWords (sizesAt S old T) g anew V) g anew
        (coefAt (Fr.addKept {} x.2 x.1.c))).sum =
      (old.kept.toList.map (keptShare (sizesAt S old T) old W)).sum := by
    rw [← VerifiableInference.Desc.First.K2Hands.map_zip_fst (keptShare (sizesAt S old T) old W)
      old.kept.toList ks (by omega)]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact worth_share A hFr x.1 x.2 (hmem x hx)
  rw [hk] at h1
  have h2 := hc.2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h2
  have htg : rdE.val (carriedOf Fr old ks).target = readE old.target := rfl
  unfold Says
  rw [h1, htg, ← h2, add_assoc]
  rfl

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.worth_share
#print axioms VerifiableInference.Desc.K2.Honest.carried_holds
