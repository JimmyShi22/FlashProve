-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedStrict.lean: the strict format's test on the chain's own trees,
along listed leaves, with the read leaves given as numbers.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

One part of the strict format of a slot's argument string (strictSB, which proofHasStrictFormat calls:
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) asks, of every tree of both components of every round: at
every leaf at whose position an opening stands, has the tree a root, is the position read, has the
salt its length? strictComp walks all 2 ^ depth numbers of leaves for that, and asks a test on
positions whether one is read. The string's field opens is a function on all positions, and the
verdict hangs on its value at each position that stands at a leaf. So here the caller says at which
leaves openings can stand, and the equation asks that there are none elsewhere. The caller also says
which leaves are read, as numbers, and the equation asks that these are the leaves of the read
positions: so these bodies make and search no set of read positions. The like for the library's own
layer, which has one tree a component, is in OnBytes/RunA/ListedOwnDefs.lean. Here a component has a
list of trees, and the functions take any shape s (the list of the rounds); there they take a list S
of round skeletons (RS) and stand at the shape up S.

Main names.
 - strictCompL, strictTreesL, strictSBL: strictComp, strictTrees, strictSB along listed leaves. own:
   round by round, for the shared component and for the slot's component, for each tree in the order
   of the trees, the leaves at which an opening can stand, read or not. rd: in the same form, the
   read leaves. A round or a tree for which a list holds nothing has the empty list of leaves. A
   listed number that is no leaf's (2 ^ depth or more) counts for nothing. strictSBL takes own
   before rd; strictTreesL takes the read leaves before the listed ones. The two have one type, so
   Lean does not see a swap.
 - ListedOK: an opening stands only at positions of leaves listed in own.
 - ReadsOK: a leaf of a tree is in rd exactly if its position is read. Both speak of the trees that
   the round's wiring lists (k below the number of depths) alone.
 - all_range_eq: a test along a list, with the list's numbers of n or more let pass, is the test
   along all numbers below n, if the list holds every number below n at which the test fails.
 - strictCompL_eq, strictTreesL_eq, strictSBL_eq: the tests along the listed leaves are the tests of
   OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean: the third under ListedOK and ReadsOK, the first two
   under the clauses of these for one tree and for one component.

Limits. Definitions and equations of Booleans. ListedOK and ReadsOK are premises: whoever makes the
string and the lists shows them; they are shown of no string and no lists here.
own must hold every leaf with an opening, not the read ones alone: the strict format is there to
refuse an opening at an unread place. At an own that leaves out a leaf with an opening strictSBL can
say yes where strictSB says no; at the empty own it tests nothing. strictSBL takes own as an
argument of its own beside the openings f, and nothing in this file ties the two. So a caller must
tie them. Either it makes both of one record and shows ListedOK for every such record. Or it strikes
the string's openings outside own first and shows ListedOK of the struck string: the equation then
speaks of the struck string, so an opening outside own is dropped, not refused.
At an rd that names an unread leaf strictSBL can say yes where strictSB says no; at an rd that
leaves out a read leaf it can say no where strictSB says yes. So a caller must compute rd on the
verifier's side, of the instance, the verifier's messages and the plain parts, and must not take it
as a list from the proof's side. Nothing in this file sees to that.
ListedOK asks more than the equation needs. It speaks of every number j at which the wiring names a
position. So a number of 2 ^ depth or more at which an opening stands must be listed, though it
counts for nothing in the test. And where a wiring names positions with openings at endlessly many
numbers of one listed tree, no list meets ListedOK. Under the laws of WireRB.OKG
(OnBytes/TypedOracleCompiler/Iop/BatchWire.lean: place_posAt0 with place_lt0, place_posAtJ with place_ltJ) a wiring
names no position at a number of 2 ^ depth or more: by reading, no lemma of this file says it.
ReadsOK asks its equation at every leaf with a position; the test needs it where an opening stands.
Nothing is said on time or memory: that no list of length 2 ^ depth is built is by reading the
bodies; a listed leaf is searched in the tree's list of read leaves from its front. Still carried as
data: W holds each round's wire record WireRB whole, with pt : Round.IsPoint, whose field finPos :
Fintype r.Pos holds the list of all the round's positions. By reading, not by a run: compiled Lean
is strict (Iop/Shape.lean, at finChalT), so a record's fields are built when the record is built,
and whoever builds W builds these lists. The like in OnBytes/RunA/ListedOwnDefs.lean drops that
field; this file does not.
The lists need not be sorted and may hold a number twice. all_range_eq and ListedOK stand under the
same short names in OnBytes/RunA/ListedOwnLaws.lean, in another namespace. Nothing is said on
soundness.
The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {lam K : ℕ}

/-! ### The definitions -/

/-- strictComp along the listed leaves js. isReadJ: is the leaf's position read? -/
def strictCompL (sMT : ℕ) {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isReadJ : ℕ → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ) : Bool :=
  js.all fun j => !decide (j < 2 ^ depth) || match posAt j with
    | none => true
    | some p => match f p with
      | none => true
      | some op => hasRoot && isReadJ j && decide (op.salt.length = sMT)

/-- strictTrees along listed leaves. For each tree of the component: rdss: its read leaves; jss: the
leaves at which an opening can stand. -/
def strictTreesL (sMT : ℕ) {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (rt : List (Dig lam)) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (rdss jss : List (List ℕ)) : Bool :=
  (List.range depth.length).all fun k =>
    strictCompL sMT (posAt k) (depth.getD k 0) (rt[k]?).isSome
      (fun j => (rdss.getD k []).contains j) f (jss.getD k [])

/-- strictSB along listed leaves. Round by round, for the trees of the shared component and of the
slot's component: own: the leaves at which an opening can stand; rd: the read leaves. -/
def strictSBL (sMT : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → RootsOfChain lam s →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → List (List (List ℕ) × List (List ℕ)) →
    List (List (List ℕ) × List (List ℕ)) → Bool
  | [], _, _, _, _, _, _ => true
  | _ :: s, (_, A), (w, W), (rt, rts), f, own, rd =>
      strictTreesL sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => f (.inl p))
        (rd.headD ([], [])).1 (own.headD ([], [])).1 &&
      strictTreesL sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => f (.inl p))
        (rd.headD ([], [])).2 (own.headD ([], [])).2 &&
      strictSBL sMT s A W rts (fun p => f (.inr p)) own.tail rd.tail

/-- An opening stands only at positions of listed leaves. Asked of the trees that the wiring lists
(k below the number of depths), at every number j. -/
def ListedOK :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → List (List (List ℕ) × List (List ℕ)) → Prop
  | [], _, _, _, _ => True
  | r :: s, (_, A), (w, W), f, own =>
    (∀ k, k < w.depth0.length → ∀ (j : ℕ) (p : r.Pos), w.posAt0 k j = some p →
      f (.inl p) ≠ none → j ∈ (own.headD ([], [])).1.getD k []) ∧
    (∀ k, k < w.depthJ.length → ∀ (j : ℕ) (p : r.Pos), w.posAtJ k j = some p →
      f (.inl p) ≠ none → j ∈ (own.headD ([], [])).2.getD k []) ∧
    ListedOK s A W (fun p => f (.inr p)) own.tail

/-- A leaf of a tree is in the tree's list of read leaves exactly if its position is read. Asked of
the trees that the wiring lists (k below the number of depths), at j below 2 ^ depth. -/
def ReadsOK :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (OPos s → Bool) →
    List (List (List ℕ) × List (List ℕ)) → Prop
  | [], _, _, _, _ => True
  | r :: s, (_, A), (w, W), isRead, rd =>
    (∀ k, k < w.depth0.length → ∀ (j : ℕ) (p : r.Pos), j < 2 ^ w.depth0.getD k 0 →
      w.posAt0 k j = some p → ((rd.headD ([], [])).1.getD k []).contains j = isRead (.inl p)) ∧
    (∀ k, k < w.depthJ.length → ∀ (j : ℕ) (p : r.Pos), j < 2 ^ w.depthJ.getD k 0 →
      w.posAtJ k j = some p → ((rd.headD ([], [])).2.getD k []).contains j = isRead (.inl p)) ∧
    ReadsOK s A W (fun p => isRead (.inr p)) rd.tail

/-! ### The equations -/

/-- A test along a list, with the list's numbers of n or more let pass, is the test along all
numbers below n, if the list holds every number below n at which the test fails. -/
theorem all_range_eq (n : ℕ) (B : ℕ → Bool) (js : List ℕ)
    (h : ∀ j, j < n → B j = false → j ∈ js) :
    (js.all fun j => !decide (j < n) || B j) = (List.range n).all B := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H j hj
    have hlt : j < n := List.mem_range.1 hj
    cases hB : B j with
    | true => rfl
    | false =>
      have := H j (h j hlt hB)
      simp [hlt, hB] at this
  · intro H j _
    by_cases hlt : j < n
    · simp [H j (List.mem_range.2 hlt)]
    · simp [hlt]

/-- One tree: along a list that holds every number at which an opening stands, and with a test on
numbers that agrees at the leaves with the test on positions, strictCompL is strictComp. -/
theorem strictCompL_eq (sMT : ℕ) {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (hasRoot : Bool) (isReadJ : ℕ → Bool) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ)
    (h : ∀ j p, posAt j = some p → f p ≠ none → j ∈ js)
    (hr : ∀ j p, j < 2 ^ depth → posAt j = some p → isReadJ j = isRead p) :
    strictCompL sMT posAt depth hasRoot isReadJ f js =
      strictComp sMT posAt depth hasRoot isRead f := by
  have e : strictCompL sMT posAt depth hasRoot isReadJ f js =
      js.all fun j => !decide (j < 2 ^ depth) || match posAt j with
        | none => true
        | some p => match f p with
          | none => true
          | some op => hasRoot && isRead p && decide (op.salt.length = sMT) := by
    unfold strictCompL
    congr 1
    funext j
    by_cases hlt : j < 2 ^ depth
    · cases hp : posAt j with
      | none => rfl
      | some p => rw [hr j p hlt hp]
    · simp [hlt]
  rw [e]
  unfold strictComp
  refine all_range_eq _ _ js fun j _ hB => ?_
  split at hB
  · cases hB
  · rename_i p hp
    split at hB
    · cases hB
    · rename_i op hf
      exact h j p hp (by rw [hf]; exact Option.some_ne_none _)

/-- One component: the same for its trees. Both premises are asked of the trees that have a depth
alone. -/
theorem strictTreesL_eq (sMT : ℕ) {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (rdss jss : List (List ℕ))
    (h : ∀ k, k < depth.length → ∀ j p, posAt k j = some p → f p ≠ none → j ∈ jss.getD k [])
    (hr : ∀ k, k < depth.length → ∀ j p, j < 2 ^ depth.getD k 0 → posAt k j = some p →
      (rdss.getD k []).contains j = isRead p) :
    strictTreesL sMT posAt depth rt f rdss jss = strictTrees sMT posAt depth rt isRead f := by
  have e : ∀ k, k ∈ List.range depth.length →
      strictCompL sMT (posAt k) (depth.getD k 0) (rt[k]?).isSome
        (fun j => (rdss.getD k []).contains j) f (jss.getD k []) =
      strictComp sMT (posAt k) (depth.getD k 0) (rt[k]?).isSome isRead f := fun k hk =>
    strictCompL_eq sMT (posAt k) (depth.getD k 0) (rt[k]?).isSome
      (fun j => (rdss.getD k []).contains j) isRead f (jss.getD k [])
      (h k (List.mem_range.1 hk)) (hr k (List.mem_range.1 hk))
  unfold strictTreesL strictTrees
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H k hk
    rw [← e k hk]
    exact H k hk
  · intro H k hk
    rw [e k hk]
    exact H k hk

/-- **Under ListedOK and ReadsOK the test along the listed leaves is strictSB.** -/
theorem strictSBL_eq (sMT : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
      (f : (p : OPos s) → Option (Opening lam (OSym s p)))
      (own rd : List (List (List ℕ) × List (List ℕ))), ListedOK s A W f own →
      ReadsOK s A W isRead rd →
      strictSBL sMT s A W rts f own rd = strictSB sMT s A W rts isRead f
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), (rt, rts), isRead, f, own, rd, h, hr => by
    have ih := strictSBL_eq sMT s A W rts (fun p => isRead (.inr p)) (fun p => f (.inr p))
      own.tail rd.tail h.2.2 hr.2.2
    have e0 := strictTreesL_eq sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => isRead (.inl p))
      (fun p => f (.inl p)) (rd.headD ([], [])).1 (own.headD ([], [])).1 h.1 hr.1
    have eJ := strictTreesL_eq sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => isRead (.inl p))
      (fun p => f (.inl p)) (rd.headD ([], [])).2 (own.headD ([], [])).2 h.2.1 hr.2.1
    show (strictTreesL sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => f (.inl p))
          (rd.headD ([], [])).1 (own.headD ([], [])).1 &&
        strictTreesL sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => f (.inl p))
          (rd.headD ([], [])).2 (own.headD ([], [])).2 &&
        strictSBL sMT s A W rts (fun p => f (.inr p)) own.tail rd.tail) = _
    rw [e0, eJ, ih]
    rfl

end TypedOracleCompiler.Compile.Batch

#print axioms TypedOracleCompiler.Compile.Batch.all_range_eq
#print axioms TypedOracleCompiler.Compile.Batch.strictCompL_eq
#print axioms TypedOracleCompiler.Compile.Batch.strictTreesL_eq
#print axioms TypedOracleCompiler.Compile.Batch.strictSBL_eq
