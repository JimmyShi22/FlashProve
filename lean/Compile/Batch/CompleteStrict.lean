-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteStrict.lean: lemmas for the strict format (`proofHasStrictFormat`,
Compile/Batch/Verifier.lean) of the honest prover's proof string of a slot;
Compile/Batch/CompleteAcc.lean puts them together (words of this library: lean/GLOSSARY.md).

From Compile/Batch/CompleteOpen.lean: under `RoundsQueryLayout.OKG`, there is an opening at every position that
is read and whose component has a tree (`OpensOK`). Part 1: under `RoundsQueryLayout.OKG`, nothing else is
opened. Part 2 has the lemmas for four of the six conjuncts of `proofHasStrictFormat`, from Part 1, `RoundsQueryLayout.OKG`
and `RoundsOK` (Compile/Batch/CompleteChain.lean: salts of exactly sMT bits): the second conjunct,
on the number of roots (`length_rootToks`); the third, `strictSB` (`strictSB_of`); the fourth,
`strictExt` (`strictExt_of`), from `ExtSalt`; the sixth, on the request path (`isSome_slotVal_phV`),
only where the chain has joined. The first and the fifth (that the chain's salt has sFS bits, that
the slot number is in range) and `ExtSalt` are hypotheses in Compile/Batch/CompleteAcc.lean. Part 3:
when the strict verifier accepts.

Notation: `proofHasStrictFormat` (Compile/Batch/Verifier.lean): a `Bool`: the strict format of the proof string
of a slot, given what the chain yields; `Tri f c vs Q` (Compile/EraseKit.lean): a proposition: under
the oracle functions f, whatever the coins, the erased program c, started with the store vs, returns
a value a and a store vs' with Q a vs'; `EvalsTo f x a` (Compile/MerkleRom.lean): a proposition:
under the oracle functions f the algorithm x returns a, whatever its coins; `vs`: a `List Bits`: the
store: the list of strings for which the tokens stand (the head of Compile/Batch/CompleteRef.lean);
`tjs`, `t0s`, `rts` (`RoundsOK`, Compile/Batch/CompleteChain.lean): tjs are the trees over the
slot's components, t0s those over the shared components, rts the roots as the verifier has them;
`opT` (Compile/Batch/CompleteOpen.lean): the honest opening of the position p in the token tree tr
over (a component of) the oracle o; `honestExt` (Compile/Batch/CompleteOpen.lean): the honest
opening of an external position.
-/
import Compile.Batch.CompleteOpen

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. Nothing is opened that is not read (under `RoundsQueryLayout.OKG`) -/

theorem tri_opensComp_only {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (o : r.Orc) (tr : TTree) (isRead : r.Pos → Bool)
    (f0 : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ∀ (js : List ℕ) (vs : List Bits),
    Tri f (opensComp (K := K) (L := L) dec posAt o tr isRead f0 js) vs fun g vs' =>
      vs' = vs ∧
      ∀ p op, g p = some op →
        f0 p = some op ∨ (isRead p = true ∧ (∃ j ∈ js, posAt j = some p) ∧ op = opT place vs tr o p)
  | [], _ => tri_pure_iff.2 ⟨rfl, fun _ _ h => Or.inl h⟩
  | j :: js, vs => by
      refine Tri.bind (tri_opensComp_only dec posAt place hpl o tr isRead f0 js vs)
        fun g vs1 hg => ?_
      obtain ⟨rfl, hg⟩ := hg
      have hmore : ∀ p op, g p = some op →
          f0 p = some op ∨
          (isRead p = true ∧
            (∃ j' ∈ j :: js, posAt j' = some p) ∧
            op = opT place vs1 tr o p) := fun p op h =>
        (hg p op h).imp id fun ⟨h1, ⟨j', hj', h2⟩, h3⟩ =>
          ⟨h1, ⟨j', List.mem_cons_of_mem _ hj', h2⟩, h3⟩
      split
      · rename_i p0 hpos
        by_cases hr : isRead p0 = true
        · rw [if_pos hr]
          refine Tri.bind (tri_openT f tr j (r.rd o p0) vs1) fun op vs2 hop => tri_pure_iff.2 ?_
          obtain ⟨rfl, rfl⟩ := hop
          refine ⟨rfl, fun p op' h => ?_⟩
          by_cases hpp : p = p0
          · subst hpp
            rw [@Function.update_self _ _ dec] at h
            obtain rfl := Option.some.inj h
            exact Or.inr ⟨hr, ⟨j, List.mem_cons_self, hpos⟩, by rw [opT, hpl j p hpos]⟩
          · rw [@Function.update_of_ne _ _ dec _ _ hpp] at h
            exact hmore p op' h
        · rw [if_neg hr]
          exact tri_pure_iff.2 ⟨rfl, hmore⟩
      · exact tri_pure_iff.2 ⟨rfl, hmore⟩

/-- Opening the trees of one component from number k on adds nothing but honest openings at read
positions (`posAt n j`: the position at leaf j of tree number n; hpl: `place p` is that leaf; f0:
the openings made before). Tree number k + n is entry n of trs, and its depth is entry n of ds; only
the numbers n at which both lists have an entry count. An opening in the result is f0's, or it is at
a read position that stands at a leaf of such a tree and is the honest opening in that tree. The
store stays as it is. -/
theorem tri_opensTrees_only {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (place : r.Pos → ℕ) (hpl : ∀ n j p, posAt n j = some p → place p = j)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f0 : (p : r.Pos) → Option (Opening lam (r.Sym p))) (vs : List Bits),
      Tri f (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f0) vs fun g vs' =>
        vs' = vs ∧
        ∀ p op, g p = some op →
          f0 p = some op ∨
          (isRead p = true ∧
            ∃ n d t, ds[n]? = some d ∧ trs[n]? = some t ∧
              (∃ j < 2 ^ d, posAt (k + n) j = some p) ∧ op = opT place vs t o p)
  | _, [], _, _, _ => tri_pure_iff.2 ⟨rfl, fun _ _ h => Or.inl h⟩
  | _, _ :: _, [], _, _ => tri_pure_iff.2 ⟨rfl, fun _ _ h => Or.inl h⟩
  | k, d :: ds, tr :: trs, f0, vs => by
      refine Tri.bind (tri_opensTrees_only dec posAt place hpl o isRead (k + 1) ds trs f0 vs)
        fun g1 vs1 hg => ?_
      obtain ⟨rfl, h1⟩ := hg
      refine (tri_opensComp_only f dec (posAt k) place (hpl k) o tr isRead g1
        (List.range (2 ^ d)) vs1).mono ?_
      rintro g vs' ⟨rfl, c1⟩
      refine ⟨rfl, fun p op h => ?_⟩
      rcases c1 p op h with h' | ⟨hr, ⟨j, hj, hpos⟩, hop⟩
      · refine (h1 p op h').imp id ?_
        rintro ⟨hr, n, d', t, hd, ht, ⟨j, hj, hpos⟩, hop⟩
        have hk : k + (n + 1) = k + 1 + n := by omega
        exact ⟨hr, n + 1, d', t, hd, ht, ⟨j, hj, hk ▸ hpos⟩, hop⟩
      · exact Or.inr ⟨hr, 0, d, tr, rfl, rfl, ⟨j, List.mem_range.1 hj, hpos⟩, hop⟩

/-- An opening is only at a position that is read and whose component has a tree, and it is the
honest opening. -/
def OpensOnly (vs : List Bits) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Tr s → List (Option TTree) →
    List (Option TTree) → (OPos s → Bool) → ((p : OPos s) → Option (Opening lam (OSym s p))) → Prop
  | [], _, _, _, _, _, _, _ => True
  | _ :: s, (a, A), (w, W), (m, _, τ), tjs, t0s, isRead, g =>
      (∀ p op, g (.inl p) = some op → isRead (.inl p) = true ∧
        ((a.own p = false ∧ ∃ tr, t0s.headD none = some tr ∧ op = opT w.place vs tr m.1 p) ∨
         (a.own p = true ∧ ∃ tr, tjs.headD none = some tr ∧ op = opT w.place vs tr m.1 p))) ∧
      OpensOnly vs s A W τ tjs.tail t0s.tail (fun p => isRead (.inr p)) (fun p => g (.inr p))

theorem tri_opensB_only :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (τ : Tr s) (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool) (vs : List Bits),
        Tri f (opensB (L := L) s A W τ tjs t0s isRead) vs fun g vs' =>
          vs' = vs ∧ OpensOnly vs s A W τ tjs t0s isRead g
  | [], _, _, _, _, _, _, _, _ => tri_pure_iff.2 ⟨rfl, trivial⟩
  | r :: s, (a, A), (w, W), hW, (m, _, τ), tjs, t0s, isRead, vs => by
      have h0 : Tri f
          (opensOpt (K := K) (L := L) w.pt.decPos w.posAt0 w.depth0 m.1 (t0s.headD none)
            (fun p => isRead (.inl p)) (fun _ => none))
          vs fun g vs' =>
            vs' = vs ∧
            ∀ p op, g p = some op →
              isRead (.inl p) = true ∧
              a.own p = false ∧
              ∃ tr, t0s.headD none = some tr ∧ op = opT w.place vs tr m.1 p := by
        unfold opensOpt
        cases t0s.headD none with
        | none => exact tri_pure_iff.2 ⟨rfl, fun _ _ h => by cases h⟩
        | some tr =>
          refine (tri_opensComp_only f w.pt.decPos w.posAt0 w.place
            (fun j p h => (hW.1.place_posAt0 j p h).2) m.1 tr _ _ _ vs).mono ?_
          rintro g vs' ⟨rfl, h1⟩
          refine ⟨rfl, fun p op h => ?_⟩
          rcases h1 p op h with h2 | ⟨h2, ⟨j, -, h3⟩, h4⟩
          · cases h2
          · exact ⟨h2, (hW.1.place_posAt0 j p h3).1, tr, rfl, h4⟩
      refine Tri.bind h0 fun g0 vs1 hg0 => ?_
      obtain ⟨rfl, hg0⟩ := hg0
      have h1 : Tri f
          (opensOpt (K := K) (L := L) w.pt.decPos w.posAtJ w.depthJ m.1 (tjs.headD none)
            (fun p => isRead (.inl p)) g0)
          vs1 fun g vs' =>
            vs' = vs1 ∧
            ∀ p op, g p = some op →
              g0 p = some op ∨
              (isRead (.inl p) = true ∧
                a.own p = true ∧
                ∃ tr, tjs.headD none = some tr ∧ op = opT w.place vs1 tr m.1 p) := by
        unfold opensOpt
        cases tjs.headD none with
        | none => exact tri_pure_iff.2 ⟨rfl, fun _ _ h => Or.inl h⟩
        | some tr =>
          refine (tri_opensComp_only f w.pt.decPos w.posAtJ w.place
            (fun j p h => (hW.1.place_posAtJ j p h).2) m.1 tr _ _ _ vs1).mono ?_
          rintro g vs' ⟨rfl, h1⟩
          refine ⟨rfl, fun p op h => (h1 p op h).imp id ?_⟩
          rintro ⟨h2, ⟨j, -, h3⟩, h4⟩
          exact ⟨h2, (hW.1.place_posAtJ j p h3).1, tr, rfl, h4⟩
      refine Tri.bind h1 fun g1 vs2 hg1 => ?_
      obtain ⟨rfl, hg1⟩ := hg1
      refine Tri.bind
        (tri_opensB_only s A W hW.2 τ tjs.tail t0s.tail (fun p => isRead (.inr p)) vs2)
        fun g2 vs3 hg2 => tri_pure_iff.2 ?_
      obtain ⟨rfl, hg2⟩ := hg2
      refine ⟨rfl, fun p op h => ?_, hg2⟩
      rcases hg1 p op h with h' | ⟨h2, h3, h4⟩
      · obtain ⟨h2, h3, h4⟩ := hg0 p op h'
        exact ⟨h2, Or.inl ⟨h3, h4⟩⟩
      · exact ⟨h2, Or.inr ⟨h3, h4⟩⟩

theorem tri_opensExtB_only {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) (vs : List Bits), Tri f (opensExtB (K := K) (L := L) we y trees isRead ps) vs fun g vs' =>
      vs' = vs ∧ ∀ p op, g p = some op → isRead p = true ∧ op = honestExt we vs trees y p
  | [], vs => tri_pure_iff.2 ⟨rfl, fun _ _ h => by cases h⟩
  | p0 :: ps, vs => by
      refine Tri.bind (tri_opensExtB_only we y trees isRead ps vs) fun g vs1 hg => ?_
      obtain ⟨rfl, hg⟩ := hg
      by_cases hr : isRead p0 = true
      · rw [if_pos hr]
        refine Tri.bind (tri_openE f _ _ _ vs1) fun op vs2 hop => tri_pure_iff.2 ?_
        obtain ⟨rfl, rfl⟩ := hop
        refine ⟨rfl, fun p op' h => ?_⟩
        by_cases hpp : p = p0
        · subst hpp
          rw [@Function.update_self _ _ we.dec] at h
          obtain rfl := Option.some.inj h
          exact ⟨hr, rfl⟩
        · rw [@Function.update_of_ne _ _ we.dec _ _ hpp] at h
          exact hg p op' h
      · rw [if_neg hr]
        exact tri_pure_iff.2 ⟨rfl, hg⟩

/-! ## Part 2. The checks of the strict format -/

theorem strictComp_of {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ) {sent : Bool}
    {isRead : r.Pos → Bool} {g : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h : ∀ j p op, j < 2 ^ depth → posAt j = some p → g p = some op →
      sent = true ∧ isRead p = true ∧ op.salt.length = sMT) :
    strictComp sMT posAt depth sent isRead g = true := by
  unfold strictComp
  refine List.all_eq_true.2 fun j hj => ?_
  split
  · rfl
  · rename_i p hp
    split
    · rfl
    · rename_i op hop
      obtain ⟨h1, h2, h3⟩ := h j p op (List.mem_range.1 hj) hp hop
      simp [h1, h2, h3]

/-- The strict format holds for all trees of a component, from tree number k on, if every opening at
a leaf of one of them belongs to a tree whose root is sent, stands at a position that is read, and
has a salt of sMT bits. i counts the trees from k: tree number k + i has the depth ds[i], and its
root is sent exactly if i < rts.length. -/
theorem strictTrees_of {sMT : ℕ} {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    {isRead : r.Pos → Bool} {g : (p : r.Pos) → Option (Opening lam (r.Sym p))} :
    ∀ (k : ℕ) (ds : List ℕ) (rts : List (Dig lam)),
      (∀ i d j p op, ds[i]? = some d → j < 2 ^ d → posAt (k + i) j = some p → g p = some op →
        i < rts.length ∧ isRead p = true ∧ op.salt.length = sMT) →
      strictTrees sMT posAt isRead g k ds rts = true
  | _, [], _, _ => by simp only [strictTrees]
  | k, d :: ds, [], h => by
      simp only [strictTrees, Bool.and_eq_true]
      exact ⟨strictComp_of (posAt k) d fun j p op hj hp hop =>
          absurd (h 0 d j p op rfl hj hp hop).1 (Nat.not_lt_zero _),
        strictTrees_of posAt (k + 1) ds [] fun i e j p op he hj hp hop =>
          absurd (h (i + 1) e j p op he hj
            (by rwa [show k + (i + 1) = k + 1 + i by omega]) hop).1 (Nat.not_lt_zero _)⟩
  | k, d :: ds, _ :: cs, h => by
      simp only [strictTrees, Bool.and_eq_true]
      exact ⟨strictComp_of (posAt k) d fun j p op hj hp hop =>
          ⟨rfl, (h 0 d j p op rfl hj hp hop).2⟩,
        strictTrees_of posAt (k + 1) ds cs fun i e j p op he hj hp hop =>
          (h (i + 1) e j p op he hj
            (by rwa [show k + (i + 1) = k + 1 + i by omega]) hop).imp_left Nat.lt_of_succ_lt_succ⟩

variable {f} in
/-- the salt of a leaf of a token tree with `TTreeOK` has sMT bits -/
theorem TTreeOK.salt_length {sMT : ℕ} {vs : List Bits} {t : TTree} {d : ℕ} {leaf : ℕ → Body L}
    (h : TTreeOK f sMT vs t d leaf) {j : ℕ} (hj : j < 2 ^ d) :
    (vs.getD (t.salts.getD j 0) []).length = sMT :=
  (h.2.1 _ (getD_mem_of_lt (by rw [h.1]; exact hj))).2

theorem strictSB_of {sMT : ℕ} {vs : List Bits} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (embS : (p : OPos s) → OSym s p → Body L)
          (τ : Tr s) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam s),
        RoundsOK f sMT vs s A W embS τ tjs t0s rts →
        ∀ (isRead : OPos s → Bool) (g : (p : OPos s) → Option (Opening lam (OSym s p))),
          OpensOnly vs s A W τ tjs t0s isRead g → strictSB sMT s A W rts isRead g = true
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), hW, embS, (m, _, τ), _, _, ((rt0, rtj), rts), h, isRead, g, hg => by
      obtain ⟨tj, t0, tjs', t0s', rfl, rfl, h0, hj, -, -, -, -, hr⟩ := h
      show (strictComp sMT w.posAt0 w.depth0 rt0.join.isSome
            (fun p => isRead (.inl p)) (fun p => g (.inl p)) &&
          strictComp sMT w.posAtJ w.depthJ rtj.join.isSome
            (fun p => isRead (.inl p)) (fun p => g (.inl p)) &&
          strictSB sMT s A W rts (fun p => isRead (.inr p)) (fun p => g (.inr p))) = true
      revert h0 hj
      show CompOK f sMT vs t0 rt0.join _ _ → CompOK f sMT vs tj rtj.join _ _ → _
      generalize rt0.join = c0
      generalize rtj.join = cj
      intro h0 hj
      rw [strictComp_of w.posAt0 w.depth0 fun j p op hjl hp hop => ?_,
        strictComp_of w.posAtJ w.depthJ fun j p op hjl hp hop => ?_,
        strictSB_of s A W hW.2 _ τ tjs' t0s' rts hr _ _ hg.2]
      · rfl
      · obtain ⟨hown, hpl⟩ := hW.1.place_posAtJ j p hp
        obtain ⟨h1, h2⟩ := hg.1 p op hop
        rcases h2 with ⟨h3, -⟩ | ⟨-, tr, htr, rfl⟩
        · rw [hown] at h3; cases h3
        · obtain rfl : tj = some tr := htr
          cases cj with
          | none => exact hj.elim
          | some c => exact ⟨rfl, h1, by rw [opT, hpl]; exact hj.1.salt_length hjl⟩
      · obtain ⟨hown, hpl⟩ := hW.1.place_posAt0 j p hp
        obtain ⟨h1, h2⟩ := hg.1 p op hop
        rcases h2 with ⟨-, tr, htr, rfl⟩ | ⟨h3, -⟩
        · obtain rfl : t0 = some tr := htr
          cases c0 with
          | none => exact h0.elim
          | some c => exact ⟨rfl, h1, by rw [opT, hpl]; exact h0.1.salt_length hjl⟩
        · rw [hown] at h3; cases h3

/-- Under `RoundsOK`: there are as many root tokens as the verifier's chain takes roots. -/
theorem length_rootToks {sMT : ℕ} {vs : List Bits} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (τ : Tr s) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam s),
      RoundsOK f sMT vs s A W embS τ tjs t0s rts → (rootToks tjs t0s).length = RootsOfChain.count s rts
  | [], _, _, _, _, _, _, _, h => by rw [h.1, h.2]; rfl
  | _ :: s, (_, A), (_, W), embS, (_, _, τ), _, _, ((rt0, rtj), rts), h => by
      obtain ⟨tj, t0, tjs', t0s', rfl, rfl, h0, hj, -, -, -, -, hr⟩ := h
      have e0 : (t0.map TTree.root).toList.length = rt0.join.toList.length := by
        revert h0
        show CompOK f sMT vs t0 rt0.join _ _ → _
        generalize rt0.join = c0
        intro h0
        cases t0 <;> cases c0 <;> first | rfl | exact h0.elim
      have ej : (tj.map TTree.root).toList.length = rtj.join.toList.length := by
        revert hj
        show CompOK f sMT vs tj rtj.join _ _ → _
        generalize rtj.join = cj
        intro hj
        cases tj <;> cases cj <;> first | rfl | exact hj.elim
      show ((tj.map TTree.root).toList ++ (t0.map TTree.root).toList ++ rootToks tjs' t0s').length =
        rt0.join.toList.length + rtj.join.toList.length + RootsOfChain.count s rts
      rw [List.length_append, List.length_append, e0, ej,
        length_rootToks s A W _ τ tjs' t0s' rts hr]
      omega

/-- In the external trees, the leaf of every external position has a salt of exactly sMT bits. -/
def ExtSalt {E : ExtSpec} (we : WireE E) (vs : List Bits) (sMT : ℕ) (trees : List (TreeH lam)) :
    Prop :=
  ∀ p : E.Pos,
    (saltVal vs ((trees.getD (we.which p) ⟨[], []⟩).salts.getD (we.leaf p) none)).length = sMT

variable {f} in
theorem ExtSalt.mono {E : ExtSpec} {we : WireE E} {embE : E.Sym → Body L} {vs vs' : List Bits}
    (hp : vs <+: vs') {sMT : ℕ} {trees : List (TreeH lam)} {y : E.Str}
    (hok : ExtOK f sMT we embE vs trees y) (h : ExtSalt we vs sMT trees) :
    ExtSalt we vs' sMT trees :=
  fun p => by
    obtain ⟨-, -, leaf, h3, -⟩ := hok p
    rw [saltVal_of_prefix hp (tokOK_getD h3.2.1 _)]
    exact h p

theorem strictExt_of {sMT : ℕ} {E : ExtSpec} (we : WireE E) {isRead : E.Pos → Bool}
    {g : E.Pos → Option (Opening lam E.Sym)}
    (h : ∀ p op, g p = some op → isRead p = true ∧ op.salt.length = sMT) :
    strictExt sMT we isRead g = true := by
  unfold strictExt
  refine List.all_eq_true.2 fun p _ => ?_
  split
  · rfl
  · rename_i op hop
    obtain ⟨h1, h2⟩ := h p op hop
    simp [h1, h2]

theorem isSome_slotVal_phV {Y : Type} (vs : List Bits) :
    ∀ (ph : PhT) (acc : SlotAcc lam K Y), chainsHaveJoined ph → (phV vs ph acc).slotVal.isSome = true
  | .shr _, _, _ => rfl
  | .aft, _, _ => rfl

/-! ## Part 3. The strict verifier -/

variable {f} in
/-- The strict verifier accepts, if its own chain returns a value at which the string is of the
strict format and its end checkPrunedOpenings accepts. (That the lax verifyB accepts would not be enough:
checkPrunedOpenings may verify the opened leaves of a tree together, from pruned paths;
Compile/Batch/CompleteForest.lean.) -/
theorem evalsTo_verifyBS {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {wq : ProtocolQueryLayout lam K Q} {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
    {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (h1 : EvalsTo f (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true)
    (h2 : EvalsTo f (recomputeChainOfProof t Q wq embP xin cms x π) (some (ρ, rts, ph)))
    (h3 : proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph = true) :
    EvalsTo f (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) true := by
  unfold EvalsTo at h1 h2 ⊢
  unfold verifyOneProtocol
  rw [OComp.runEager_bind, h2, PMF.pure_bind]
  simp only [h3, if_true]
  exact h1

end Compile.Batch.Cmpl
