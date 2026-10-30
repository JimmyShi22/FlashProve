-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteOpen.lean: the honest prover's Merkle openings pass the verifier's checks
(words of this library: lean/GLOSSARY.md).

The openings of the compiled prover (`opensB`, `opensExtB`) against the checks of the compiled
verifier (`checksB`, `checksExt`), and what the verifier does after it has recomputed the chain, for
fixed oracle functions, each under the hypotheses of its statement (among them `RoundsQueryLayout.OKG`,
`RoundsOK`, `OpensOK`, `ExtOK`). A component without a field in its round's format is not sent.

  Part 1  the openings in the two trees of each round
  Part 2  the checks that they call for are good, and not too many
  Part 3  the transcript that the verifier builds agrees with the prover's where the verifier reads
  Part 4  external positions

Notation: `Tri f c vs Q` (Compile/EraseKit.lean): a proposition: under the oracle functions f,
whatever the coins, the erased program c, started with the store vs, returns a value a and a store
vs' with Q a vs'; `EvalsTo f x a` (Compile/MerkleRom.lean): a proposition: under the oracle
functions f the algorithm x returns a, whatever its coins; `f`: a `Fam` (Rom/OSpec.lean): a whole
family of functions; `vs`: a `List Bits`: the store: the list of strings for which the tokens stand
(the head of Compile/Batch/CompleteRef.lean); `dv lam vs` (Compile/Batch/CompleteTree.lean):
`Tok → Dig lam`: the digest for which a token stands; `lam`, `K`: natural numbers; a `Dig lam`
(Iop/Wire.lean): a hash block (a digest or a chaining value): lam bits; `L`: an `BatchProtocol I X`
(Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with the honest sides; `sMT`: a
natural number: the length of the salt of a leaf (Compile/Batch/Verifier.lean); a token tree: a
`TTree` (Compile/Batch/TokTree.lean): all levels of tokens of digests, leaves first; the token of
the salt of each leaf (none in a request tree).

Limits: `evalsTo_afterChain` follows the path of each opening by itself (`runChecks`): that is the
form of `afterB`, the end of the verifier without the strict-format check (`verifyB`,
Compile/Batch/Verifier.lean). The scheme runs the strict verifier (`verifyOneProtocol`), whose end `checkPrunedOpenings`
verifies forest by forest: Compile/Batch/CompleteForest.lean.
-/
import Compile.Batch.CompleteChain
import Mathlib.Data.Finset.Sum

noncomputable section

namespace Compile.Batch.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. Openings -/

/-- the honest opening of the position p in the token tree tr over (a component of) the oracle o -/
def opT {r : Round} (place : r.Pos → ℕ) (vs : List Bits) (tr : TTree) (o : r.Orc) (p : r.Pos) :
    Opening lam (r.Sym p) :=
  ⟨r.rd o p, vs.getD (tr.salts.getD (place p) 0) [], (pathOf tr.levels (place p)).map (dv lam vs)⟩

theorem tri_opensComp {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (o : r.Orc) (tr : TTree) (isRead : r.Pos → Bool)
    (f0 : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ∀ (js : List ℕ) (vs : List Bits),
    Tri f (opensComp (K := K) (L := L) dec posAt o tr isRead f0 js) vs fun g vs' =>
      vs' = vs ∧
      (∀ p, isRead p = true → (∃ j ∈ js, posAt j = some p) → g p = some (opT place vs tr o p)) ∧
      ∀ p, (∀ j ∈ js, posAt j ≠ some p) → g p = f0 p
  | [], _ =>
    tri_pure_iff.2 ⟨rfl, fun _ _ h => (by obtain ⟨j, hj, -⟩ := h; cases hj), fun _ _ => rfl⟩
  | j :: js, vs => by
      refine Tri.bind (tri_opensComp dec posAt place hpl o tr isRead f0 js vs) fun g vs1 hg => ?_
      obtain ⟨rfl, hg1, hg2⟩ := hg
      have hrest : ∀ p, posAt j ≠ some p → (∃ j' ∈ j :: js, posAt j' = some p) →
          ∃ j' ∈ js, posAt j' = some p := by
        rintro p hp ⟨j', hj', hpos⟩
        rcases List.mem_cons.1 hj' with rfl | h
        · exact absurd hpos hp
        · exact ⟨j', h, hpos⟩
      split
      · rename_i p0 hpos
        by_cases hr : isRead p0 = true
        · rw [if_pos hr]
          refine Tri.bind (tri_openT f tr j (r.rd o p0) vs1) fun op vs2 hop => tri_pure_iff.2 ?_
          obtain ⟨rfl, rfl⟩ := hop
          refine ⟨rfl, fun p hp hm => ?_, fun p hp => ?_⟩
          · by_cases hpp : p = p0
            · subst hpp
              rw [@Function.update_self _ _ dec, opT, hpl j p hpos]
            · rw [@Function.update_of_ne _ _ dec _ _ hpp]
              exact hg1 p hp (hrest p (fun h => hpp (Option.some.inj (hpos.symm.trans h)).symm) hm)
          · have hpp : p ≠ p0 := fun h => hp j List.mem_cons_self (h ▸ hpos)
            rw [@Function.update_of_ne _ _ dec _ _ hpp]
            exact hg2 p fun j' hj' => hp j' (List.mem_cons_of_mem _ hj')
        · rw [if_neg hr]
          refine tri_pure_iff.2
            ⟨rfl, fun p hp hm => hg1 p hp (hrest p (fun h => ?_) hm),
              fun p hp => hg2 p fun j' hj' => hp j' (List.mem_cons_of_mem _ hj')⟩
          rw [hpos] at h
          exact hr (Option.some.inj h ▸ hp)
      · rename_i hpos
        exact tri_pure_iff.2
          ⟨rfl, fun p hp hm => hg1 p hp (hrest p (fun h => by rw [hpos] at h; cases h) hm),
            fun p hp => hg2 p fun j' hj' => hp j' (List.mem_cons_of_mem _ hj')⟩

/-- The openings in the trees of one component from number k on (`posAt n j`: the position at leaf j
of tree number n; hpl: a position stands in one tree only, at one leaf): the store is as before; at
every read position at a leaf of a tree that has a depth and a token tree the result holds the
honest opening in that tree; at a position that stands at no such leaf it is f0. -/
theorem tri_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (tree place : r.Pos → ℕ) (hpl : ∀ n j p, posAt n j = some p → tree p = n ∧ place p = j)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f0 : (p : r.Pos) → Option (Opening lam (r.Sym p))) (vs : List Bits),
      Tri f (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f0) vs fun g vs' =>
        vs' = vs ∧
        (∀ n d t, ds[n]? = some d → trs[n]? = some t →
          ∀ j p, j < 2 ^ d → posAt (k + n) j = some p → isRead p = true →
            g p = some (opT place vs t o p)) ∧
        ∀ p, (∀ n d t, ds[n]? = some d → trs[n]? = some t →
          ∀ j, j < 2 ^ d → posAt (k + n) j ≠ some p) → g p = f0 p
  | _, [], _, _, _ => tri_pure_iff.2 ⟨rfl, fun _ _ _ hd => by simp at hd, fun _ _ => rfl⟩
  | _, _ :: _, [], _, _ => tri_pure_iff.2 ⟨rfl, fun _ _ _ _ ht => by simp at ht, fun _ _ => rfl⟩
  | k, d :: ds, tr :: trs, f0, vs => by
      refine Tri.bind (tri_opensTrees dec posAt tree place hpl o isRead (k + 1) ds trs f0 vs)
        fun g1 vs1 h1 => ?_
      obtain ⟨rfl, h1a, h1b⟩ := h1
      refine (tri_opensComp f dec (posAt k) place (fun j p h => (hpl k j p h).2) o tr isRead g1
        (List.range (2 ^ d)) vs1).mono ?_
      rintro g vs' ⟨rfl, h2a, h2b⟩
      refine ⟨rfl, fun n d' t hd ht j p hj hp hr => ?_, fun p hp => ?_⟩
      · cases n with
        | zero =>
          obtain rfl := Option.some.inj hd
          obtain rfl := Option.some.inj ht
          exact h2a p hr ⟨j, List.mem_range.2 hj, hp⟩
        | succ n =>
          have hk : ∀ j' ∈ List.range (2 ^ d), posAt k j' ≠ some p := fun j' _ h' => by
            have e1 := (hpl _ _ _ h').1
            have e2 := (hpl _ _ _ hp).1
            omega
          rw [h2b p hk]
          rw [List.getElem?_cons_succ] at hd ht
          exact h1a n d' t hd ht j p hj
            (by rw [show k + 1 + n = k + (n + 1) by omega]; exact hp) hr
      · rw [h2b p fun j' hj' =>
          hp 0 d tr List.getElem?_cons_zero List.getElem?_cons_zero j' (List.mem_range.1 hj')]
        refine h1b p fun n d' t hd ht j hj => ?_
        rw [show k + 1 + n = k + (n + 1) by omega]
        exact hp (n + 1) d' t (by rw [List.getElem?_cons_succ]; exact hd)
          (by rw [List.getElem?_cons_succ]; exact ht) j hj

/-- At every position that is read, and whose component has a tree, the proof string holds the
honest opening. -/
def OpensOK (vs : List Bits) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Tr s → List (Option TTree) →
    List (Option TTree) → (OPos s → Bool) → ((p : OPos s) → Option (Opening lam (OSym s p))) → Prop
  | [], _, _, _, _, _, _, _ => True
  | _ :: s, (a, A), (w, W), (m, _, τ), tjs, t0s, isRead, g =>
      (∀ tr, t0s.headD none = some tr →
        ∀ p,
          a.own p = false → isRead (.inl p) = true → g (.inl p) = some (opT w.place vs tr m.1 p)) ∧
      (∀ tr, tjs.headD none = some tr →
        ∀ p,
          a.own p = true → isRead (.inl p) = true → g (.inl p) = some (opT w.place vs tr m.1 p)) ∧
      OpensOK vs s A W τ tjs.tail t0s.tail (fun p => isRead (.inr p)) (fun p => g (.inr p))

theorem tri_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (τ : Tr s) (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool) (vs : List Bits),
        Tri f (opensB (L := L) s A W τ tjs t0s isRead) vs fun g vs' =>
          vs' = vs ∧ OpensOK vs s A W τ tjs t0s isRead g
  | [], _, _, _, _, _, _, _, _ => tri_pure_iff.2 ⟨rfl, trivial⟩
  | r :: s, (a, A), (w, W), hW, (m, _, τ), tjs, t0s, isRead, vs => by
      have h0 : Tri f
          (opensOpt (K := K) (L := L) w.pt.decPos w.posAt0 w.depth0 m.1 (t0s.headD none)
            (fun p => isRead (.inl p)) (fun _ => none))
          vs fun g vs' =>
            vs' = vs ∧
            ∀ tr, t0s.headD none = some tr →
              ∀ p, a.own p = false → isRead (.inl p) = true →
                g p = some (opT w.place vs tr m.1 p) := by
        unfold opensOpt
        cases t0s.headD none with
        | none => exact tri_pure_iff.2 ⟨rfl, fun _ h => by cases h⟩
        | some tr =>
          refine (tri_opensComp f w.pt.decPos w.posAt0 w.place
            (fun j p h => (hW.1.place_posAt0 j p h).2) m.1 tr _ _ _ vs).mono ?_
          rintro g vs' ⟨rfl, h1, -⟩
          refine ⟨rfl, fun tr' htr p hown hp => ?_⟩
          obtain rfl := Option.some.inj htr
          exact h1 p hp
            ⟨w.place p, List.mem_range.2 (hW.1.place_lt0 p hown), hW.1.posAt0_place p hown⟩
      refine Tri.bind h0 fun g0 vs1 hg0 => ?_
      obtain ⟨rfl, hg0⟩ := hg0
      have h1 : Tri f
          (opensOpt (K := K) (L := L) w.pt.decPos w.posAtJ w.depthJ m.1 (tjs.headD none)
            (fun p => isRead (.inl p)) g0)
          vs1 fun g vs' =>
            vs' = vs1 ∧
            (∀ tr, tjs.headD none = some tr →
              ∀ p,
                a.own p = true → isRead (.inl p) = true → g p = some (opT w.place vs1 tr m.1 p)) ∧
            ∀ p, a.own p = false → g p = g0 p := by
        unfold opensOpt
        cases tjs.headD none with
        | none => exact tri_pure_iff.2 ⟨rfl, fun _ h => (by cases h), fun _ _ => rfl⟩
        | some tr =>
          refine (tri_opensComp f w.pt.decPos w.posAtJ w.place
            (fun j p h => (hW.1.place_posAtJ j p h).2) m.1 tr _ _ _ vs1).mono ?_
          rintro g vs' ⟨rfl, h1, h2⟩
          refine ⟨rfl, fun tr' htr p hown hp => ?_, fun p hown => h2 p fun j _ h => ?_⟩
          · obtain rfl := Option.some.inj htr
            exact h1 p hp
              ⟨w.place p, List.mem_range.2 (hW.1.place_ltJ p hown), hW.1.posAtJ_place p hown⟩
          · rw [(hW.1.place_posAtJ j p h).1] at hown
            cases hown
      refine Tri.bind h1 fun g1 vs2 hg1 => ?_
      obtain ⟨rfl, hg1, hg1'⟩ := hg1
      refine Tri.bind (tri_opensB s A W hW.2 τ tjs.tail t0s.tail (fun p => isRead (.inr p)) vs2)
        fun g2 vs3 hg2 => tri_pure_iff.2 ?_
      obtain ⟨rfl, hg2⟩ := hg2
      exact ⟨rfl, fun tr htr p hown hp => (hg1' p hown).trans (hg0 tr htr p hown hp), hg1, hg2⟩

/-! ## Part 2. Checks -/

/-- A check that the compiled verifier lets pass: well formed, in a tree of depth at most D, and
accepted. -/
def GoodCheck (D : ℕ) (c : Check lam L) : Prop :=
  c.wellFormed = true ∧ c.depth ≤ D ∧ EvalsTo f (runCheck (K := K) c) true

/-- is j the leaf of a read position -/
def readAt {r : Round} (posAt : ℕ → Option r.Pos) (isRead : r.Pos → Bool) (j : ℕ) : Bool :=
  match posAt j with
  | some p => isRead p
  | none => false

theorem checksComp_ok {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (tr : TTree) (vs : List Bits) (htr : TTreeOK f sMT vs tr depth (bodyAt posAt emb o))
    (isRead : r.Pos → Bool) (g : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hg : ∀ j p, posAt j = some p → isRead p = true → g p = some (opT place vs tr o p)) (D : ℕ)
    (hD : depth ≤ D) :
    ∀ js : List ℕ, (∀ j ∈ js, j < 2 ^ depth) →
      ∃ cs,
        checksComp posAt depth emb (dv lam vs tr.root) isRead g js = some cs ∧
        (∀ c ∈ cs, GoodCheck f D c) ∧
        cs.length = (js.filter (readAt posAt isRead)).length
  | [], _ => ⟨[], rfl, (fun _ h => by cases h), rfl⟩
  | j :: js, hjs => by
      obtain ⟨cs, h1, h2, h3⟩ := checksComp_ok posAt place hpl depth emb o tr vs htr isRead g hg D
        hD js fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')
      cases hpos : posAt j with
      | none =>
        refine ⟨cs, ?_, h2, ?_⟩
        · simp only [checksComp, hpos, h1]
        · rw [List.filter_cons_of_neg (by simp [readAt, hpos]), h3]
      | some p =>
        by_cases hr : isRead p = true
        · have hgood := check_of_ttreeOK f htr (hjs j List.mem_cons_self)
          have hleaf : bodyAt posAt emb o j = emb p (r.rd o p) := by simp only [bodyAt, hpos]
          rw [hleaf] at hgood
          refine ⟨(⟨⟨emb p (opT (lam := lam) place vs tr o p).sym,
                  (opT (lam := lam) place vs tr o p).salt⟩,
                j,
                (opT (lam := lam) place vs tr o p).path,
                dv lam vs tr.root,
                depth⟩ : Check lam L) :: cs,
            ?_, ?_, ?_⟩
          · simp only [checksComp, hpos, hr, if_true, hg j p hpos hr, h1]
          · intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · simp only [opT, hpl j p hpos]
              exact ⟨hgood.1, hD, hgood.2⟩
            · exact h2 c hc
          · rw [List.filter_cons_of_pos (by simp [readAt, hpos, hr]),
              List.length_cons, List.length_cons, h3]
        · refine ⟨cs, ?_, h2, ?_⟩
          · simp only [checksComp, hpos, hr, h1, Bool.false_eq_true, if_false]
          · rw [List.filter_cons_of_neg (by simp [readAt, hpos, hr]), h3]

theorem length_filter_readAt_le {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (isRead : r.Pos → Bool) (B : Finset r.Pos)
    (hB : ∀ j p, posAt j = some p → isRead p = true → p ∈ B) (n : ℕ) :
    ((List.range n).filter (readAt posAt isRead)).length ≤ B.card := by
  classical
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  refine le_trans (Finset.card_le_card (t := B.image place) fun j hj => ?_) Finset.card_image_le
  have hj' := (List.mem_filter.1 (List.mem_toFinset.1 hj)).2
  cases hpos : posAt j with
  | none => simp [readAt, hpos] at hj'
  | some p =>
    simp only [readAt, hpos] at hj'
    exact Finset.mem_image.2 ⟨p, hB j p hpos hj', hpl j p hpos⟩

/-- One component, under the hypotheses below: good checks, at most as many as B has elements (B
holds every read position). -/
theorem checksOpt_ok {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (tr : Option TTree) (rt : Option (Dig lam)) (vs : List Bits)
    (htr : CompOK f sMT vs tr rt depth (bodyAt posAt emb o)) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hg : ∀ t,
      tr = some t → ∀ j p, posAt j = some p → isRead p = true → g p = some (opT place vs t o p))
    (D : ℕ) (hD : depth ≤ D) (B : Finset r.Pos)
    (hB : ∀ j p, posAt j = some p → isRead p = true → p ∈ B) :
    ∃ cs,
      checksOpt posAt depth emb rt isRead g = some cs ∧
      (∀ c ∈ cs, GoodCheck f D c) ∧
      cs.length ≤ B.card := by
  match tr, rt, htr with
  | none, none, _ => exact ⟨[], rfl, (fun _ h => by cases h), Nat.zero_le _⟩
  | some t, some c, htr =>
    obtain ⟨cs, h1, h2, h3⟩ := checksComp_ok f posAt place hpl depth emb o t vs htr.1 isRead g
      (hg t rfl) D hD (List.range (2 ^ depth)) fun j hj => List.mem_range.1 hj
    refine ⟨cs, ?_, h2, by rw [h3]; exact length_filter_readAt_le posAt place hpl isRead B hB _⟩
    rw [htr.2]
    exact h1

/-- The trees of one component from number k on (`posAt n j`: the position at leaf j of tree number
n; `leaf n`: the leaves of tree number k + n), each kept correctly, against their own roots, under
the hypotheses below: for each tree good checks, and in all at most as many as B has elements (B
holds every read position of these trees). hpl also says that a position stands in one tree only:
else it would be counted twice. -/
theorem checksTrees_ok {sMT : ℕ} {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (tree place : r.Pos → ℕ) (hpl : ∀ n j p, posAt n j = some p → tree p = n ∧ place p = j)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (vs : List Bits) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) (D : ℕ) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree) (leaf : ℕ → ℕ → Body L),
      (∀ n, leaf n = bodyAt (posAt (k + n)) emb o) →
      OTreesOK f sMT vs ds trs leaf →
      (∀ n t, trs[n]? = some t →
        ∀ j p, posAt (k + n) j = some p → isRead p = true → g p = some (opT place vs t o p)) →
      (∀ d ∈ ds, d ≤ D) →
      ∀ B : Finset r.Pos, (∀ n j p, k ≤ n → posAt n j = some p → isRead p = true → p ∈ B) →
        ∃ l,
          checksTrees posAt emb isRead g k ds (rootsV lam vs trs) = some l ∧
          (∀ z ∈ l, ∀ c ∈ z.2.2, GoodCheck f D c) ∧
          (l.flatMap fun z => z.2.2).length ≤ B.card
  | _, [], [], _, _, _, _, _, _, _ =>
    ⟨[], by simp only [checksTrees], (fun _ h => by cases h), Nat.zero_le _⟩
  | _, [], _ :: _, _, _, hOK, _, _, _, _ => False.elim hOK
  | _, _ :: _, [], _, _, hOK, _, _, _, _ => False.elim hOK
  | k, d :: ds, tr :: trs, leaf, hleaf, hOK, hg, hD, B, hB => by
      obtain ⟨h0, hrest⟩ := hOK
      rw [hleaf 0] at h0
      obtain ⟨a, a1, a2, a3⟩ := checksComp_ok f (posAt k) place (fun j p h => (hpl k j p h).2) d
        emb o tr vs h0 isRead g (hg 0 tr List.getElem?_cons_zero) D (hD d List.mem_cons_self)
        (List.range (2 ^ d)) fun j hj => List.mem_range.1 hj
      have a4 : a.length ≤ (B.filter fun p => tree p = k).card := by
        rw [a3]
        exact length_filter_readAt_le (posAt k) place (fun j p h => (hpl k j p h).2) isRead _
          (fun j p hp hr => Finset.mem_filter.2 ⟨hB k j p le_rfl hp hr, (hpl k j p hp).1⟩) _
      obtain ⟨b, b1, b2, b3⟩ := checksTrees_ok posAt tree place hpl emb o vs isRead g D (k + 1) ds
        trs (fun n => leaf (n + 1))
        (fun n => (hleaf (n + 1)).trans (by rw [show k + (n + 1) = k + 1 + n by omega])) hrest
        (fun n t ht j p hp hr =>
          hg (n + 1) t (by rw [List.getElem?_cons_succ]; exact ht) j p
            (by rw [show k + (n + 1) = k + 1 + n by omega]; exact hp) hr)
        (fun e he => hD e (List.mem_cons_of_mem _ he)) (B.filter fun p => ¬ tree p = k)
        fun n j p hn hp hr =>
          Finset.mem_filter.2 ⟨hB n j p (by omega) hp hr, by rw [(hpl n j p hp).1]; omega⟩
      refine ⟨(d, dv lam vs tr.root, a) :: b, ?_, fun z hz c hc => ?_, ?_⟩
      · show checksTrees posAt emb isRead g k (d :: ds) (dv lam vs tr.root :: rootsV lam vs trs) = _
        simp only [checksTrees, a1, b1]
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact a2 c hc
        · exact b2 z hz c hc
      · rw [List.flatMap_cons, List.length_append]
        exact le_trans (Nat.add_le_add a4 b3)
          (le_of_eq (Finset.card_filter_add_card_filter_not (s := B) fun p => tree p = k))

/-- One component with a list of trees, under the hypotheses below (hpl as in `checksTrees_ok`): the
checks of all its trees are good, and at most as many as B has elements (B holds every read position
of the component). -/
theorem checksOfTrees_ok {sMT : ℕ} {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (tree place : r.Pos → ℕ) (hpl : ∀ n j p, posAt n j = some p → tree p = n ∧ place p = j)
    (ds : List ℕ) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (trs : List TTree)
    (rts : List (Dig lam)) (vs : List Bits)
    (htr : CompsOK f sMT vs trs rts ds fun n => bodyAt (posAt n) emb o) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hg : ∀ n t, trs[n]? = some t →
      ∀ j p, posAt n j = some p → isRead p = true → g p = some (opT place vs t o p))
    (D : ℕ) (hD : ∀ d ∈ ds, d ≤ D) (B : Finset r.Pos)
    (hB : ∀ n j p, posAt n j = some p → isRead p = true → p ∈ B) :
    ∃ cs,
      checksOfTrees posAt ds emb rts isRead g = some cs ∧
      (∀ c ∈ cs, GoodCheck f D c) ∧
      cs.length ≤ B.card := by
  rcases htr with ⟨-, rfl⟩ | ⟨htr, rfl⟩
  · refine ⟨[], ?_, (fun _ h => by cases h), Nat.zero_le _⟩
    unfold checksOfTrees
    cases ds <;> simp only [checksTrees] <;> rfl
  · obtain ⟨l, l1, l2, l3⟩ := checksTrees_ok f posAt tree place hpl emb o vs isRead g D 0 ds trs _
      (fun n => by rw [Nat.zero_add]) htr
      (fun n t ht j p hp hr => hg n t ht j p (by rw [Nat.zero_add] at hp; exact hp) hr) hD B
      fun n j p _ hp hr => hB n j p hp hr
    refine ⟨l.flatMap fun z => z.2.2, by unfold checksOfTrees; rw [l1]; rfl, fun c hc => ?_, l3⟩
    obtain ⟨z, hz, hc⟩ := List.mem_flatMap.1 hc
    exact l2 z hz c hc

theorem checksB_ok {sMT : ℕ} (vs : List Bits) (D : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W → RoundsQueryLayout.DepthLe D s A W →
      ∀ (embS : (p : OPos s) → OSym s p → Body L)
          (τ : Tr s) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam s),
        RoundsOK f sMT vs s A W embS τ tjs t0s rts →
        ∀ (isRead : OPos s → Bool) (g : (p : OPos s) → Option (Opening lam (OSym s p))),
          OpensOK vs s A W τ tjs t0s isRead g →
          ∀ B : Finset (OPos s), (∀ p, isRead p = true → p ∈ B) →
            ∃ cs,
              checksB s A W embS rts isRead g = some cs ∧
              (∀ c ∈ cs, GoodCheck f D c) ∧
              cs.length ≤ B.card
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨[], rfl, (fun _ h => by cases h), Nat.zero_le _⟩
  | r :: s, (a, A), (w, W), hW, hD, embS, (m, _, τ), tjs, t0s, (rt, rts), htr, isRead, g, hg, B, hB => by
      classical
      obtain ⟨tj, t0, tjs', t0s', rfl, rfl, h0, hj, -, -, -, -, hrest⟩ := htr
      let BL : Finset r.Pos := Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from B)
      have hBL : ∀ p, isRead (.inl p) = true → p ∈ BL := fun p hp =>
        Finset.mem_toLeft.2 (hB (.inl p) hp)
      obtain ⟨c0, a1, a2, a3⟩ := checksOpt_ok f w.posAt0 w.place
        (fun j p h => (hW.1.place_posAt0 j p h).2) w.depth0 (fun p => embS (.inl p))
        m.1 t0 rt.1.join vs h0 (fun p => isRead (.inl p)) (fun p => g (.inl p))
        (fun t ht j p hpos hp =>
          hg.1 t (by rw [List.headD_cons]; exact ht) p (hW.1.place_posAt0 j p hpos).1 hp)
        D hD.1.1 (BL.filter fun p => a.own p = false)
        fun j p hpos hp => Finset.mem_filter.2 ⟨hBL p hp, (hW.1.place_posAt0 j p hpos).1⟩
      obtain ⟨cj, b1, b2, b3⟩ := checksOpt_ok f w.posAtJ w.place
        (fun j p h => (hW.1.place_posAtJ j p h).2) w.depthJ (fun p => embS (.inl p))
        m.1 tj rt.2.join vs hj (fun p => isRead (.inl p)) (fun p => g (.inl p))
        (fun t ht j p hpos hp =>
          hg.2.1 t (by rw [List.headD_cons]; exact ht) p (hW.1.place_posAtJ j p hpos).1 hp)
        D hD.1.2 (BL.filter fun p => ¬ a.own p = false) fun j p hpos hp =>
          Finset.mem_filter.2 ⟨hBL p hp, by rw [(hW.1.place_posAtJ j p hpos).1]; simp⟩
      obtain ⟨cr, d1, d2, d3⟩ := checksB_ok vs D s A W hW.2 hD.2 (fun p => embS (.inr p))
        τ tjs' t0s' rts hrest (fun p => isRead (.inr p)) (fun p => g (.inr p)) hg.2.2
        (Finset.toRight (show Finset (r.Pos ⊕ OPos s) from B))
        fun p hp => Finset.mem_toRight.2 (hB (.inr p) hp)
      refine ⟨c0 ++ cj ++ cr, ?_, ?_, ?_⟩
      · simp only [checksB, a1, b1, d1]
      · intro c hc
        rcases List.mem_append.1 hc with h | h
        · rcases List.mem_append.1 h with h | h
          · exact a2 c h
          · exact b2 c h
        · exact d2 c h
      · have hc := Finset.card_toLeft_add_card_toRight (u := (show Finset (r.Pos ⊕ OPos s) from B))
        have hs := Finset.card_filter_add_card_filter_not (s := BL) fun p => a.own p = false
        rw [List.length_append, List.length_append]
        calc
          _ ≤ ((BL.filter fun p => a.own p = false).card +
                  (BL.filter fun p => ¬ a.own p = false).card) +
                (Finset.toRight (show Finset (r.Pos ⊕ OPos s) from B)).card :=
            Nat.add_le_add (Nat.add_le_add a3 b3) d3
          _ = B.card := by rw [hs]; exact hc

theorem evalsTo_runChecks :
    ∀ cs : List (Check lam L),
      (∀ c ∈ cs, EvalsTo f (runCheck (K := K) c) true) → EvalsTo f (runChecks (K := K) cs) true
  | [], _ => rfl
  | c :: cs, h =>
      (evaluates_eager f).bind (h c List.mem_cons_self)
        ((evaluates_eager f).bind
          (evalsTo_runChecks cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
          ((evaluates_eager f).pure _))

/-! ## Part 3. The transcript that the verifier builds -/

theorem join_split {r : Round} (a : RAnn r) (m : r.Msg) : a.join (a.split m).1 (a.split m).2 = m :=
  a.split.symm_apply_apply m

/-- Under `a.Coherent`: where a component that is not sent is empty, the plain part that the
verifier uses is the prover's. -/
theorem effPlain_eq {r : Round} {a : RAnn r} (hC : a.Coherent) (rt : RtC lam × RtC lam)
    (h1 : rt.1 = none → a.NoShared) (h2 : rt.2 = none → a.NoSlot) (m : r.Msg) :
    effPlain a rt m.2 = m.2 := by
  have hm := hC.plain_join (a.split m).1 (a.split m).2
  rw [join_split] at hm
  have hd := hC.plain_join (a.split (r.dOrc, r.dPlain)).1 (a.split (r.dOrc, r.dPlain)).2
  rw [join_split] at hd
  have e1 : (if rt.1.isSome then (a.plain m.2).1 else (a.plain r.dPlain).1) = (a.plain m.2).1 := by
    cases h : rt.1 with
    | some c => rfl
    | none =>
      haveI := (h1 h).2
      show (a.plain r.dPlain).1 = _
      rw [hm, hd, Subsingleton.elim (a.split (r.dOrc, r.dPlain)).1 (a.split m).1]
  have e2 : (if rt.2.isSome then (a.plain m.2).2 else (a.plain r.dPlain).2) = (a.plain m.2).2 := by
    cases h : rt.2 with
    | some c => rfl
    | none =>
      haveI := (h2 h).2
      show (a.plain r.dPlain).2 = _
      rw [hm, hd, Subsingleton.elim (a.split (r.dOrc, r.dPlain)).2 (a.split m).2]
  unfold effPlain
  rw [e1, e2, Prod.mk.eta, Equiv.symm_apply_apply]

theorem effPlains_eq {sMT : ℕ} {vs : List Bits} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (τ : Tr s) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam s),
      A.Coherent → RoundsOK f sMT vs s A W embS τ tjs t0s rts →
      effPlains s A rts τ.plains = τ.plains
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (_, W), embS, (m, _, τ), _, _, (rt, rts), hC, h => by
      obtain ⟨tj, t0, tjs', t0s', -, -, -, -, h1, h2, -, -, hr⟩ := h
      show (effPlain _ rt m.2, effPlains s A rts τ.plains) = (m.2, τ.plains)
      rw [effPlain_eq hC.1 rt h1 h2 m, effPlains_eq s A W _ τ tjs' t0s' rts hC.2 hr]

theorem rho_mkTr :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (pls : Plains s) (ρ : Rho s)
        (g : (p : OPos s) → Option (Opening lam (OSym s p))),
      (mkTr s A W rts pls ρ g).rho = ρ
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (_, W), (_, rts), (_, pls), (c, ρ), g =>
    congrArg (fun z => (c, z)) (rho_mkTr s A W rts pls ρ fun p => g (.inr p))

theorem plains_mkTr :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (pls : Plains s) (ρ : Rho s)
        (g : (p : OPos s) → Option (Opening lam (OSym s p))),
      (mkTr s A W rts pls ρ g).plains = effPlains s A rts pls
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (_, W), (rt, rts), (pl, pls), (_, ρ), g =>
      congrArg (fun z => (effPlain a rt pl, z)) (plains_mkTr s A W rts pls ρ fun p => g (.inr p))

/-- Under `RoundsOK`, `OpensOK`: where the verifier reads, the transcript that it builds shows the
prover's symbols. -/
theorem read_mkTr {sMT : ℕ} {vs : List Bits} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (τ : Tr s) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam s),
      RoundsOK f sMT vs s A W embS τ tjs t0s rts →
      ∀ (isRead : OPos s → Bool) (g : (p : OPos s) → Option (Opening lam (OSym s p))),
        OpensOK vs s A W τ tjs t0s isRead g →
        ∀ (pls : Plains s) (ρ : Rho s) (p : OPos s),
          isRead p = true → (mkTr s A W rts pls ρ g).read p = τ.read p
  | _ :: s, (a, A), (w, W), embS, (m, _, τ), _, _, ((rt0, rtj), rts), h, isRead, g, hg, (_, pls), (_, ρ), .inl p, hp => by
      obtain ⟨tj, t0, tjs', t0s', rfl, rfl, h0, hj, -, -, h1, h2, -⟩ := h
      show Round.rd _ (w.pt.ofSyms _) p = Round.rd _ m.1 p
      rw [w.pt.rd_ofSyms]
      cases hown : a.own p with
      | true =>
        generalize hcj : rtj.join = cj at hj h2
        match tj, cj, hj, h2, hg with
        | none, none, _, h2, _ => rw [h2 rfl p] at hown; cases hown
        | some tr, some c, _, _, hg =>
          have hgp := hg.2.1 tr rfl p hown hp
          simp only [rootAt, hown, if_true, hcj, Option.isSome_some, hgp]
          rfl
      | false =>
        generalize hc0 : rt0.join = c0 at h0 h1
        match t0, c0, h0, h1, hg with
        | none, none, _, h1, _ => rw [h1 rfl p] at hown; cases hown
        | some tr, some c, _, _, hg =>
          have hgp := hg.1 tr rfl p hown hp
          simp only [rootAt, hown, Bool.false_eq_true, if_false, hc0, Option.isSome_some, hgp]
          rfl
  | _ :: s, (_, A), (_, W), embS, (_, _, τ), _, _, (_, rts), h, isRead, g, hg, (_, pls), (_, ρ), .inr p, hp => by
      obtain ⟨tj, t0, tjs', t0s', rfl, rfl, -, -, -, -, -, -, hr⟩ := h
      exact read_mkTr s A W _ τ tjs' t0s' rts hr (fun p => isRead (.inr p))
        (fun p => g (.inr p)) hg.2.2 pls ρ p hp

/-! ## Part 4. External positions -/

/-- the honest opening of an external position -/
def honestExt {E : ExtSpec} (we : WireE E) (vs : List Bits) (trees : List (TreeH lam))
    (y : E.Str) (p : E.Pos) : Opening lam E.Sym :=
  ⟨E.rd y p, saltVal vs ((trees.getD (we.which p) ⟨[], []⟩).salts.getD (we.leaf p) none),
    pathOf (trees.getD (we.which p) ⟨[], []⟩).levels (we.leaf p)⟩

theorem tri_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) (vs : List Bits), Tri f (opensExtB (K := K) (L := L) we y trees isRead ps) vs fun g vs' =>
      vs' = vs ∧ ∀ p, isRead p = true → p ∈ ps → g p = some (honestExt we vs trees y p)
  | [], vs => tri_pure_iff.2 ⟨rfl, fun _ _ h => by cases h⟩
  | p0 :: ps, vs => by
      refine Tri.bind (tri_opensExtB we y trees isRead ps vs) fun g vs1 hg => ?_
      obtain ⟨rfl, hg⟩ := hg
      by_cases hr : isRead p0 = true
      · rw [if_pos hr]
        refine Tri.bind (tri_openE f _ _ _ vs1) fun op vs2 hop => tri_pure_iff.2 ?_
        obtain ⟨rfl, rfl⟩ := hop
        refine ⟨rfl, fun p hp hm => ?_⟩
        by_cases hpp : p = p0
        · subst hpp
          rw [@Function.update_self _ _ we.dec]; rfl
        · rw [@Function.update_of_ne _ _ we.dec _ _ hpp]
          exact hg p hp ((List.mem_cons.1 hm).resolve_left hpp)
      · rw [if_neg hr]
        refine tri_pure_iff.2
          ⟨rfl, fun p hp hm => hg p hp ((List.mem_cons.1 hm).resolve_left fun h => hr (h ▸ hp))⟩

/-- The external trees fit the external strings: the tree of every external position satisfies
`TreeOK` and has the depth `we.depth` of the wire record, and the leaf of the position holds its
symbol. -/
def ExtOK (sMT : ℕ) {E : ExtSpec} (we : WireE E) (embE : E.Sym → Body L) (vs : List Bits)
    (trees : List (TreeH lam)) (y : E.Str) : Prop :=
  ∀ p : E.Pos,
    we.which p < trees.length ∧
    we.leaf p < 2 ^ we.depth ∧
    ∃ leaf,
      TreeOK f sMT vs (trees.getD (we.which p) ⟨[], []⟩) we.depth leaf ∧
      (leaf (we.leaf p)).1 = embE (E.rd y p)

variable {f} in
theorem ExtOK.mono {sMT : ℕ} {E : ExtSpec} {we : WireE E} {embE : E.Sym → Body L}
    {vs vs' : List Bits} (hp : vs <+: vs') {trees : List (TreeH lam)} {y : E.Str}
    (h : ExtOK f sMT we embE vs trees y) :
    ExtOK f sMT we embE vs' trees y := fun p => by
  obtain ⟨h1, h2, leaf, h3, h4⟩ := h p
  exact ⟨h1, h2, leaf, h3.mono hp, h4⟩

theorem checksExt_ok {sMT : ℕ} {E : ExtSpec} (we : WireE E) (embE : E.Sym → Body L) (vs : List Bits)
    (trees : List (TreeH lam)) (y : E.Str) (hext : ExtOK f sMT we embE vs trees y)
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) (D : ℕ) (hD : we.depth ≤ D) :
    ∀ ps : List E.Pos, (∀ p ∈ ps, isRead p = true → g p = some (honestExt we vs trees y p)) →
      ∃ cs,
        checksExt we embE (trees.map TreeH.root) isRead g ps = some cs ∧
        (∀ c ∈ cs, GoodCheck f D c) ∧
        cs.length = (ps.filter isRead).length
  | [], _ => ⟨[], rfl, (fun _ h => by cases h), rfl⟩
  | p :: ps, hg => by
      obtain ⟨cs, h1, h2, h3⟩ := checksExt_ok we embE vs trees y hext isRead g D hD ps
        fun p' hp' => hg p' (List.mem_cons_of_mem _ hp')
      by_cases hr : isRead p = true
      · obtain ⟨e1, e2, leaf, e3, e4⟩ := hext p
        have hgood := check_of_treeOK f e3 e2
        rw [e4] at hgood
        have hroot : (trees.map TreeH.root).getD (we.which p) default =
            (trees.getD (we.which p) ⟨[], []⟩).root := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem e1]
        refine ⟨(⟨⟨embE (honestExt we vs trees y p).sym, (honestExt we vs trees y p).salt⟩,
              we.leaf p,
              (honestExt we vs trees y p).path,
              (trees.map TreeH.root).getD (we.which p) default,
              we.depth⟩ : Check lam L) :: cs,
          ?_, ?_, ?_⟩
        · simp only [checksExt, hr, if_true, hg p List.mem_cons_self hr, h1]
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · simp only [honestExt, hroot]
            exact ⟨hgood.1, hD, hgood.2⟩
          · exact h2 c hc
        · rw [List.filter_cons_of_pos hr, List.length_cons, List.length_cons, h3]
      · refine ⟨cs, ?_, h2, ?_⟩
        · simp only [checksExt, hr, h1, Bool.false_eq_true, if_false]
        · rw [List.filter_cons_of_neg hr, h3]

theorem length_filter_le_card {α : Type} (l : List α) (hl : l.Nodup) (φ : α → Bool) (A : Finset α)
    (hA : ∀ a, φ a = true → a ∈ A) : (l.filter φ).length ≤ A.card := by
  classical
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  exact Finset.card_le_card fun a ha => hA a (List.mem_filter.1 (List.mem_toFinset.1 ha)).2

/-! ## After the chain -/

/-- What the verifier does after it has recomputed the chain, on the honest proof string, under the
hypotheses below: it accepts. rest is what follows the checks of the openings (the check in the
request tree, and the conjunction), as a function of the outcome of these checks and of the decision
of the verifier of the protocol. -/
theorem evalsTo_afterChain {sMT : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (hwq : wq.OKG) (hloc : Q.loc.IsLocal)
    (hC : Q.ann.Coherent) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embE : E.Sym → Body L) (trees : List (TreeH lam)) (y : E.Str)
    (x : Y) (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees y) (τ : Tr Q.loc.shape)
    (hτ : Q.loc.accept x y τ = true) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam Q.loc.shape)
    (htr : RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS τ tjs t0s rts)
    (g1 : (p : OPos Q.loc.shape) → Option (Opening lam (OSym Q.loc.shape p)))
    (isR1 : OPos Q.loc.shape → Bool)
    (hR1 : ∀ p, isR1 p = true ↔ p ∈ Q.loc.reads x τ.rho τ.plains)
    (hg1 : OpensOK vs Q.loc.shape Q.ann wq.sh τ tjs t0s isR1 g1)
    (g2 : E.Pos → Option (Opening lam E.Sym))
    (isR2 : E.Pos → Bool) (hR2 : ∀ p, isR2 p = true ↔ p ∈ Q.loc.extReads x τ.rho)
    (hg2 : ∀ p, isR2 p = true → g2 p = some (honestExt wq.ext vs trees y p))
    (rest : Bool → Bool → TypedOracleComputation lam K L Bool)
    (hrest : EvalsTo f (rest true true) true) :
    EvalsTo f (match checksB Q.loc.shape Q.ann wq.sh embS rts isR1 g1,
        checksExt wq.ext embE (trees.map TreeH.root) isR2 g2 wq.ext.all with
      | some a, some b =>
          if (a ++ b).length ≤ wq.nOpen ∧
              (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) then do
            let ok ← runChecks (K := K) (a ++ b)
            rest ok (Q.loc.accept x (wq.ext.build fun p => (g2 p).map Opening.sym)
                (mkTr Q.loc.shape Q.ann wq.sh rts τ.plains τ.rho g1))
          else pure false
      | _, _ => pure false) true := by
  obtain ⟨a, a1, a2, a3⟩ := checksB_ok f vs wq.maxDepth Q.loc.shape Q.ann wq.sh hwq.sh hwq.depth
    embS τ tjs t0s rts htr isR1 g1 hg1 (Q.loc.reads x τ.rho τ.plains) fun p hp => (hR1 p).1 hp
  obtain ⟨b, b1, b2, b3⟩ := checksExt_ok f wq.ext embE vs trees y hext isR2 g2 wq.maxDepth hDe
    wq.ext.all fun p _ hp => hg2 p hp
  have hb : b.length ≤ (Q.loc.extReads x τ.rho).card := by
    rw [b3]; exact length_filter_le_card _ hwq.ext.nodup isR2 _ fun p hp => (hR2 p).1 hp
  have hgood : ∀ c ∈ a ++ b, GoodCheck f wq.maxDepth c := fun c hc => by
    rcases List.mem_append.1 hc with h | h
    · exact a2 c h
    · exact b2 c h
  have hcond : (a ++ b).length ≤ wq.nOpen ∧
      (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true := by
    refine ⟨?_, List.all_eq_true.2 fun c hc => ?_⟩
    · rw [List.length_append]
      exact le_trans (Nat.add_le_add a3 hb) (hwq.opens x τ.rho τ.plains)
    · simp [(hgood c hc).1, (hgood c hc).2.1]
  have hacc : Q.loc.accept x (wq.ext.build fun p => (g2 p).map Opening.sym)
        (mkTr Q.loc.shape Q.ann wq.sh rts τ.plains τ.rho g1) = true := by
    rw [← hτ]
    refine (hloc x y _ τ _ (rho_mkTr _ _ _ _ _ _ _).symm
      ((plains_mkTr _ _ _ _ _ _ _).trans (effPlains_eq f _ _ _ embS τ tjs t0s rts hC htr)).symm
      (fun p hp => ?_) fun p hp => ?_).symm
    · refine (hwq.ext.build_rd _ p _ ?_).symm
      rw [hg2 p ((hR2 p).2 hp)]; rfl
    · exact (read_mkTr f _ _ _ embS τ tjs t0s rts htr isR1 g1 hg1 _ _ p ((hR1 p).2 hp)).symm
  simp only [a1, b1]
  rw [if_pos hcond, hacc]
  exact (evaluates_eager f).bind (evalsTo_runChecks f _ fun c hc => (hgood c hc).2.2) hrest

end Compile.Batch.Cmpl
