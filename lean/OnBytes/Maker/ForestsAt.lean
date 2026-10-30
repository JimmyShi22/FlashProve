-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ForestsAt.lean: what the forests are that the compiled verifier makes of the openings
at a stretch of written rounds (OnBytes/Maker/Wire.lean).

The compiled verifier (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, `forestsB`) gathers the checks of
the openings tree by tree, and walks each tree's checks together ("a forest"). This file says which
forests there are at the wire records `wiresLo` and `wiresSh`: each is one tree of the stretch.

  `checksComp_mem`, `checksTrees_mem`, `mem_forestsT`, `forestsB_cons`
        for any round and wire record: each check of a tree is the check of a position of that tree
        that is read and has an opening; a forest of trees that are walked whole; one round's
        forests and the later rounds'.
  `IsTree C ds Wr emb R rd f T n sh c`
        the forest T is the tree number n of the stretch: the tree has the shape sh in the rounds'
        data; T has its depth; T's one root is c; c is the root, and sh.a the depth, that the wire
        records and the roots R give to each position of the tree; and each check of T bears the
        tree number 0 and is the check of a position q of the tree n that is read, with the opening
        that f has at q.
  `forests_lo`, `forests_sh`
        **each forest at a stretch of local, or of shared, rounds is a tree of the stretch.**
  `forests_behind`
        a silent round in front adds no forest.

Not claimed. That the forests are there (OnBytes/TypedOracleCompiler/Joined/K/Openings.lean, `exists_forestsB`).
That a walk says yes. Nothing on soundness.


-/
import OnBytes.Maker.TypingOpened

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-! ## Any round -/

section Any
variable {lam K : ℕ}

theorem checksComp_mem {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ) (cs : List (Check lam L))
    (h : checksComp posAt depth emb rt isRead f js = some cs) :
    ∀ c ∈ cs, ∃ j p op, posAt j = some p ∧ isRead p = true ∧ f p = some op ∧
      c = ⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ :=
  forall_checksComp (P := fun c => ∃ j p op, posAt j = some p ∧ isRead p = true ∧
      f p = some op ∧ c = ⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩)
    posAt depth emb rt isRead f js cs h fun j _ p op h1 h2 h3 => ⟨j, p, op, h1, h2, h3, rfl⟩

theorem checksTrees_mem {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      ∀ z ∈ l, ∃ i, ds[i]? = some z.1 ∧ rt[i]? = some z.2.1 ∧
        ∀ c ∈ z.2.2, ∃ j p op, posAt (k + i) j = some p ∧ isRead p = true ∧ f p = some op ∧
          c = ⟨⟨emb p op.sym, op.salt⟩, j, op.path, z.2.1, z.1⟩
  | k, d0 :: ds, c0 :: rt, l, h, z, hz => by
    simp only [checksTrees] at h
    cases h1 : checksComp (posAt k) d0 emb c0 isRead f (List.range (2 ^ d0)) with
    | none => rw [h1] at h; cases h
    | some a =>
      cases h2 : checksTrees posAt emb isRead f (k + 1) ds rt with
      | none => rw [h1, h2] at h; cases h
      | some b =>
        rw [h1, h2] at h
        cases h
        rcases List.mem_cons.1 hz with rfl | hz'
        · exact ⟨0, rfl, rfl, checksComp_mem (posAt k) d0 emb c0 isRead f _ a h1⟩
        · obtain ⟨i, e1, e2, e3⟩ := checksTrees_mem posAt emb isRead f (k + 1) ds rt b h2 z hz'
          refine ⟨i + 1, by simpa using e1, by simpa using e2, fun c hc => ?_⟩
          obtain ⟨j, p, op, a1, a2, a3, a4⟩ := e3 c hc
          exact ⟨j, p, op, by rwa [show k + (i + 1) = k + 1 + i by omega], a2, a3, a4⟩
  | _, [], _, l, h, z, hz => by
    simp only [checksTrees] at h
    cases h
    cases hz
  | _, _ :: _, [], l, h, z, hz => by
    simp only [checksTrees] at h
    cases h
    cases hz

/-- A forest of trees that are walked whole. -/
theorem mem_forestsT {l : List (ℕ × Dig lam × List (Check lam L))} {T : Forest lam L}
    (h : T ∈ forestsT true l) :
    ∃ z ∈ l, (⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ : Forest lam L) = T := by
  obtain ⟨z, hz, hT⟩ := List.mem_flatMap.1 h
  exact ⟨z, hz, (List.mem_singleton.1 hT).symm⟩

/-- One round's forests, and the later rounds'. -/
theorem forestsB_cons {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam K r a}
    {W : RoundsQueryLayout lam K s A} {emb : (p : OPos (r :: s)) → OSym (r :: s) p → Body L}
    {rt : RtC lam × RtC lam} {R : RootsOfChain lam s} {rd : OPos (r :: s) → Bool}
    {f : (p : OPos (r :: s)) → Option (Opening lam (OSym (r :: s) p))}
    {Fs : List (Forest lam L)}
    (h : forestsB (r :: s) (a, A) (w, W) emb (rt, R) rd f = some Fs) :
    ∃ x y z,
      checksTrees w.posAt0 (fun p => emb (.inl p)) (fun p => rd (.inl p)) (fun p => f (.inl p)) 0
        w.depth0 (rt.1.getD []) = some x ∧
      checksTrees w.posAtJ (fun p => emb (.inl p)) (fun p => rd (.inl p)) (fun p => f (.inl p)) 0
        w.depthJ (rt.2.getD []) = some y ∧
      forestsB s A W (fun p => emb (.inr p)) R (fun p => rd (.inr p)) (fun p => f (.inr p)) =
        some z ∧
      forestsT w.pr0 x ++ (forestsT w.prJ y ++ z) = Fs := by
  simp only [forestsB] at h
  cases hx : checksTrees w.posAt0 (fun p => emb (.inl p)) (fun p => rd (.inl p))
      (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []) with
  | none => rw [hx] at h; cases h
  | some x =>
    cases hy : checksTrees w.posAtJ (fun p => emb (.inl p)) (fun p => rd (.inl p))
        (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []) with
    | none => rw [hx, hy] at h; cases h
    | some y =>
      cases hz : forestsB s A W (fun p => emb (.inr p)) R (fun p => rd (.inr p))
          (fun p => f (.inr p)) with
      | none => rw [hx, hy, hz] at h; cases h
      | some z =>
        rw [hx, hy, hz] at h
        exact ⟨x, y, z, rfl, rfl, rfl, Option.some.inj h⟩

end Any

/-! ## A stretch of written rounds -/

/-- **The forest T is the tree number n of the stretch.** -/
structure IsTree {K' : ℕ} (C : CK) (ds : List RDT) {A : RoundSplits (uLT C ds)}
    (Wr : RoundsQueryLayout 256 K' (uLT C ds) A) (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L)
    (R : RootsOfChain 256 (uLT C ds)) (rd : OPos (uLT C ds) → Bool)
    (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))) (T : Forest 256 L)
    (n : ℕ) (sh : Fmt.Shape) (c : Dig 256) : Prop where
  shape : treeShT ds n = some sh
  depth : T.depth = sh.a
  root : T.treeRoot = fun _ => c
  tree : ∀ x q, posAtST C ds n x = some q → treeOf (uLT C ds) A Wr R q = some (sh.a, c)
  checks : ∀ e ∈ T.cs, e.1 = 0 ∧ ∃ q op, posAtST C ds n e.2.j = some q ∧ rd q = true ∧
    f q = some op ∧ e.2 = ⟨⟨emb q op.sym, op.salt⟩, e.2.j, op.path, c, sh.a⟩

section Stretch
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **Each forest at a stretch of local rounds is a tree of the stretch.** -/
theorem forests_lo :
    ∀ (ds : List RDT) (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L)
      (R : RootsOfChain 256 (uLT C ds)) (rd : OPos (uLT C ds) → Bool)
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
      (Fs : List (Forest 256 L)),
      forestsB (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) emb R rd f = some Fs →
      ∀ T ∈ Fs, ∃ n sh c, IsTree C ds (wiresLo C K chal ds) emb R rd f T n sh c
  | [], _, _, _, _, Fs, h, T, hT => by
      obtain rfl : [] = Fs := Option.some.inj h
      cases hT
  | d :: ds, emb, (rt, R), rd, f, Fs, h, T, hT => by
      obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := forestsB_cons (a := RAnn.allLocal (roundT C d).up)
        (A := RoundSplits.allLocal (uLT C ds)) (w := wireLo C K chal d) (W := wiresLo C K chal ds) h
      have e0 : x = [] := by
        change checksTrees _ _ _ _ 0 [] _ = some x at hx
        simp only [checksTrees] at hx
        exact (Option.some.inj hx).symm
      subst e0
      have hT' : T ∈ forestsT true y ∨ T ∈ z := by
        rcases List.mem_append.1 hT with h1 | h1
        · cases h1
        · exact List.mem_append.1 h1
      rcases hT' with h1 | h1
      · obtain ⟨u, hu, rfl⟩ := mem_forestsT h1
        obtain ⟨i, e1, e2, e3⟩ := checksTrees_mem _ _ _ _ 0 _ _ y hy u hu
        have e1' : (d.trees.map (·.a))[i]? = some u.1 := e1
        rw [List.getElem?_map] at e1'
        obtain ⟨sh, hsh, ha⟩ := Option.map_eq_some_iff.1 e1'
        have hi : i < d.trees.length := (List.getElem?_eq_some_iff.1 hsh).1
        refine ⟨i, sh, u.2.1, ?_, ha.symm, rfl, fun x q hq => ?_, fun e he => ?_⟩
        · show (if i < d.trees.length then d.trees[i]? else _) = _
          rw [if_pos hi, hsh]
        · have hq' : (if i < d.trees.length then (posAtT d.trees i x).map Sum.inl else _) =
              some q := hq
          rw [if_pos hi] at hq'
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hq'
          show TypedOracleCompiler.Joined.treeAt (d.trees.map (·.a)) (rt.2.getD []) (treeT d.trees p) = _
          rw [(place_posAtT d.trees i x p hp).1, ha]
          exact treeAt_of e1 e2
        · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 he
          obtain ⟨j, p, op, a1, a2, a3, rfl⟩ := e3 c0 hc0
          refine ⟨rfl, .inl p, op, ?_, a2, a3, by rw [ha]⟩
          show (if i < d.trees.length then (posAtT d.trees i j).map Sum.inl else _) = _
          rw [if_pos hi]
          have a1' : posAtT d.trees i j = some p := by rw [Nat.zero_add] at a1; exact a1
          rw [a1']
          rfl
      · obtain ⟨n, sh, c, H⟩ := forests_lo ds _ R _ _ z hz T h1
        have hn : ¬ d.trees.length + n < d.trees.length := by omega
        refine ⟨d.trees.length + n, sh, c, ?_, H.depth, H.root, fun x q hq => ?_, fun e he => ?_⟩
        · show (if d.trees.length + n < d.trees.length then _ else
            treeShT ds (d.trees.length + n - d.trees.length)) = _
          rw [if_neg hn, Nat.add_sub_cancel_left]
          exact H.shape
        · have hq' : (if d.trees.length + n < d.trees.length then _ else
              (posAtST C ds (d.trees.length + n - d.trees.length) x).map Sum.inr) = some q := hq
          rw [if_neg hn, Nat.add_sub_cancel_left] at hq'
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hq'
          exact H.tree x p hp
        · obtain ⟨b1, q, op, b2, b3, b4, b5⟩ := H.checks e he
          refine ⟨b1, .inr q, op, ?_, b3, b4, b5⟩
          show (if d.trees.length + n < d.trees.length then _ else
            (posAtST C ds (d.trees.length + n - d.trees.length) e.2.j).map Sum.inr) = _
          rw [if_neg hn, Nat.add_sub_cancel_left, b2]
          rfl

/-- **The same at a stretch of shared rounds.** -/
theorem forests_sh :
    ∀ (ds : List RDT) (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L)
      (R : RootsOfChain 256 (uLT C ds)) (rd : OPos (uLT C ds) → Bool)
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
      (Fs : List (Forest 256 L)),
      forestsB (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) emb R rd
        f = some Fs →
      ∀ T ∈ Fs, ∃ n sh c, IsTree C ds (wiresSh C K chal ds) emb R rd f T n sh c
  | [], _, _, _, _, Fs, h, T, hT => by
      obtain rfl : [] = Fs := Option.some.inj h
      cases hT
  | d :: ds, emb, (rt, R), rd, f, Fs, h, T, hT => by
      obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := forestsB_cons (a := RAnn.ofShared .sh (roundT C d).up)
        (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (w := wireSh C K chal d)
        (W := wiresSh C K chal ds) h
      have e0 : y = [] := by
        change checksTrees _ _ _ _ 0 [] _ = some y at hy
        simp only [checksTrees] at hy
        exact (Option.some.inj hy).symm
      subst e0
      have hT' : T ∈ forestsT true x ∨ T ∈ z := by
        rcases List.mem_append.1 hT with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_append.1 h1 with h2 | h2
          · cases h2
          · exact Or.inr h2
      rcases hT' with h1 | h1
      · obtain ⟨u, hu, rfl⟩ := mem_forestsT h1
        obtain ⟨i, e1, e2, e3⟩ := checksTrees_mem _ _ _ _ 0 _ _ x hx u hu
        have e1' : (d.trees.map (·.a))[i]? = some u.1 := e1
        rw [List.getElem?_map] at e1'
        obtain ⟨sh, hsh, ha⟩ := Option.map_eq_some_iff.1 e1'
        have hi : i < d.trees.length := (List.getElem?_eq_some_iff.1 hsh).1
        refine ⟨i, sh, u.2.1, ?_, ha.symm, rfl, fun x q hq => ?_, fun e he => ?_⟩
        · show (if i < d.trees.length then d.trees[i]? else _) = _
          rw [if_pos hi, hsh]
        · have hq' : (if i < d.trees.length then (posAtT d.trees i x).map Sum.inl else _) =
              some q := hq
          rw [if_pos hi] at hq'
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hq'
          show TypedOracleCompiler.Joined.treeAt (d.trees.map (·.a)) (rt.1.getD []) (treeT d.trees p) = _
          rw [(place_posAtT d.trees i x p hp).1, ha]
          exact treeAt_of e1 e2
        · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 he
          obtain ⟨j, p, op, a1, a2, a3, rfl⟩ := e3 c0 hc0
          refine ⟨rfl, .inl p, op, ?_, a2, a3, by rw [ha]⟩
          show (if i < d.trees.length then (posAtT d.trees i j).map Sum.inl else _) = _
          rw [if_pos hi]
          have a1' : posAtT d.trees i j = some p := by rw [Nat.zero_add] at a1; exact a1
          rw [a1']
          rfl
      · obtain ⟨n, sh, c, H⟩ := forests_sh ds _ R _ _ z hz T h1
        have hn : ¬ d.trees.length + n < d.trees.length := by omega
        refine ⟨d.trees.length + n, sh, c, ?_, H.depth, H.root, fun x q hq => ?_, fun e he => ?_⟩
        · show (if d.trees.length + n < d.trees.length then _ else
            treeShT ds (d.trees.length + n - d.trees.length)) = _
          rw [if_neg hn, Nat.add_sub_cancel_left]
          exact H.shape
        · have hq' : (if d.trees.length + n < d.trees.length then _ else
              (posAtST C ds (d.trees.length + n - d.trees.length) x).map Sum.inr) = some q := hq
          rw [if_neg hn, Nat.add_sub_cancel_left] at hq'
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hq'
          exact H.tree x p hp
        · obtain ⟨b1, q, op, b2, b3, b4, b5⟩ := H.checks e he
          refine ⟨b1, .inr q, op, ?_, b3, b4, b5⟩
          show (if d.trees.length + n < d.trees.length then _ else
            (posAtST C ds (d.trees.length + n - d.trees.length) e.2.j).map Sum.inr) = _
          rw [if_neg hn, Nat.add_sub_cancel_left, b2]
          rfl

/-- A silent round in front adds no forest. -/
theorem forests_behind {T0 : Type} (t : T0) (a0 : RAnn (plainRound T0 t)) {s : Shape} {A : RoundSplits s}
    (W : RoundsQueryLayout 256 (K + 1) s A)
    (emb : (p : OPos (plainRound T0 t :: s)) → OSym (plainRound T0 t :: s) p → Body L)
    (R : RootsOfChain 256 (plainRound T0 t :: s)) (rd : OPos (plainRound T0 t :: s) → Bool)
    (f : (p : OPos (plainRound T0 t :: s)) → Option (Opening 256 (OSym (plainRound T0 t :: s) p)))
    (Fs : List (Forest 256 L))
    (h : forestsB (plainRound T0 t :: s) (a0, A) (wireSilent (K + 1) T0 t a0, W) emb R rd f =
      some Fs) :
    forestsB s A W (fun p => emb (.inr p)) R.2 (fun p => rd (.inr p)) (fun p => f (.inr p)) =
      some Fs := by
  obtain ⟨rt, R⟩ := R
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := forestsB_cons h
  change checksTrees _ _ _ _ 0 [] _ = some x at hx
  change checksTrees _ _ _ _ 0 [] _ = some y at hy
  simp only [checksTrees] at hx hy
  obtain rfl := Option.some.inj hx
  obtain rfl := Option.some.inj hy
  exact hz

end Stretch

end OnBytes.Maker
