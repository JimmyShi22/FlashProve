-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/Openings.lean: what the compiled verifier asks of the openings of a proof
string before it hashes, as conditions position by position.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.

"Yes, cut by cut" (`CutsAt`, OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) asks of the openings at each
chain's rounds, and of those of the external strings, three things that want no oracle: the strict
format (`strictSB`, `strictExt`), that no opening that is read is missing (`forestsB`, `forestExt`
give a list), and that each check is well formed and within the depth (`fits`). These are defined
by walks over rounds, trees and leaf numbers (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean). Here each is
had from a condition on each position p, in terms of the tree in which p stands and its leaf number
(`treeOf`, `placeOf`, OnBytes/TypedOracleCompiler/Joined/Clauses.lean). All is general in the rounds: it serves
each of the three chains.

Main names:
  `strictSB_of`: an opening stands only at a position that is read and whose tree has a root, with
    a salt of sMT bits.
  `exists_forestsB`: each position that is read has an opening.
  `forall_checksB`, `forall_flatF`: each check is the check of a position that is read, has an
    opening, and stands in a tree with a root: so what holds of these checks holds of all. (The
    converse of `mem_checksB`, Clauses.lean.)
  `treeOf_bounds`: a position's leaf number is one of its tree, whose depth the wire record bounds.
  `fit_of`: each opening that is read has a path as long as its tree is deep.
  `strictExt_of`, `exists_forestExt`, `fitExt_of`: the same three for the external strings.

Limits: one direction only. Nothing on hashing.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts
import OnBytes.TypedOracleCompiler.Joined.Clauses

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem treeAt_of {ds : List ℕ} {rt : List (Dig lam)} {k d : ℕ} {c : Dig lam}
    (hd : ds[k]? = some d) (hc : rt[k]? = some c) : treeAt ds rt k = some (d, c) := by
  unfold treeAt
  rw [hd, hc]

theorem isSome_root_of_treeAt {ds : List ℕ} {rt : List (Dig lam)} {k : ℕ}
    (h : (treeAt ds rt k).isSome = true) : (rt[k]?).isSome = true := by
  obtain ⟨⟨d, c⟩, hz⟩ := Option.isSome_iff_exists.1 h
  rw [(treeAt_eq_some hz).2]
  rfl

/-! ## The strict format -/

section Strict
variable (sMT : ℕ)

theorem strictComp_of {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ j p op, posAt j = some p → f p = some op →
      hasRoot = true ∧ isRead p = true ∧ op.salt.length = sMT) :
    strictComp sMT posAt depth hasRoot isRead f = true := by
  refine List.all_eq_true.2 fun j _ => ?_
  cases hp : posAt j with
  | none => rfl
  | some p =>
    cases hf : f p with
    | none => simp only [hf]
    | some op =>
      obtain ⟨h1, h2, h3⟩ := h j p op hp hf
      simp only [hf, h1, h2, h3, decide_true, Bool.and_self]

theorem strictTrees_of {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ k j p op, posAt k j = some p → f p = some op →
      (rt[k]?).isSome = true ∧ isRead p = true ∧ op.salt.length = sMT) :
    strictTrees sMT posAt depth rt isRead f = true :=
  List.all_eq_true.2 fun k _ => strictComp_of sMT (posAt k) _ _ isRead f fun j p op => h k j p op

/-- **The strict format of the openings at the rounds s**: an opening stands only at a position that
is read and whose tree has a root, and its salt has sMT bits. -/
theorem strictSB_of :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (R : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))),
        (∀ p op, f p = some op → isRead p = true ∧ op.salt.length = sMT ∧
          (treeOf s A W R p).isSome = true) →
        strictSB sMT s A W R isRead f = true
  | [], _, _, _, _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), hW, (rt, R), isRead, f, h => by
    have h0 : strictTrees sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) = true :=
      strictTrees_of sMT _ _ _ _ _ fun k j p op hp hf => by
        obtain ⟨ho, rfl, -⟩ := hW.1.place_posAt0 k j p hp
        obtain ⟨h1, h2, h3⟩ := h (.inl p) op hf
        have h3' : (treeAt w.depth0 (rt.1.getD []) (w.tree p)).isSome = true := by
          simpa only [treeOf, ho, Bool.false_eq_true, if_false] using h3
        exact ⟨isSome_root_of_treeAt h3', h1, h2⟩
    have hJ : strictTrees sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) = true :=
      strictTrees_of sMT _ _ _ _ _ fun k j p op hp hf => by
        obtain ⟨ho, rfl, -⟩ := hW.1.place_posAtJ k j p hp
        obtain ⟨h1, h2, h3⟩ := h (.inl p) op hf
        have h3' : (treeAt w.depthJ (rt.2.getD []) (w.tree p)).isSome = true := by
          simpa only [treeOf, ho, if_true] using h3
        exact ⟨isSome_root_of_treeAt h3', h1, h2⟩
    have ih := strictSB_of s A W hW.2 R (fun p => isRead (.inr p)) (fun p => f (.inr p))
      fun p op hf => h (.inr p) op hf
    show (strictTrees sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) &&
      strictTrees sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) &&
      strictSB sMT s A W R (fun p => isRead (.inr p)) (fun p => f (.inr p))) = true
    rw [h0, hJ, ih]
    rfl

end Strict

/-! ## No opening that is read is missing -/

section Exists
variable {r : Round} (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
  (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))

theorem isSome_checksComp (posAt : ℕ → Option r.Pos) (depth : ℕ) (rt : Dig lam) :
    ∀ js : List ℕ, (∀ j ∈ js, ∀ p, posAt j = some p → isRead p = true → (f p).isSome = true) →
      (checksComp posAt depth emb rt isRead f js).isSome = true
  | [], _ => rfl
  | j0 :: js, H => by
    have ih := isSome_checksComp posAt depth rt js fun j hj => H j (List.mem_cons_of_mem _ hj)
    obtain ⟨cs', hcs'⟩ := Option.isSome_iff_exists.1 ih
    cases h0 : posAt j0 with
    | none =>
      simp only [checksComp, h0]
      exact ih
    | some p0 =>
      by_cases hr0 : isRead p0 = true
      · obtain ⟨op, hop⟩ := Option.isSome_iff_exists.1 (H j0 List.mem_cons_self p0 h0 hr0)
        simp only [checksComp, h0, hr0, if_true, hop, hcs']
        rfl
      · simp only [checksComp, h0, hr0]
        exact ih

theorem isSome_checksTrees (posAt : ℕ → ℕ → Option r.Pos)
    (H : ∀ k j p, posAt k j = some p → isRead p = true → (f p).isSome = true) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)),
      (checksTrees posAt emb isRead f k ds rt).isSome = true
  | k, d :: ds, c :: cs => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (isSome_checksComp emb isRead f (posAt k) d c
      (List.range (2 ^ d)) fun j _ p hp hr => H k j p hp hr)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (isSome_checksTrees posAt H (k + 1) ds cs)
    simp only [checksTrees, ha, hb]
    rfl
  | _, [], _ => by simp [checksTrees]
  | _, _ :: _, [] => by simp [checksTrees]

end Exists

/-- **No opening that is read is missing at the rounds s**: the forests are there. -/
theorem exists_forestsB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
      (R : RootsOfChain lam s) (isRead : OPos s → Bool)
      (f : (p : OPos s) → Option (Opening lam (OSym s p))),
      (∀ p, isRead p = true → (f p).isSome = true) →
      ∃ Fs, forestsB s A W emb R isRead f = some Fs
  | [], _, _, _, _, _, _, _ => ⟨[], rfl⟩
  | r :: s, (a, A), (w, W), emb, (rt, R), isRead, f, H => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (isSome_checksTrees (fun p => emb (.inl p))
      (fun p => isRead (.inl p)) (fun p => f (.inl p)) w.posAt0 (fun _ _ p _ hr => H (.inl p) hr)
      0 w.depth0 (rt.1.getD []))
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (isSome_checksTrees (fun p => emb (.inl p))
      (fun p => isRead (.inl p)) (fun p => f (.inl p)) w.posAtJ (fun _ _ p _ hr => H (.inl p) hr)
      0 w.depthJ (rt.2.getD []))
    obtain ⟨z, hz⟩ := exists_forestsB s A W (fun p => emb (.inr p)) R (fun p => isRead (.inr p))
      (fun p => f (.inr p)) fun p hr => H (.inr p) hr
    exact ⟨forestsT w.pr0 x ++ (forestsT w.prJ y ++ z), by simp only [forestsB, hx, hy, hz]⟩

/-! ## Each check is the check of a position that is read -/

section Forall
variable {P : Check lam L → Prop}

theorem forall_checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)),
      checksComp posAt depth emb rt isRead f js = some cs →
      (∀ j ∈ js, ∀ p op, posAt j = some p → isRead p = true → f p = some op →
        P ⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩) →
      ∀ c ∈ cs, P c
  | [], cs, h, _, c, hc => by
    simp only [checksComp] at h
    cases h
    cases hc
  | j0 :: js, cs, h, H, c, hc => by
    have ih := fun cs' h' => forall_checksComp posAt depth emb rt isRead f js cs' h'
      fun j hj => H j (List.mem_cons_of_mem _ hj)
    simp only [checksComp] at h
    cases h0 : posAt j0 with
    | none =>
      rw [h0] at h
      exact ih cs h c hc
    | some p0 =>
      rw [h0] at h
      by_cases hr0 : isRead p0 = true
      · simp only [hr0, if_true] at h
        cases hf : f p0 with
        | none => rw [hf] at h; cases h
        | some op =>
          cases hcc : checksComp posAt depth emb rt isRead f js with
          | none => rw [hf, hcc] at h; cases h
          | some cs' =>
            rw [hf, hcc] at h
            cases h
            rcases List.mem_cons.1 hc with rfl | hc'
            · exact H j0 List.mem_cons_self p0 op h0 hr0 hf
            · exact ih cs' hcc c hc'
      · simp only [hr0] at h
        exact ih cs h c hc

theorem forall_checksTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      (∀ i d c, ds[i]? = some d → rt[i]? = some c → ∀ j, j < 2 ^ d → ∀ p op,
        posAt (k + i) j = some p → isRead p = true → f p = some op →
        P ⟨⟨emb p op.sym, op.salt⟩, j, op.path, c, d⟩) →
      ∀ z ∈ l, ∀ x ∈ z.2.2, P x
  | k, d0 :: ds, c0 :: rt, l, h, H, z, hz, x, hx => by
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
        · exact forall_checksComp (posAt k) d0 emb c0 isRead f _ a h1
            (fun j hj p op hp hr hf =>
              H 0 d0 c0 rfl rfl j (List.mem_range.1 hj) p op (by rwa [Nat.add_zero]) hr hf) x hx
        · exact forall_checksTrees posAt emb isRead f (k + 1) ds rt b h2
            (fun i d c hd hc j hj p op hp hr hf =>
              H (i + 1) d c (by simpa using hd) (by simpa using hc) j hj p op
                (by rwa [show k + (i + 1) = k + 1 + i by omega]) hr hf) z hz' x hx
  | _, [], _, l, h, _, z, hz, _, _ => by
    simp only [checksTrees] at h
    cases h
    cases hz
  | _, _ :: _, [], l, h, _, z, hz, _, _ => by
    simp only [checksTrees] at h
    cases h
    cases hz

/-- **Each check at the rounds s is the check of a position that is read, has an opening, and stands
in a tree with a root**: what holds of these checks holds of all. -/
theorem forall_checksB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (emb : (p : OPos s) → OSym s p → Body L) (R : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
        checksB s A W emb R isRead f = some cs →
        (∀ p op d c, isRead p = true → f p = some op → treeOf s A W R p = some (d, c) →
          P ⟨⟨emb p op.sym, op.salt⟩, placeOf s A W p, op.path, c, d⟩) →
        ∀ x ∈ cs, P x
  | [], _, _, _, _, _, _, _, cs, h, _, x, hx => by
    simp only [checksB] at h
    cases h
    cases hx
  | r :: s, (a, A), (w, W), hW, emb, (rt, R), isRead, f, cs, hcs, H, x, hx => by
    simp only [checksB] at hcs
    cases h0 : checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD [])
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
    | none => rw [h0] at hcs; cases hcs
    | some c0 =>
      cases hJ : checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
      | none => rw [h0, hJ] at hcs; cases hcs
      | some cJ =>
        cases h2 : checksB s A W (fun p => emb (.inr p)) R
            (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
        | none => rw [h0, hJ, h2] at hcs; cases hcs
        | some c2 =>
          rw [h0, hJ, h2] at hcs
          cases hcs
          rcases List.mem_append.1 hx with hx | hx
          · rcases List.mem_append.1 hx with hx | hx
            · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h0
              obtain ⟨z, hz, hxz⟩ := List.mem_flatMap.1 hx
              refine forall_checksTrees w.posAt0 _ _ _ 0 w.depth0 (rt.1.getD []) l hl
                (fun i d c hd hc j _ p op hp hr hf => ?_) z hz x hxz
              rw [Nat.zero_add] at hp
              obtain ⟨ho, rfl, rfl⟩ := hW.1.place_posAt0 i j p hp
              exact H (.inl p) op d c hr hf
                (by simpa only [treeOf, ho, Bool.false_eq_true, if_false] using treeAt_of hd hc)
            · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hJ
              obtain ⟨z, hz, hxz⟩ := List.mem_flatMap.1 hx
              refine forall_checksTrees w.posAtJ _ _ _ 0 w.depthJ (rt.2.getD []) l hl
                (fun i d c hd hc j _ p op hp hr hf => ?_) z hz x hxz
              rw [Nat.zero_add] at hp
              obtain ⟨ho, rfl, rfl⟩ := hW.1.place_posAtJ i j p hp
              exact H (.inl p) op d c hr hf
                (by simpa only [treeOf, ho, if_true] using treeAt_of hd hc)
          · exact forall_checksB s A W hW.2 (fun p => emb (.inr p)) R (fun p => isRead (.inr p))
              (fun p => f (.inr p)) c2 h2 (fun p op d c hr hf ht => H (.inr p) op d c hr hf ht) x hx

/-- the same for all checks of the forests -/
theorem forall_flatF {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} (hW : RoundsQueryLayout.OKG s A W)
    {emb : (p : OPos s) → OSym s p → Body L} {R : RootsOfChain lam s} {isRead : OPos s → Bool}
    {f : (p : OPos s) → Option (Opening lam (OSym s p))} {Fs : List (Forest lam L)}
    (hF : forestsB s A W emb R isRead f = some Fs)
    (H : ∀ p op d c, isRead p = true → f p = some op → treeOf s A W R p = some (d, c) →
      P ⟨⟨emb p op.sym, op.salt⟩, placeOf s A W p, op.path, c, d⟩) :
    ∀ x ∈ flatF Fs, P x := by
  have h := map_flatF_forestsB s A W emb R isRead f
  rw [hF] at h
  exact forall_checksB s A W hW emb R isRead f (flatF Fs) h.symm H

end Forall

/-! ## Each check is well formed and within the depth -/

/-- A position's leaf number is one of its tree, and the wire record's bound holds of the depth. -/
theorem treeOf_bounds {m : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      RoundsQueryLayout.DepthLe m s A W → ∀ (R : RootsOfChain lam s) (p : OPos s) (d : ℕ) (c : Dig lam),
        treeOf s A W R p = some (d, c) → placeOf s A W p < 2 ^ d ∧ d ≤ m
  | [], _, _, _, _, _, p, _, _, _ => nomatch p
  | r :: s, (a, A), (w, W), hW, hD, (rt, R), .inl q, d, c, ht => by
    by_cases ho : a.own q = true
    · have ht' : treeAt w.depthJ (rt.2.getD []) (w.tree q) = some (d, c) := by
        simpa only [treeOf, ho, if_true] using ht
      obtain ⟨d', hd', hlt⟩ := hW.1.place_ltJ q ho
      obtain rfl : d' = d := Option.some.inj (hd'.symm.trans (treeAt_eq_some ht').1)
      exact ⟨hlt, hD.1.2 d' (List.mem_of_getElem? hd')⟩
    · have ho' : a.own q = false := by simpa using ho
      have ht' : treeAt w.depth0 (rt.1.getD []) (w.tree q) = some (d, c) := by
        simpa only [treeOf, ho', Bool.false_eq_true, if_false] using ht
      obtain ⟨d', hd', hlt⟩ := hW.1.place_lt0 q ho'
      obtain rfl : d' = d := Option.some.inj (hd'.symm.trans (treeAt_eq_some ht').1)
      exact ⟨hlt, hD.1.1 d' (List.mem_of_getElem? hd')⟩
  | r :: s, (a, A), (w, W), hW, hD, (rt, R), .inr q, d, c, ht =>
    treeOf_bounds s A W hW.2 hD.2 R q d c ht

/-- **Each check at the rounds s is well formed and within the depth m**: each opening that is read
has a path as long as its tree is deep. -/
theorem fit_of {m : ℕ} {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} (hW : RoundsQueryLayout.OKG s A W)
    (hD : RoundsQueryLayout.DepthLe m s A W) {emb : (p : OPos s) → OSym s p → Body L} {R : RootsOfChain lam s}
    {isRead : OPos s → Bool} {f : (p : OPos s) → Option (Opening lam (OSym s p))}
    {Fs : List (Forest lam L)} (hF : forestsB s A W emb R isRead f = some Fs)
    (hp : ∀ p op d c, isRead p = true → f p = some op → treeOf s A W R p = some (d, c) →
      op.path.length = d) :
    (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ m)) = true :=
  List.all_eq_true.2 <| forall_flatF (P := fun c => (c.wellFormed && decide (c.depth ≤ m)) = true)
    hW hF fun p op d c hr hf ht => by
      obtain ⟨h1, h2⟩ := treeOf_bounds s A W hW hD R p d c ht
      show ((decide (op.path.length = d) && decide (placeOf s A W p < 2 ^ d)) &&
        decide (d ≤ m)) = true
      rw [decide_eq_true (hp p op d c hr hf ht), decide_eq_true h1, decide_eq_true h2]
      rfl

/-! ## The external strings -/

section Ext
variable {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
  (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym))

/-- the strict format of the openings of the external strings -/
theorem strictExt_of (sMT : ℕ)
    (h : ∀ p ∈ we.all, ∀ op, g p = some op → isRead p = true ∧ op.salt.length = sMT) :
    strictExt sMT we isRead g = true := by
  refine List.all_eq_true.2 fun p hp => ?_
  cases hg : g p with
  | none => rfl
  | some op =>
    obtain ⟨h1, h2⟩ := h p hp op hg
    simp only [h1, h2, decide_true, Bool.and_self]

theorem checksExtW_spec {P : Check lam L → Prop} :
    ∀ ps : List E.Pos, (∀ p ∈ ps, isRead p = true → (g p).isSome = true) →
      ∃ cs, checksExtW we emb cms isRead g ps = some cs ∧
        ((∀ p ∈ ps, ∀ op, isRead p = true → g p = some op →
          P ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path, cms.getD (we.which p) default,
            we.depth⟩) → ∀ x ∈ cs, P x.2)
  | [], _ => ⟨[], rfl, fun _ x hx => by cases hx⟩
  | p :: ps, H => by
    obtain ⟨cs, hcs, hP⟩ := checksExtW_spec ps fun q hq => H q (List.mem_cons_of_mem _ hq)
    by_cases hr : isRead p = true
    · obtain ⟨op, hop⟩ := Option.isSome_iff_exists.1 (H p List.mem_cons_self hr)
      refine ⟨(we.which p, ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
        cms.getD (we.which p) default, we.depth⟩) :: cs,
        by simp only [checksExtW, hr, if_true, hop, hcs], fun h x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h p List.mem_cons_self op hr hop
      · exact hP (fun q hq => h q (List.mem_cons_of_mem _ hq)) x hx
    · exact ⟨cs, by simp only [checksExtW, hr]; exact hcs,
        fun h x hx => hP (fun q hq => h q (List.mem_cons_of_mem _ hq)) x hx⟩

/-- no opening of the external strings that is read is missing -/
theorem exists_forestExt (H : ∀ p ∈ we.all, isRead p = true → (g p).isSome = true) :
    ∃ Fe, forestExt we emb cms isRead g = some Fe := by
  obtain ⟨cs, hcs, -⟩ := checksExtW_spec (P := fun _ => True) we emb cms isRead g we.all H
  exact ⟨_, by unfold forestExt; rw [hcs]; rfl⟩

/-- each check of the external strings is well formed and within the depth m -/
theorem fitExt_of {m : ℕ} {Fe : List (Forest lam L)}
    (hF : forestExt we emb cms isRead g = some Fe) (hm : we.depth ≤ m)
    (hl : ∀ p, we.leaf p < 2 ^ we.depth)
    (H : ∀ p ∈ we.all, isRead p = true → (g p).isSome = true)
    (hp : ∀ p ∈ we.all, ∀ op, isRead p = true → g p = some op → op.path.length = we.depth) :
    (flatF Fe).all (fun c => c.wellFormed && decide (c.depth ≤ m)) = true := by
  obtain ⟨cs, hcs, hP⟩ := checksExtW_spec
    (P := fun c => (c.wellFormed && decide (c.depth ≤ m)) = true) we emb cms isRead g we.all H
  unfold forestExt at hF
  rw [hcs] at hF
  obtain rfl : Forest.split we.pr ⟨we.depth, fun t => cms.getD t default, cs⟩ = Fe :=
    Option.some.inj hF
  rw [flatF_split]
  refine List.all_eq_true.2 fun c hc => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  refine hP (fun p hpm op hr hg => ?_) x hx
  show ((decide (op.path.length = we.depth) && decide (we.leaf p < 2 ^ we.depth)) &&
    decide (we.depth ≤ m)) = true
  rw [decide_eq_true (hp p hpm op hr hg), decide_eq_true (hl p), decide_eq_true hm]
  rfl

end Ext

end TypedOracleCompiler.Joined
