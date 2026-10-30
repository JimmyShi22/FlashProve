-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/Count.lean: the compiled verifier makes no more checks of openings than it
reads positions; so, by the wire record's own law, at most `nOpen`.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.


"Yes, cut by cut" (`CutsAt`, OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) asks that the checks of all
three chains and of the external strings together are at most `nOpen`. A lawful wire record has: the
positions that the verifier reads, in the prover's oracles and in the external strings, are at most
`nOpen` (`ProtocolQueryLayout.OKG.opens`, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean). Here: each check belongs to a position
that is read, and no two to the same.

Main names:
  `readComp`, `readTrees`, `readB`: the positions whose openings are checked, in the order of the
    checks: in one tree, in the trees of one component, in all rounds.
  `length_checksB`: there are as many checks as such positions.
  `nodup_readB`, `mem_readB`: under the laws of the wire records none stands twice; each is read.
  `length_checksB_le`: so there are at most as many checks as a finite set has members that holds
    all positions that are read.
  `length_checksExtW_le`: the same for the external strings.
  `count_of_forests`: the premise `count`, from the laws of the file's wire record.

Limits: a count alone.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts
import OnBytes.TypedOracleCompiler.Joined.YesByCuts

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## One tree -/

section Comp
variable {r : Round}

/-- the positions at the leaf numbers js that are read, in the order of js -/
def readComp (posAt : ℕ → Option r.Pos) (isRead : r.Pos → Bool) : List ℕ → List r.Pos
  | [] => []
  | j :: js =>
    match posAt j with
    | some p => if isRead p then p :: readComp posAt isRead js else readComp posAt isRead js
    | none => readComp posAt isRead js

theorem length_checksComp (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)),
      checksComp posAt depth emb rt isRead f js = some cs →
      cs.length = (readComp posAt isRead js).length
  | [], cs, h => by
    simp only [checksComp] at h
    cases h
    rfl
  | j0 :: js, cs, h => by
    have ih := length_checksComp posAt depth emb rt isRead f js
    simp only [checksComp] at h
    cases h0 : posAt j0 with
    | none =>
      rw [h0] at h
      simp only [readComp, h0]
      exact ih cs h
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
            simp only [readComp, h0, hr0, if_true, List.length_cons]
            rw [ih cs' hcc]
      · simp only [hr0] at h
        simp only [readComp, h0, hr0]
        exact ih cs h

theorem mem_readComp {posAt : ℕ → Option r.Pos} {isRead : r.Pos → Bool} {p : r.Pos} :
    ∀ {js : List ℕ}, p ∈ readComp posAt isRead js →
      isRead p = true ∧ ∃ j ∈ js, posAt j = some p
  | [], h => by cases h
  | j0 :: js, h => by
    have ih := fun h' => mem_readComp (posAt := posAt) (isRead := isRead) (p := p) (js := js) h'
    have up : (isRead p = true ∧ ∃ j ∈ js, posAt j = some p) →
        isRead p = true ∧ ∃ j ∈ j0 :: js, posAt j = some p :=
      fun ⟨a, j, hj, b⟩ => ⟨a, j, List.mem_cons_of_mem _ hj, b⟩
    cases h0 : posAt j0 with
    | none =>
      simp only [readComp, h0] at h
      exact up (ih h)
    | some p0 =>
      by_cases hr0 : isRead p0 = true
      · simp only [readComp, h0, hr0, if_true] at h
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨hr0, j0, List.mem_cons_self, h0⟩
        · exact up (ih h)
      · simp only [readComp, h0, hr0] at h
        exact up (ih h)

theorem nodup_readComp {posAt : ℕ → Option r.Pos} (isRead : r.Pos → Bool) (plc : r.Pos → ℕ)
    (hp : ∀ j p, posAt j = some p → plc p = j) :
    ∀ {js : List ℕ}, js.Nodup → (readComp posAt isRead js).Nodup
  | [], _ => List.nodup_nil
  | j0 :: js, h => by
    obtain ⟨hn, hjs⟩ := List.nodup_cons.1 h
    have ih := nodup_readComp isRead plc hp hjs
    cases h0 : posAt j0 with
    | none =>
      simp only [readComp, h0]
      exact ih
    | some p0 =>
      by_cases hr0 : isRead p0 = true
      · simp only [readComp, h0, hr0, if_true]
        refine List.nodup_cons.2 ⟨fun hm => ?_, ih⟩
        obtain ⟨-, j, hj, hpj⟩ := mem_readComp hm
        rw [← hp j p0 hpj, hp j0 p0 h0] at hj
        exact hn hj
      · simp only [readComp, h0, hr0]
        exact ih

/-! ## The trees of one component -/

/-- the positions that are read in the trees from number k on that have a depth and a root -/
def readTrees (posAt : ℕ → ℕ → Option r.Pos) (isRead : r.Pos → Bool) :
    ℕ → List ℕ → List (Dig lam) → List r.Pos
  | k, d :: ds, _ :: cs =>
    readComp (posAt k) isRead (List.range (2 ^ d)) ++ readTrees posAt isRead (k + 1) ds cs
  | _, _, _ => []

theorem length_checksTrees (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      (l.flatMap fun z => z.2.2).length = (readTrees posAt isRead k ds rt).length
  | k, d0 :: ds, c0 :: rt, l, h => by
    simp only [checksTrees] at h
    cases h1 : checksComp (posAt k) d0 emb c0 isRead f (List.range (2 ^ d0)) with
    | none => rw [h1] at h; cases h
    | some a =>
      cases h2 : checksTrees posAt emb isRead f (k + 1) ds rt with
      | none => rw [h1, h2] at h; cases h
      | some b =>
        rw [h1, h2] at h
        cases h
        rw [List.flatMap_cons, List.length_append, readTrees, List.length_append,
          length_checksComp _ _ _ _ _ _ _ a h1, length_checksTrees posAt emb isRead f _ _ _ b h2]
  | _, [], _, l, h => by
    simp only [checksTrees] at h
    cases h
    simp [readTrees]
  | _, _ :: _, [], l, h => by
    simp only [checksTrees] at h
    cases h
    simp [readTrees]

theorem mem_readTrees {posAt : ℕ → ℕ → Option r.Pos} {isRead : r.Pos → Bool} {p : r.Pos} :
    ∀ {k : ℕ} {ds : List ℕ} {rt : List (Dig lam)}, p ∈ readTrees posAt isRead k ds rt →
      isRead p = true ∧ ∃ k', k ≤ k' ∧ ∃ j, posAt k' j = some p
  | k, d :: ds, _ :: cs, h => by
    rw [readTrees] at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨a, j, -, b⟩ := mem_readComp h
      exact ⟨a, k, Nat.le_refl k, j, b⟩
    · obtain ⟨a, k', hk, b⟩ := mem_readTrees h
      exact ⟨a, k', Nat.le_of_succ_le hk, b⟩
  | _, [], _, h => by simp [readTrees] at h
  | _, _ :: _, [], h => by simp [readTrees] at h

theorem nodup_readTrees {posAt : ℕ → ℕ → Option r.Pos} (isRead : r.Pos → Bool)
    (tre plc : r.Pos → ℕ) (hp : ∀ k j p, posAt k j = some p → tre p = k ∧ plc p = j) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)), (readTrees posAt isRead k ds rt).Nodup
  | k, d :: ds, _ :: cs => by
    rw [readTrees]
    refine List.Nodup.append
      (nodup_readComp isRead plc (fun j p h => (hp k j p h).2) List.nodup_range)
      (nodup_readTrees isRead tre plc hp (k + 1) ds cs) fun p h1 h2 => ?_
    obtain ⟨-, j, -, b⟩ := mem_readComp h1
    obtain ⟨-, k', hk, j', b'⟩ := mem_readTrees h2
    have e1 := (hp k j p b).1
    have e2 := (hp k' j' p b').1
    omega
  | _, [], _ => by simp [readTrees]
  | _, _ :: _, [] => by simp [readTrees]

end Comp

/-! ## All rounds -/

/-- the positions whose openings are checked, in the order of the checks -/
def readB : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → RootsOfChain lam s → (OPos s → Bool) →
    List (OPos s)
  | [], _, _, _, _ => []
  | r :: s, (_, A), (w, W), (rt, R), isRead =>
    (((readTrees w.posAt0 (fun p => isRead (.inl p)) 0 w.depth0 (rt.1.getD []) ++
      readTrees w.posAtJ (fun p => isRead (.inl p)) 0 w.depthJ (rt.2.getD [])).map
        (Sum.inl : r.Pos → r.Pos ⊕ OPos s)) ++
      (readB s A W R fun p => isRead (.inr p)).map (Sum.inr : OPos s → r.Pos ⊕ OPos s) :
      List (r.Pos ⊕ OPos s))

theorem length_checksB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
      (R : RootsOfChain lam s) (isRead : OPos s → Bool)
      (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
      checksB s A W emb R isRead f = some cs → cs.length = (readB s A W R isRead).length
  | [], _, _, _, _, _, _, cs, h => by
    simp only [checksB] at h
    cases h
    rfl
  | r :: s, (a, A), (w, W), emb, (rt, R), isRead, f, cs, hcs => by
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
          obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 h0
          obtain ⟨lJ, hlJ, rfl⟩ := Option.map_eq_some_iff.1 hJ
          have e0 := length_checksTrees _ _ _ _ _ _ _ l0 hl0
          have eJ := length_checksTrees _ _ _ _ _ _ _ lJ hlJ
          have e2 := length_checksB s A W _ R _ _ c2 h2
          have e3 : (readB (r :: s) (a, A) (w, W) (rt, R) isRead).length =
              (readTrees w.posAt0 (fun p => isRead (.inl p)) 0 w.depth0 (rt.1.getD [])).length +
                (readTrees w.posAtJ (fun p => isRead (.inl p)) 0 w.depthJ (rt.2.getD [])).length +
                (readB s A W R fun p => isRead (.inr p)).length := by
            show (List.map (Sum.inl : r.Pos → r.Pos ⊕ OPos s) (_ ++ _) ++
              List.map (Sum.inr : OPos s → r.Pos ⊕ OPos s) _).length = _
            rw [List.length_append, List.length_map, List.length_map, List.length_append]
          rw [e3, List.length_append, List.length_append]
          omega

theorem mem_readB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (R : RootsOfChain lam s) (isRead : OPos s → Bool)
      (p : OPos s), p ∈ readB s A W R isRead → isRead p = true
  | [], _, _, _, _, p, _ => nomatch p
  | r :: s, (a, A), (w, W), (rt, R), isRead, p, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
      rcases List.mem_append.1 hq with hq | hq
      · exact (mem_readTrees hq).1
      · exact (mem_readTrees hq).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
      exact mem_readB s A W R (fun p => isRead (.inr p)) q hq

theorem nodup_readB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (R : RootsOfChain lam s) (isRead : OPos s → Bool), (readB s A W R isRead).Nodup
  | [], _, _, _, _, _ => List.nodup_nil
  | r :: s, (a, A), (w, W), hW, (rt, R), isRead => by
    refine List.Nodup.append (List.Nodup.map Sum.inl_injective (List.Nodup.append
      (nodup_readTrees _ w.tree w.place (fun k j p h => (hW.1.place_posAt0 k j p h).2) _ _ _)
      (nodup_readTrees _ w.tree w.place (fun k j p h => (hW.1.place_posAtJ k j p h).2) _ _ _)
      fun p h1 h2 => ?_))
      (List.Nodup.map Sum.inr_injective
        (nodup_readB s A W hW.2 R fun p => isRead (.inr p))) fun p h1 h2 => ?_
    · obtain ⟨-, k, -, j, b⟩ := mem_readTrees h1
      obtain ⟨-, k', -, j', b'⟩ := mem_readTrees h2
      have e1 := (hW.1.place_posAt0 k j p b).1
      have e2 := (hW.1.place_posAtJ k' j' p b').1
      rw [e1] at e2
      cases e2
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 h1
      obtain ⟨q', -, e⟩ := List.mem_map.1 h2
      cases e

open Classical in
/-- **No more checks than positions that are read.** -/
theorem length_checksB_le {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A}
    (hW : RoundsQueryLayout.OKG s A W) {emb : (p : OPos s) → OSym s p → Body L} {R : RootsOfChain lam s}
    {isRead : OPos s → Bool} {f : (p : OPos s) → Option (Opening lam (OSym s p))}
    {cs : List (Check lam L)} (h : checksB s A W emb R isRead f = some cs)
    (B : Finset (OPos s)) (hB : ∀ p, isRead p = true → p ∈ B) : cs.length ≤ B.card := by
  rw [length_checksB s A W emb R isRead f cs h,
    ← List.toFinset_card_of_nodup (nodup_readB s A W hW R isRead)]
  exact Finset.card_le_card fun p hp =>
    hB p (mem_readB s A W R isRead p (List.mem_toFinset.1 hp))

/-! ## The external strings -/

theorem length_checksExtW {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L)
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (ℕ × Check lam L)),
      checksExtW we emb cms isRead g ps = some cs → cs.length = (ps.filter isRead).length
  | [], cs, h => by
    simp only [checksExtW] at h
    cases h
    rfl
  | p :: ps, cs, h => by
    have ih := length_checksExtW we emb cms isRead g ps
    simp only [checksExtW] at h
    by_cases hr : isRead p = true
    · simp only [hr, if_true] at h
      cases hg : g p with
      | none => rw [hg] at h; cases h
      | some op =>
        cases hc : checksExtW we emb cms isRead g ps with
        | none => rw [hg, hc] at h; cases h
        | some cs' =>
          rw [hg, hc] at h
          cases h
          rw [List.filter_cons_of_pos hr, List.length_cons, List.length_cons, ih cs' hc]
    · simp only [hr] at h
      rw [List.filter_cons_of_neg hr]
      exact ih cs h

open Classical in
theorem length_checksExtW_le {E : ExtSpec} {we : WireE E} (hwe : we.OK) {emb : E.Sym → Body L}
    {cms : List (Dig lam)} {isRead : E.Pos → Bool} {g : E.Pos → Option (Opening lam E.Sym)}
    {cs : List (ℕ × Check lam L)} (h : checksExtW we emb cms isRead g we.all = some cs)
    (B : Finset E.Pos) (hB : ∀ p, isRead p = true → p ∈ B) : cs.length ≤ B.card := by
  rw [length_checksExtW we emb cms isRead g we.all cs h,
    ← List.toFinset_card_of_nodup (hwe.nodup.filter _)]
  exact Finset.card_le_card fun p hp => hB p (List.mem_filter.1 (List.mem_toFinset.1 hp)).2

/-! ## The premise `count` -/

section File
variable {Y : Type} {E : ExtSpec} {G : Chains} {D : Desc G Y E} {wq : ProtocolQueryLayout lam K D.batch}
  {embS : (p : OPos G.sh) → OSym G.sh p → Body L} {embE : E.Sym → Body L} {cms : List (Dig lam)}
  {x : Y} {π : OneProtocolProof lam D.batch} {a : Out lam G.c₁} {b : Out lam G.c₂} {e : Out lam G.c₃}
  {F₁ F₂ F₃ Fe : List (Forest lam L)}

/-- **The premise `count`**, from the laws of the file's wire record. -/
theorem count_of_forests (hw : wq.OKG)
    (f₁ : forestsB G.c₁ G.A₁ (wire₁ wq) (symb₁ embS) a.2.1 (rd₁ D wq x π a b e) (op₁ D π) =
      some F₁)
    (f₂ : forestsB G.c₂ G.A₂ (wire₂ wq) (symb₂ embS) b.2.1 (rd₂ D wq x π a b e) (op₂ D π) =
      some F₂)
    (f₃ : forestsB G.c₃ G.A₃ (wire₃ wq) (symb₃ embS) e.2.1 (rd₃ D wq x π a b e) (op₃ D π) =
      some F₃)
    (fE : forestExt wq.ext embE cms (readE D wq x (glue a b e).1) π.ext = some Fe) :
    (flatF F₁).length + (flatF F₂).length + (flatF F₃).length + (flatF Fe).length ≤ wq.nOpen := by
  have hall : forestsB G.sh G.ann wq.sh embS (glue a b e).2.1 (rd D wq x π a b e) π.opens =
      some (F₁ ++ (F₂ ++ F₃)) := by
    show forestsB (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh embS
      (RT.app a.2.1 (RT.app b.2.1 e.2.1)) (rd D wq x π a b e) π.opens = _
    rw [forestsB_app, forestsB_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
    exact appO_eq_some.2 ⟨_, _, f₁, appO_eq_some.2 ⟨_, _, f₂, f₃, rfl⟩, rfl⟩
  have hcs := map_flatF_forestsB G.sh G.ann wq.sh embS (glue a b e).2.1 (rd D wq x π a b e) π.opens
  rw [hall] at hcs
  have h1 := length_checksB_le hw.sh hcs.symm
    (D.reads x (glue a b e).1 (effPlains G.sh G.ann (glue a b e).2.1 π.plains))
    fun p hp => by
      letI := wq.decO
      exact of_decide_eq_true hp
  obtain ⟨cs, hcE, rfl⟩ := Option.map_eq_some_iff.1 fE
  have h2 := length_checksExtW_le hw.ext hcE (D.extReads x (glue a b e).1)
    fun p hp => by
      letI := wq.ext.dec
      exact of_decide_eq_true hp
  have h3 := hw.opens x (glue a b e).1 (effPlains G.sh G.ann (glue a b e).2.1 π.plains)
  rw [flatF_append, flatF_append, List.length_append, List.length_append] at h1
  rw [flatF_split, List.length_map]
  show (flatF F₁).length + (flatF F₂).length + (flatF F₃).length + cs.length ≤ wq.nOpen
  have h3' : (D.reads x (glue a b e).1 (effPlains G.sh G.ann (glue a b e).2.1 π.plains)).card +
      (D.extReads x (glue a b e).1).card ≤ wq.nOpen := h3
  omega

end File

end TypedOracleCompiler.Joined
