-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/Same.lean: WHEN TWO RUNS OF THE PROVER's CHAIN HAVE KEPT THE SAME, AS FAR AS A PROOF
STRING SHOWS IT. Relations on strategies, on kept trees and on what the chain keeps (Kept,
OnBytes/Prover/Defs.lean), and what follows from them for the fields of the proof string and for the
leaves that are written into the table. No oracle, no probability.

General definitions and lemmas. This file states no goal of the release. It serves
OnBytes/Dry/Side.lean and OnBytes/Dry/View.lean.

rd is a letter throughout: which positions count as read.

Main names.
  leafAt       the input of leaf j of tree number k of a component, as treesO makes it.
  TreesAt      two lists of kept trees, from tree number k on: the same levels of digests; the
               leaves' inputs are two given families.
  TreesSame    the same levels; the same salts at all leaves; the same inputs at the leaves at which
               a position stands that is read.
  KeptSame     round by round: the same plain part as it was hashed; the same symbols at the
               positions that are read; TreesSame for both components.
  AgreeAt      two strategies along the verifier messages ρ: the same plain parts, the same symbols
               at the positions that are read. agreeAt_of_run: from the two runs' transcripts.
  rdOf         "the position lies in the finite set S", as a test.
  TreesAt.roots, TreesAt.same; TreesSame.roots, .opening, .laid; KeptSame.roots, .plains, .opens,
  .laid        what follows: the same roots, plain parts, openings, and leaves to be written (laidK,
               Johnson/WholeKey/Sim.lean).

Limits. Nothing here says that two runs keep the same.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.SpecView

set_option autoImplicit false

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Trees -/

/-- The input of leaf j of tree number k of one component of one round, as treesO makes it. -/
def leafAt {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (k j : ℕ) : LeafIn L :=
  ⟨match posAt k j with
    | some p => emb p (r.rd o p)
    | none => pad, sl k j⟩

/-- Two lists of kept trees, from tree number k on: the same levels; the leaves' inputs are the two
given families. -/
def TreesAt (inp inp' : ℕ → ℕ → LeafIn L) :
    ℕ → List (TreeK lam L) → List (TreeK lam L) → Prop
  | _, [], [] => True
  | k, T :: Ts, T' :: Ts' =>
      (T.lv = T'.lv ∧ T.inp = inp k ∧ T'.inp = inp' k) ∧ TreesAt inp inp' (k + 1) Ts Ts'
  | _, _, _ => False

/-- Two lists of kept trees, from tree number k on: the same levels; the same salts; the same inputs
at the leaves at which a position stands that is read. -/
def TreesSame {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool) :
    ℕ → List (TreeK lam L) → List (TreeK lam L) → Prop
  | _, [], [] => True
  | k, T :: Ts, T' :: Ts' =>
      (T.lv = T'.lv ∧ (∀ j, (T.inp j).salt = (T'.inp j).salt) ∧
        ∀ j p, posAt k j = some p → rd p = true → T.inp j = T'.inp j) ∧
      TreesSame posAt rd (k + 1) Ts Ts'
  | _, _, _ => False

theorem TreesAt.roots {inp inp' : ℕ → ℕ → LeafIn L} :
    ∀ (k : ℕ) (Ts Ts' : List (TreeK lam L)), TreesAt inp inp' k Ts Ts' →
      Ts.map TreeK.root = Ts'.map TreeK.root
  | _, [], [], _ => rfl
  | k, T :: Ts, T' :: Ts', h => by
    have h' : (T.lv = T'.lv ∧ T.inp = inp k ∧ T'.inp = inp' k) ∧
      TreesAt inp inp' (k + 1) Ts Ts' := h
    show T.root :: Ts.map TreeK.root = T'.root :: Ts'.map TreeK.root
    rw [TreesAt.roots (k + 1) Ts Ts' h'.2]
    unfold TreeK.root
    rw [h'.1.1]
  | _, [], _ :: _, h => False.elim h
  | _, _ :: _, [], h => False.elim h

/-- One family of salts, and oracles with the same symbols at the positions that are read. -/
theorem TreesAt.same {r : Round} {pad pad' : Body L} {sl : ℕ → ℕ → Bits}
    {posAt : ℕ → ℕ → Option r.Pos} {emb : (p : r.Pos) → r.Sym p → Body L} {o o' : r.Orc}
    (rd : r.Pos → Bool) (hs : ∀ p, rd p = true → r.rd o p = r.rd o' p) :
    ∀ (k : ℕ) (Ts Ts' : List (TreeK lam L)),
      TreesAt (leafAt pad sl posAt emb o) (leafAt pad' sl posAt emb o') k Ts Ts' →
      TreesSame posAt rd k Ts Ts'
  | _, [], [], _ => trivial
  | k, T :: Ts, T' :: Ts', h => by
    have h' : (T.lv = T'.lv ∧ T.inp = leafAt pad sl posAt emb o k ∧
        T'.inp = leafAt pad' sl posAt emb o' k) ∧
      TreesAt (leafAt pad sl posAt emb o) (leafAt pad' sl posAt emb o') (k + 1) Ts Ts' := h
    refine ⟨⟨h'.1.1, fun j => ?_, fun j p hp hr => ?_⟩, TreesAt.same rd hs (k + 1) Ts Ts' h'.2⟩
    · rw [h'.1.2.1, h'.1.2.2]
      rfl
    · rw [h'.1.2.1, h'.1.2.2]
      simp only [leafAt, hp, hs p hr]
  | _, [], _ :: _, h => False.elim h
  | _, _ :: _, [], h => False.elim h

section
variable {r : Round} {posAt : ℕ → ℕ → Option r.Pos} {rd : r.Pos → Bool}

theorem TreesSame.roots : ∀ (k : ℕ) (Ts Ts' : List (TreeK lam L)), TreesSame posAt rd k Ts Ts' →
    Ts.map TreeK.root = Ts'.map TreeK.root
  | _, [], [], _ => rfl
  | k, T :: Ts, T' :: Ts', h => by
    obtain ⟨⟨h1, -, -⟩, h2⟩ := h
    show T.root :: Ts.map TreeK.root = T'.root :: Ts'.map TreeK.root
    rw [TreesSame.roots (k + 1) Ts Ts' h2]
    unfold TreeK.root
    rw [h1]
  | _, [], _ :: _, h => False.elim h
  | _, _ :: _, [], h => False.elim h

/-- the opening of leaf j of tree number n of the list, which holds the symbol a -/
theorem TreesSame.opening {τ : Type} : ∀ (k : ℕ) (Ts Ts' : List (TreeK lam L)),
    TreesSame posAt rd k Ts Ts' → ∀ (n j : ℕ) (a : τ),
      (Ts[n]?).map (fun T => T.opening j a) = (Ts'[n]?).map fun T => T.opening j a
  | _, [], [], _, _, _, _ => rfl
  | k, T :: Ts, T' :: Ts', h, 0, j, a => by
    obtain ⟨⟨h1, h2, -⟩, -⟩ := h
    rw [List.getElem?_cons_zero, List.getElem?_cons_zero]
    show some (T.opening j a) = some (T'.opening j a)
    unfold TreeK.opening
    rw [h1, h2 j]
  | k, T :: Ts, T' :: Ts', h, n + 1, j, a => by
    obtain ⟨-, h3⟩ := h
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact TreesSame.opening (k + 1) Ts Ts' h3 n j a
  | _, [], _ :: _, h, _, _, _ => False.elim h
  | _, _ :: _, [], h, _, _, _ => False.elim h

/-- the leaves that are written into the table -/
theorem TreesSame.laid : ∀ (k : ℕ) (Ts Ts' : List (TreeK lam L)), TreesSame posAt rd k Ts Ts' →
    laidTrees (K := K) posAt rd k Ts = laidTrees (K := K) posAt rd k Ts'
  | _, [], [], _ => rfl
  | k, T :: Ts, T' :: Ts', h => by
    obtain ⟨⟨h1, -, h3⟩, h4⟩ := h
    show laidTree (K := K) (posAt k) rd T ++ laidTrees (K := K) posAt rd (k + 1) Ts =
      laidTree (K := K) (posAt k) rd T' ++ laidTrees (K := K) posAt rd (k + 1) Ts'
    rw [TreesSame.laid (k + 1) Ts Ts' h4]
    refine congrArg (fun u => u ++ laidTrees (K := K) posAt rd (k + 1) Ts') ?_
    unfold laidTree
    rw [h1]
    refine List.map_congr_left fun j hj => ?_
    have hj' := (List.mem_filter.1 hj).2
    cases hp : posAt k j with
    | none => simp [hp] at hj'
    | some p =>
      simp only [hp] at hj'
      rw [h3 j p hp hj']
  | _, [], _ :: _, h => False.elim h
  | _, _ :: _, [], h => False.elim h

end

/-! ## What the chain keeps -/

/-- Round by round: the same plain part as it was hashed; the same symbols at the positions that are
read; the trees of both components the same as far as it shows. -/
def KeptSame : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (OPos s → Bool) → Kept lam L s →
    Kept lam L s → Prop
  | [], _, _, _, _, _ => True
  | r :: s, (_, A), (w, W), rd, (kp, ks), (kp', ks') =>
      kp.1.2 = kp'.1.2 ∧ (∀ p, rd (.inl p) = true → r.rd kp.1.1 p = r.rd kp'.1.1 p) ∧
      TreesSame w.posAt0 (fun p => rd (.inl p)) 0 kp.2.1 kp'.2.1 ∧
      TreesSame w.posAtJ (fun p => rd (.inl p)) 0 kp.2.2 kp'.2.2 ∧
      KeptSame s A W (fun p => rd (.inr p)) ks ks'

theorem KeptSame.roots : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rd : OPos s → Bool)
    (ks ks' : Kept lam L s), KeptSame s A W rd ks ks' → rootsK s ks = rootsK s ks'
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (_, W), _, (kp, ks), (kp', ks'), h => by
    obtain ⟨-, -, h0, hJ, hs⟩ := h
    show kp.2.2.map TreeK.root ++ (kp.2.1.map TreeK.root ++ rootsK s ks) =
      kp'.2.2.map TreeK.root ++ (kp'.2.1.map TreeK.root ++ rootsK s ks')
    rw [TreesSame.roots _ _ _ h0, TreesSame.roots _ _ _ hJ, KeptSame.roots s A W _ ks ks' hs]

theorem KeptSame.plains : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rd : OPos s → Bool)
    (ks ks' : Kept lam L s), KeptSame s A W rd ks ks' → ∀ ρ : Rho s,
      (trK s ks ρ).plains = (trK s ks' ρ).plains
  | [], _, _, _, _, _, _, _ => rfl
  | r :: s, (_, A), (_, W), _, (kp, ks), (kp', ks'), h, (c, ρ) => by
    obtain ⟨h1, -, -, -, hs⟩ := h
    show ((kp.1.2, (trK s ks ρ).plains) : r.Plain × Plains s) = (kp'.1.2, (trK s ks' ρ).plains)
    rw [h1, KeptSame.plains s A W _ ks ks' hs ρ]

theorem KeptSame.opens : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rd : OPos s → Bool)
    (ks ks' : Kept lam L s), KeptSame s A W rd ks ks' → ∀ p : OPos s,
      OnBytes.Prover.opensK s A W ks rd p = OnBytes.Prover.opensK s A W ks' rd p
  | [], _, _, _, _, _, _, p => nomatch p
  | r :: s, (a, A), (w, W), rd, (kp, ks), (kp', ks'), h, .inl p => by
    obtain ⟨-, h2, h0, hJ, -⟩ := h
    show (if rd (.inl p) then
        ((if a.own p then kp.2.2 else kp.2.1)[w.tree p]?).map fun T =>
          T.opening (w.place p) (r.rd kp.1.1 p)
      else none) =
      if rd (.inl p) then
        ((if a.own p then kp'.2.2 else kp'.2.1)[w.tree p]?).map fun T =>
          T.opening (w.place p) (r.rd kp'.1.1 p)
      else none
    by_cases hr : rd (.inl p) = true
    · rw [if_pos hr, if_pos hr, h2 p hr]
      by_cases ho : a.own p = true
      · rw [if_pos ho, if_pos ho]
        exact TreesSame.opening 0 _ _ hJ _ _ _
      · rw [if_neg ho, if_neg ho]
        exact TreesSame.opening 0 _ _ h0 _ _ _
    · rw [if_neg hr, if_neg hr]
  | _ :: s, (_, A), (_, W), rd, (_, ks), (_, ks'), h, .inr q =>
    KeptSame.opens s A W (fun p => rd (.inr p)) ks ks' h.2.2.2.2 q

theorem KeptSame.laid : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rd : OPos s → Bool)
    (ks ks' : Kept lam L s), KeptSame s A W rd ks ks' → laidK s A W ks rd = laidK s A W ks' rd
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), rd, (kp, ks), (kp', ks'), h => by
    obtain ⟨-, -, h0, hJ, hs⟩ := h
    show laidTrees w.posAtJ (fun p => rd (.inl p)) 0 kp.2.2 ++
        (laidTrees w.posAt0 (fun p => rd (.inl p)) 0 kp.2.1 ++
          laidK s A W ks fun p => rd (.inr p)) =
      laidTrees w.posAtJ (fun p => rd (.inl p)) 0 kp'.2.2 ++
        (laidTrees w.posAt0 (fun p => rd (.inl p)) 0 kp'.2.1 ++
          laidK s A W ks' fun p => rd (.inr p))
    rw [TreesSame.laid _ _ _ h0, TreesSame.laid _ _ _ hJ, KeptSame.laid s A W _ ks ks' hs]

/-! ## Strategies -/

/-- Two strategies along the verifier messages ρ: the same plain parts, and the same symbols at the
positions that are read. -/
def AgreeAt : (s : Shape) → (OPos s → Bool) → Rho s → Strat s Unit → Strat s Unit → Prop
  | [], _, _, _, _ => True
  | r :: s, rd, (c, ρ), (m, k), (m', k') =>
      m.2 = m'.2 ∧ (∀ p, rd (.inl p) = true → r.rd m.1 p = r.rd m'.1 p) ∧
      AgreeAt s (fun p => rd (.inr p)) ρ (k c) (k' c)

theorem agreeAt_of_run : ∀ (s : Shape) (rd : OPos s → Bool) (ρ : Rho s) (σ σ' : Strat s Unit),
    (σ.run ρ).1.plains = (σ'.run ρ).1.plains →
    (∀ p, rd p = true → (σ.run ρ).1.read p = (σ'.run ρ).1.read p) → AgreeAt s rd ρ σ σ'
  | [], _, _, _, _, _, _ => trivial
  | r :: s, rd, (c, ρ), (m, k), (m', k'), hp, hr => by
    have hp' : ((m.2, ((k c).run ρ).1.plains) : r.Plain × Plains s) =
      (m'.2, ((k' c).run ρ).1.plains) := hp
    exact ⟨congrArg Prod.fst hp', fun p h => hr (.inl p) h,
      agreeAt_of_run s _ ρ (k c) (k' c) (congrArg Prod.snd hp') fun p h => hr (.inr p) h⟩

/-- "The position lies in the finite set S", as a test, with the wire's own test of equality. -/
def rdOf {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q)
    (S : Finset (OPos Q.loc.shape)) : OPos Q.loc.shape → Bool := fun p =>
  haveI := wq.decO
  decide (p ∈ S)

end OnBytes.Dry
