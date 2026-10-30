-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Inv.lean: what it means, under fixed oracle functions g, that the compiled prover
(OnBytes/Prover/Defs.lean) has kept its trees rightly; the premises on its coins and on the outer
trees; and the one look-up lemma that the files on openings, walks and the decision all spend.

Main names:
  `TreeK.At g d`   the tree's levels are those of depth d over the digests of its own leaves' inputs
  `CompAt`          one sent component: a tree for each depth, kept rightly; a leaf at which a
                    position stands holds that position's symbol and a salt of sMT bits
  `RoundsAt`        THE INVARIANT: what is kept of the rounds fits the roots that the verifier's
                    chain takes
  `Puts`            two transcripts are one but for numbers written in as nonces
  `Coins.Fit`, `ExtAt`   the lengths that the strict format asks; the outer trees hold y under the
                    roots cms
  `hasTest`         has round number j a test
  `SaltsAt`, `saltOf`, `opensK_salt`   every kept leaf's salt is the coins'; so is every opening's
  `anySh`           has some round the kind "shared"
  `rdS`, `rdE`      which positions are read (readS, readE of OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean, at
                    every protocol)
  `symK`, `read_trK`   the symbol at a position of what is kept: what the transcript reads there
  `look`            at a read position: its tree, with depth and root as the verifier has them, kept
                    rightly; the opening that `opensK` lays; what that leaf holds
  `opensK_some`     an opening stands at a read position alone
  `nodeF_eq`, `rnodeF_eq`, `climbP_eq`, `runForestF_eq`   the library has these functions twice
                    (OnBytes/TypedOracleCompiler/Run/VerifyDet.lean; OnBytes/TypedOracleCompiler/Joined/WalkAt.lean,
                    YesByCutsMore.lean): they are equal. Here trees and walks are said with nodeAt |
                    walkP, the chain and the request tree with chainF | rnodeF | climbF.

Limits: nothing on probability. Nothing says that a prover's run meets the invariant: that is
OnBytes/Prover/Chain.lean. Salts are spoken of by their lengths alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Defs
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
import OnBytes.TypedOracleCompiler.Joined.WalkAt
import OnBytes.TypedOracleCompiler.Joined.Clauses
import OnBytes.TypedOracleCompiler.Joined.K.YesRead
import OnBytes.TypedOracleCompiler.Joined.K.RunSome
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore
import Compile.MerkleList
import Iop.BatchFmt

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## One function under two names -/

theorem nodeF_eq (g : Fam (typedOracleFamily lam K L)) : TypedOracleCompiler.Run.nodeF g = nodeAt g := rfl
theorem rnodeF_eq (g : Fam (typedOracleFamily lam K L)) : TypedOracleCompiler.Run.rnodeF g = rnodeAt g := rfl

theorem climbP_eq (nd : Dig lam → Dig lam → Dig lam) :
    ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam), climbP nd path j c = climbF nd path j c
  | [], _, _ => rfl
  | s :: ss, j, c => by
    rw [climbF_cons, ← climbP_eq nd ss]
    rfl

theorem runForestF_eq (g : Fam (typedOracleFamily lam K L)) (F : Forest lam L) (s : List (Dig lam)) :
    TypedOracleCompiler.Run.runForestF g F s = walkP g F s := rfl

/-! ## Kept rightly, under fixed oracle functions g -/

/-- T is the tree of depth d over its own leaves' inputs -/
def TreeK.At (g : Fam (typedOracleFamily lam K L)) (d : ℕ) (T : TreeK lam L) : Prop :=
  T.lv = levelsF (nodeAt g) d ((List.range (2 ^ d)).map fun j => (g OracleName.leaf (T.inp j) : Dig lam))

/-- one sent component: a tree for each depth, each kept rightly; a leaf at which a position stands
holds that position's symbol and a salt of sMT bits -/
def CompAt (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (ds : List ℕ) (Ts : List (TreeK lam L)) :
    Prop :=
  Ts.length = ds.length ∧ ∀ k d T, ds[k]? = some d → Ts[k]? = some T → T.At g d ∧
    ∀ j p, posAt k j = some p → (T.inp j).body = emb p (r.rd o p) ∧ (T.inp j).salt.length = sMT

/-- **The invariant.** What is kept of the rounds s fits the roots R that the verifier's chain
takes: a component that is not sent is empty and has no tree; a sent one is kept rightly, and R has
its roots. -/
def RoundsAt (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    Kept lam L s → RootsOfChain lam s → Prop
  | [], _, _, _, _, _ => True
  | _ :: s, (a, A), (w, W), embS, (kp, ks), (rt, R) =>
      ((rt.1 = none ∧ kp.2.1 = [] ∧ a.NoShared) ∨
        (rt.1 = some (kp.2.1.map TreeK.root) ∧
          CompAt g sMT w.posAt0 (fun p => embS (.inl p)) kp.1.1 w.depth0 kp.2.1)) ∧
      ((rt.2 = none ∧ kp.2.2 = [] ∧ a.NoSlot) ∨
        (rt.2 = some (kp.2.2.map TreeK.root) ∧
          CompAt g sMT w.posAtJ (fun p => embS (.inl p)) kp.1.1 w.depthJ kp.2.2)) ∧
      RoundsAt g sMT s A W (fun p => embS (.inr p)) ks R

/-- τ' is τ but for nonces: the same oracles and verifier messages; in a round with a test the plain
part of the hashed component is τ's with some number written in; elsewhere the same plain part -/
def Puts : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Tr s → Tr s → Prop
  | [], _, _, _, _ => True
  | _ :: s, (a, A), (w, W), (m, c, τ), (m', c', τ') =>
      m'.1 = m.1 ∧ c' = c ∧
      (m'.2 = m.2 ∨
        (∃ g n, a.kind = .lo ∧ w.grJ = some g ∧
          m'.2 = a.plain.symm ((a.plain m.2).1, g.put n (a.plain m.2).2)) ∨
        (∃ g n, a.kind = .sh ∧ w.gr0 = some g ∧
          m'.2 = a.plain.symm (g.put n (a.plain m.2).1, (a.plain m.2).2))) ∧
      Puts s A W τ τ'

/-- the lengths that the strict format asks of the coins -/
structure Coins.Fit (co : Coins lam L) (sMT sFS depthReq : ℕ) : Prop where
  salt : co.salt.length = sFS
  leaf : ∀ i b k j, (co.leaf i b k j).length = sMT
  slot : co.slot < 2 ^ depthReq
  path : co.path.length = depthReq

/-- the trees over the external strings are kept rightly, hold y, and have the roots cms -/
structure ExtAt (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) {E : ExtSpec} (we : WireE E)
    (embE : E.Sym → Body L) (cms : List (Dig lam)) (y : E.Str) (xt : ℕ → TreeK lam L) : Prop where
  tree : ∀ p, (xt (we.which p)).At g we.depth
  root : ∀ p, (xt (we.which p)).root = cms.getD (we.which p) default
  body : ∀ p, ((xt (we.which p)).inp (we.leaf p)).body = embE (E.rd y p)
  salt : ∀ p, ((xt (we.which p)).inp (we.leaf p)).salt.length = sMT
  leaf : ∀ p, we.leaf p < 2 ^ we.depth

section
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)

/-- is this position of the prover's oracles read, given the plain parts, the verifier messages and
the roots -/
def rdS (pls : Plains Q.loc.shape) (ρ : Rho Q.loc.shape) (R : RootsOfChain lam Q.loc.shape) :
    OPos Q.loc.shape → Bool :=
  haveI := wq.decO
  fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann R pls))

/-- is this position of the external strings read -/
def rdE (ρ : Rho Q.loc.shape) : E.Pos → Bool :=
  haveI := wq.ext.dec
  fun p => decide (p ∈ Q.loc.extReads x ρ)

end

/-- has round number j of the rounds s a test: the slot's record in a local round, the shared one in
a shared round (as WireRB.pass reads them) -/
def hasTest : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → Bool
  | [], _, _, _ => false
  | _ :: _, (a, _), (w, _), 0 =>
    match a.kind with
    | .lo => w.grJ.isSome
    | .sh => w.gr0.isSome
  | _ :: s, (_, A), (_, W), j + 1 => hasTest s A W j

/-- **The kept leaves' salts are the coins'.** In round number i every leaf j of tree number k has
the salt co.leaf i b k j: b false in the shared component's trees, true in the slot's. -/
def SaltsAt (co : Coins lam L) : ℕ → (s : Shape) → Kept lam L s → Prop
  | _, [], _ => True
  | i, _ :: s, (kp, ks) =>
      (∀ k T, kp.2.1[k]? = some T → ∀ j, (T.inp j).salt = co.leaf i false k j) ∧
      (∀ k T, kp.2.2[k]? = some T → ∀ j, (T.inp j).salt = co.leaf i true k j) ∧
      SaltsAt co (i + 1) s ks

/-- the coins' salt of the leaf at which a position stands; i: the number of the first round of s -/
def saltOf (co : Coins lam L) : ℕ → (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → OPos s → Bits
  | _, [], _, _, p => nomatch p
  | i, _ :: _, (a, _), (w, _), .inl p => co.leaf i (a.own p) (w.tree p) (w.place p)
  | i, _ :: s, (_, A), (_, W), .inr q => saltOf co (i + 1) s A W q

/-- has some round the kind "shared" -/
def anySh : (s : Shape) → RoundSplits s → Bool
  | [], _ => false
  | _ :: s, (a, A) =>
    match a.kind with
    | .sh => true
    | .lo => anySh s A

/-! ## The look-up -/

/-- the symbol at a position of what is kept -/
def symK : (s : Shape) → Kept lam L s → (p : OPos s) → OSym s p
  | [], _, p => nomatch p
  | _ :: _, (kp, _), .inl p => Round.rd _ kp.1.1 p
  | _ :: s, (_, ks), .inr q => symK s ks q

theorem read_trK : ∀ (s : Shape) (kp : Kept lam L s) (ρ : Rho s) (p : OPos s),
    (trK s kp ρ).read p = symK s kp p
  | [], _, _, p => nomatch p
  | _ :: _, (_, _), (_, _), .inl _ => rfl
  | _ :: s, (_, ks), (_, ρ), .inr q => read_trK s ks ρ q

/-- an opening stands at a read position alone -/
theorem opensK_some : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (kp : Kept lam L s)
    (rd : OPos s → Bool) (p : OPos s) (op : Opening lam (OSym s p)),
    opensK s A W kp rd p = some op → rd p = true
  | [], _, _, _, _, p, _, _ => nomatch p
  | _ :: _, (_, _), (_, _), (_, _), rd, .inl p, op, h => by
    by_contra hn
    simp only [opensK, hn, if_false] at h
    cases h
  | _ :: s, (_, A), (_, W), (_, ks), rd, .inr q, op, h =>
    opensK_some s A W ks (fun p => rd (.inr p)) q op h

/-- every opening that the prover lays has the coins' salt of its leaf -/
theorem opensK_salt {co : Coins lam L} : ∀ (i : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (kp : Kept lam L s) (rd : OPos s → Bool) (p : OPos s) (op : Opening lam (OSym s p)),
    SaltsAt co i s kp → opensK s A W kp rd p = some op → op.salt = saltOf co i s A W p
  | _, [], _, _, _, _, p, _, _, _ => nomatch p
  | i, _ :: _, (a, _), (w, _), (kp, _), rd, .inl p, op, hS, h => by
    have hp : rd (.inl p) = true := opensK_some _ _ _ _ rd (.inl p) op h
    simp only [opensK, hp, if_true] at h
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 h
    cases ho : a.own p with
    | true =>
      rw [ho] at hT
      simp only [saltOf, ho]
      exact hS.2.1 _ T hT _
    | false =>
      rw [ho] at hT
      simp only [saltOf, ho]
      exact hS.1 _ T hT _
  | i, _ :: s, (_, A), (_, W), (_, ks), rd, .inr q, op, hS, h =>
    opensK_salt (i + 1) s A W ks (fun p => rd (.inr p)) q op hS.2.2 h

/-- one component: the tree of a position that the wire places in it -/
theorem CompAt.tree {g : Fam (typedOracleFamily lam K L)} {sMT : ℕ} {r : Round} {posAt : ℕ → ℕ → Option r.Pos}
    {emb : (p : r.Pos) → r.Sym p → Body L} {o : r.Orc} {ds : List ℕ} {Ts : List (TreeK lam L)}
    (h : CompAt g sMT posAt emb o ds Ts) {k j d : ℕ} {p : r.Pos} (hd : ds[k]? = some d)
    (hp : posAt k j = some p) :
    ∃ T, Ts[k]? = some T ∧ treeAt ds (Ts.map TreeK.root) k = some (d, T.root) ∧ T.At g d ∧
      (T.inp j).body = emb p (r.rd o p) ∧ (T.inp j).salt.length = sMT := by
  have hk : k < Ts.length := by
    rw [h.1]
    exact (List.getElem?_eq_some_iff.1 hd).1
  have hT : Ts[k]? = some Ts[k] := List.getElem?_eq_getElem hk
  obtain ⟨hA, hl⟩ := h.2 k d Ts[k] hd hT
  refine ⟨Ts[k], hT, ?_, hA, hl j p hp⟩
  unfold treeAt
  rw [hd, List.getElem?_map, hT]
  rfl

/-- **The look-up.** At a position that is read: its tree, with the depth and the root that the
verifier has for it, kept rightly; its leaf's number is one of that tree; the opening that the
prover lays; and what the leaf holds. -/
theorem look {g : Fam (typedOracleFamily lam K L)} {sMT : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (kp : Kept lam L s) (R : RootsOfChain lam s) (rd : OPos s → Bool),
      RoundsAt g sMT s A W embS kp R → RoundsQueryLayout.OKG s A W → ∀ p, rd p = true →
      ∃ (T : TreeK lam L) (d : ℕ), treeOf s A W R p = some (d, T.root) ∧ T.At g d ∧
        placeOf s A W p < 2 ^ d ∧
        opensK s A W kp rd p = some (T.opening (placeOf s A W p) (symK s kp p)) ∧
        (T.inp (placeOf s A W p)).body = embS p (symK s kp p) ∧
        (T.inp (placeOf s A W p)).salt.length = sMT
  | [], _, _, _, _, _, _, _, _, p, _ => nomatch p
  | _ :: _, (a, _), (w, _), embS, (kp, _), (rt, _), rd, hR, hW, .inl p, hp => by
    obtain ⟨h0, hJ, -⟩ := hR
    cases ho : a.own p with
    | true =>
      rcases hJ with ⟨-, -, hn⟩ | ⟨hrt, hc⟩
      · rw [hn.1 p] at ho
        cases ho
      · obtain ⟨d, hd, hlt⟩ := hW.1.place_ltJ p ho
        obtain ⟨T, hT, ht, hA, hb, hs⟩ := hc.tree hd (hW.1.posAtJ_place p ho)
        refine ⟨T, d, ?_, hA, hlt, ?_, hb, hs⟩
        · simp only [treeOf, ho, if_true, hrt, Option.getD_some]
          exact ht
        · simp only [opensK, hp, if_true, ho, hT, Option.map_some]
          rfl
    | false =>
      rcases h0 with ⟨-, -, hn⟩ | ⟨hrt, hc⟩
      · rw [hn.1 p] at ho
        cases ho
      · obtain ⟨d, hd, hlt⟩ := hW.1.place_lt0 p ho
        obtain ⟨T, hT, ht, hA, hb, hs⟩ := hc.tree hd (hW.1.posAt0_place p ho)
        refine ⟨T, d, ?_, hA, hlt, ?_, hb, hs⟩
        · simp only [treeOf, ho, Bool.false_eq_true, if_false, hrt, Option.getD_some]
          exact ht
        · simp only [opensK, hp, if_true, ho, Bool.false_eq_true, if_false, hT, Option.map_some]
          rfl
  | _ :: s, (_, A), (_, W), embS, (_, ks), (_, R), rd, hR, hW, .inr q, hp =>
    look s A W (fun p => embS (.inr p)) ks R (fun p => rd (.inr p)) hR.2.2 hW.2 q hp

end OnBytes.Prover
