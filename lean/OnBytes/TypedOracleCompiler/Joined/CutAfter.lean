-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/CutAfter.lean: what a compiled verifier does behind its chain, over a shape
`s ++ u`, is made of what it does over s and over u.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Behind the chain the verifier lists the checks of the openings (`checksB`, or tree by tree
`forestsB`), tests the strict format (`strictSB`), and builds the transcript on which the local
verifier decides (`effPlains`, `mkTr`; all: OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean). Each of these
goes through the rounds one by one. So over `s ++ u` each is the value over s joined with the value
over u. The wire records and the roots are cut as in OnBytes/TypedOracleCompiler/Joined/Cut.lean, positions by the
library's `OPos.left` and `OPos.right` (Iop/ShapeKit.lean).

Main names:
  `embL`, `embR`: how the symbols of the rounds of s, of u, are written into a leaf.
  `opensL`, `opensR`: the openings at the positions of s, of u.
  `embL_ofLeft`, `embR_ofRight`, `opensL_eq`, `opensR_eq`: these four said through `OPos.left`,
    `OPos.right` and the library's `OSym.ofLeft`, `OSym.ofRight`.
  `checksB_app`, `forestsB_app`: both halves give a list, and the whole gives the two in a row; or
    one half gives none, and so does the whole.
  `strictSB_app`: both halves pass. `effPlains_app`, `mkTr_app`: the two halves in a row.

Limits: nothing here speaks of the chain, of the external strings, of the request tree, of a
protocol or of soundness. Nothing is asked of the wire records or of the roots.
No other file of the library uses `checksB_app`, `effPlains_app`, `embL_ofLeft`, `embR_ofRight` or
`appO_some` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Cut

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Symbols and openings at the positions of the two parts -/

/-- how the symbols of the rounds of s are written -/
def embL : {s u : Shape} → ((p : OPos (s ++ u)) → OSym (s ++ u) p → Body L) →
    (p : OPos s) → OSym s p → Body L
  | _ :: _, _, emb, .inl p => emb (.inl p)
  | _ :: _, _, emb, .inr p => embL (fun q => emb (.inr q)) p

/-- how the symbols of the rounds of u are written -/
def embR : {s u : Shape} → ((p : OPos (s ++ u)) → OSym (s ++ u) p → Body L) →
    (p : OPos u) → OSym u p → Body L
  | [], _, emb => emb
  | _ :: s, _, emb => embR (s := s) fun q => emb (.inr q)

/-- the openings at the positions of s -/
def opensL : {s u : Shape} → ((p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) →
    (p : OPos s) → Option (Opening lam (OSym s p))
  | _ :: _, _, f, .inl p => f (.inl p)
  | _ :: _, _, f, .inr p => opensL (fun q => f (.inr q)) p

/-- the openings at the positions of u -/
def opensR : {s u : Shape} → ((p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) →
    (p : OPos u) → Option (Opening lam (OSym u p))
  | [], _, f => f
  | _ :: s, _, f => opensR (s := s) fun q => f (.inr q)

theorem embL_ofLeft : ∀ {s u : Shape} (emb : (p : OPos (s ++ u)) → OSym (s ++ u) p → Body L)
    (p : OPos s) (a : OSym (s ++ u) (OPos.left p)),
    embL emb p (OSym.ofLeft p a) = emb (OPos.left p) a
  | _ :: _, _, _, .inl _, _ => rfl
  | _ :: _, _, emb, .inr p, a => embL_ofLeft (fun q => emb (.inr q)) p a

theorem embR_ofRight : ∀ {s u : Shape} (emb : (p : OPos (s ++ u)) → OSym (s ++ u) p → Body L)
    (p : OPos u) (a : OSym (s ++ u) (OPos.right (s := s) p)),
    embR emb p (OSym.ofRight (s := s) p a) = emb (OPos.right (s := s) p) a
  | [], _, _, _, _ => rfl
  | _ :: s, _, emb, p, a => embR_ofRight (s := s) (fun q => emb (.inr q)) p a

theorem opensL_eq : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) (p : OPos s),
    opensL f p = (f (OPos.left p)).map fun op => ⟨OSym.ofLeft p op.sym, op.salt, op.path⟩
  | _ :: _, _, f, .inl p => by
    show f (.inl p) = (f (.inl p)).map fun op => ⟨op.sym, op.salt, op.path⟩
    cases f (.inl p) <;> rfl
  | _ :: _, _, f, .inr p => opensL_eq (fun q => f (.inr q)) p

theorem opensR_eq : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) (p : OPos u),
    opensR f p =
      (f (OPos.right (s := s) p)).map fun op => ⟨OSym.ofRight (s := s) p op.sym, op.salt, op.path⟩
  | [], _, f, p => by
    show f p = (f p).map fun op => ⟨op.sym, op.salt, op.path⟩
    cases f p <;> rfl
  | _ :: s, _, f, p => opensR_eq (s := s) (fun q => f (.inr q)) p

/-! ## The checks of the openings -/

/-- two lists that may be missing, in a row -/
def appO {α : Type} (a b : Option (List α)) : Option (List α) :=
  a.bind fun x => b.map fun y => x ++ y

theorem appO_some {α : Type} (x y : List α) : appO (some x) (some y) = some (x ++ y) := rfl

theorem appO_eq_some {α : Type} {a b : Option (List α)} {z : List α} :
    appO a b = some z ↔ ∃ x y, a = some x ∧ b = some y ∧ z = x ++ y := by
  cases a <;> cases b <;> simp [appO, eq_comm]

theorem checksB_app : ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u)
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
    (emb : (p : OPos (s ++ u)) → OSym (s ++ u) p → Body L)
    (R : RootsOfChain lam (s ++ u)) (isRead : OPos (s ++ u) → Bool)
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    checksB (s ++ u) (RoundSplits.app A B) W emb R isRead f =
      appO (checksB s A (WireSB.fst W) (embL emb) (RT.fst R) (fun p => isRead (OPos.left p))
          (opensL f))
        (checksB u B (WireSB.snd W) (embR emb) (RT.snd (s := s) R)
          (fun p => isRead (OPos.right (s := s) p)) (opensR f))
  | [], u, _, B, W, emb, R, isRead, f => by
    show checksB u B W emb R isRead f = appO (some []) (checksB u B W emb R isRead f)
    cases checksB u B W emb R isRead f <;> rfl
  | r :: s, u, (a, A), B, (w, W), emb, (c, R), isRead, f => by
    have ih := checksB_app s u A B W (fun p => emb (.inr p)) R (fun p => isRead (.inr p))
      (fun p => f (.inr p))
    show (match checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) (c.1.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) (c.2.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksB (s ++ u) (RoundSplits.app A B) W (fun p => emb (.inr p)) R
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c => some (a ++ b ++ c)
      | _, _, _ => none) =
      appO (match checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) (c.1.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) (c.2.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        checksB s A (WireSB.fst W) (embL fun p => emb (.inr p)) (RT.fst R)
          (fun p => isRead (.inr (OPos.left p))) (opensL fun p => f (.inr p)) with
      | some a, some b, some c => some (a ++ b ++ c)
      | _, _, _ => none)
        (checksB u B (WireSB.snd W) (embR fun p => emb (.inr p)) (RT.snd (s := s) R)
          (fun p => isRead (.inr (OPos.right (s := s) p))) (opensR fun p => f (.inr p)))
    rw [ih]
    generalize checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) (c.1.getD [])
      (fun p => isRead (.inl p)) (fun p => f (.inl p)) = x0
    generalize checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) (c.2.getD [])
      (fun p => isRead (.inl p)) (fun p => f (.inl p)) = xJ
    generalize checksB s A (WireSB.fst W) (embL fun p => emb (.inr p)) (RT.fst R)
      (fun p => isRead (.inr (OPos.left p))) (opensL fun p => f (.inr p)) = xL
    generalize checksB u B (WireSB.snd W) (embR fun p => emb (.inr p)) (RT.snd (s := s) R)
      (fun p => isRead (.inr (OPos.right (s := s) p))) (opensR fun p => f (.inr p)) = xR
    cases x0 <;> cases xJ <;> cases xL <;> cases xR <;> simp [appO]

theorem forestsB_app : ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u)
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
    (emb : (p : OPos (s ++ u)) → OSym (s ++ u) p → Body L)
    (R : RootsOfChain lam (s ++ u)) (isRead : OPos (s ++ u) → Bool)
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    forestsB (s ++ u) (RoundSplits.app A B) W emb R isRead f =
      appO (forestsB s A (WireSB.fst W) (embL emb) (RT.fst R) (fun p => isRead (OPos.left p))
          (opensL f))
        (forestsB u B (WireSB.snd W) (embR emb) (RT.snd (s := s) R)
          (fun p => isRead (OPos.right (s := s) p)) (opensR f))
  | [], u, _, B, W, emb, R, isRead, f => by
    show forestsB u B W emb R isRead f = appO (some []) (forestsB u B W emb R isRead f)
    cases forestsB u B W emb R isRead f <;> rfl
  | r :: s, u, (a, A), B, (w, W), emb, (c, R), isRead, f => by
    have ih := forestsB_app s u A B W (fun p => emb (.inr p)) R (fun p => isRead (.inr p))
      (fun p => f (.inr p))
    show (match checksTrees w.posAt0 (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (c.1.getD []),
        checksTrees w.posAtJ (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (c.2.getD []),
        forestsB (s ++ u) (RoundSplits.app A B) W (fun p => emb (.inr p)) R
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c => some (forestsT w.pr0 a ++ (forestsT w.prJ b ++ c))
      | _, _, _ => none) =
      appO (match checksTrees w.posAt0 (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (c.1.getD []),
        checksTrees w.posAtJ (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (c.2.getD []),
        forestsB s A (WireSB.fst W) (embL fun p => emb (.inr p)) (RT.fst R)
          (fun p => isRead (.inr (OPos.left p))) (opensL fun p => f (.inr p)) with
      | some a, some b, some c => some (forestsT w.pr0 a ++ (forestsT w.prJ b ++ c))
      | _, _, _ => none)
        (forestsB u B (WireSB.snd W) (embR fun p => emb (.inr p)) (RT.snd (s := s) R)
          (fun p => isRead (.inr (OPos.right (s := s) p))) (opensR fun p => f (.inr p)))
    rw [ih]
    generalize checksTrees w.posAt0 (fun p => emb (.inl p))
      (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (c.1.getD []) = x0
    generalize checksTrees w.posAtJ (fun p => emb (.inl p))
      (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (c.2.getD []) = xJ
    generalize forestsB s A (WireSB.fst W) (embL fun p => emb (.inr p)) (RT.fst R)
      (fun p => isRead (.inr (OPos.left p))) (opensL fun p => f (.inr p)) = xL
    generalize forestsB u B (WireSB.snd W) (embR fun p => emb (.inr p)) (RT.snd (s := s) R)
      (fun p => isRead (.inr (OPos.right (s := s) p))) (opensR fun p => f (.inr p)) = xR
    cases x0 <;> cases xJ <;> cases xL <;> cases xR <;> simp [appO]

/-! ## The strict format -/

theorem strictSB_app (sMT : ℕ) : ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u)
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (R : RootsOfChain lam (s ++ u))
    (isRead : OPos (s ++ u) → Bool)
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    strictSB sMT (s ++ u) (RoundSplits.app A B) W R isRead f =
      (strictSB sMT s A (WireSB.fst W) (RT.fst R) (fun p => isRead (OPos.left p)) (opensL f) &&
        strictSB sMT u B (WireSB.snd W) (RT.snd (s := s) R)
          (fun p => isRead (OPos.right (s := s) p)) (opensR f))
  | [], _, _, _, _, _, _, _ => (Bool.true_and _).symm
  | _ :: s, u, (_, A), B, (w, W), (c, R), isRead, f => by
    have ih := strictSB_app sMT s u A B W R (fun p => isRead (.inr p)) (fun p => f (.inr p))
    show (strictTrees sMT w.posAt0 w.depth0 (c.1.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
        strictTrees sMT w.posAtJ w.depthJ (c.2.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
        strictSB sMT (s ++ u) (RoundSplits.app A B) W R (fun p => isRead (.inr p))
          (fun p => f (.inr p))) = _
    rw [ih, ← Bool.and_assoc]
    rfl

/-! ## The transcript that the verifier builds -/

theorem effPlains_app : ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u) (R : RootsOfChain lam (s ++ u))
    (pls : Plains (s ++ u)),
    effPlains (s ++ u) (RoundSplits.app A B) R pls =
      Plains.app (effPlains s A (RT.fst R) (Plains.fst pls))
        (effPlains u B (RT.snd (s := s) R) (Plains.snd (s := s) pls))
  | [], _, _, _, _, _ => rfl
  | _ :: s, u, (a, A), B, (c, R), (pl, pls) =>
    congrArg (Prod.mk (effPlain a c pl)) (effPlains_app s u A B R pls)

theorem mkTr_app : ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u)
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (R : RootsOfChain lam (s ++ u)) (pls : Plains (s ++ u))
    (ρ : Rho (s ++ u)) (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    mkTr (s ++ u) (RoundSplits.app A B) W R pls ρ f =
      Tr.app (mkTr s A (WireSB.fst W) (RT.fst R) (Plains.fst pls) (Rho.fst ρ) (opensL f))
        (mkTr u B (WireSB.snd W) (RT.snd (s := s) R) (Plains.snd (s := s) pls)
          (Rho.snd (s := s) ρ) (opensR f))
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: s, u, (a, A), B, (w, W), (rt, R), (pl, pls), (c, ρ), f => by
    have ih := mkTr_app s u A B W R pls ρ fun p => f (.inr p)
    show mkTr (r :: (s ++ u)) (a, RoundSplits.app A B) (w, W) (rt, R) (pl, pls) (c, ρ) f =
      Tr.app (mkTr (r :: s) (a, A) (w, WireSB.fst W) (rt, RT.fst R) (pl, Plains.fst pls)
          (c, Rho.fst ρ) (opensL f))
        (mkTr u B (WireSB.snd W) (RT.snd (s := s) R) (Plains.snd (s := s) pls)
          (Rho.snd (s := s) ρ) (opensR fun p => f (.inr p)))
    rw [Compile.Batch.mkTr, Compile.Batch.mkTr, ih]
    refine Prod.ext (Prod.ext (congrArg w.pt.ofSyms (funext fun p => ?_)) rfl) rfl
    have e : opensL f (Sum.inl p) = f (Sum.inl p) := rfl
    cases rootAt w rt p
    · rfl
    · rcases hf : f (Sum.inl p) with _ | op <;> simp only [e, hf]

end TypedOracleCompiler.Joined
