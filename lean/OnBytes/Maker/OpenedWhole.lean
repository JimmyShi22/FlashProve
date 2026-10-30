-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OpenedWhole.lean: records on the openings over two lists of rounds give one record
over the two in a row.

OnBytes/Maker/TypingOpened.lean has tools for the record `Opened`
(OnBytes/TypedOracleCompiler/Joined/K/YesRead.lean) over one chain's rounds. This file lays records of two lists of
rounds together.

  `opened_app`         `Opened` over s and over u give `Opened` over s ++ u, at the cuts of the wire
                       records, the roots, "is read" and the openings.
  `opened_three`       for any file: the three chains' records give the one over the whole, at what
                       the three chains have yielded, laid in a row.

OnBytes/Maker/TypingAlike.lean has the one record at a value of `typeFile`
(`opened_wholeA`).

Not claimed. That a path leads to a root. Nothing on soundness.


-/
import OnBytes.Maker.TypingOpened

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-- **Two lists of rounds in a row.** -/
theorem opened_app {lam K : ℕ} (sMT : ℕ) :
    ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u) (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
      (R : RootsOfChain lam (s ++ u)) (rd : OPos (s ++ u) → Bool)
      (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
      TypedOracleCompiler.Joined.Opened sMT s A (WireSB.fst W) (RT.fst R) (fun p => rd (OPos.left p))
        (opensL f) →
      TypedOracleCompiler.Joined.Opened sMT u B (WireSB.snd W) (RT.snd (s := s) R)
        (fun p => rd (OPos.right (s := s) p)) (opensR f) →
      TypedOracleCompiler.Joined.Opened sMT (s ++ u) (RoundSplits.app A B) W R rd f
  | [], _, _, _, _, _, _, _, _, h₂ => h₂
  | _ :: s, u, (_, A), B, (_, W), (_, R), rd, f, h₁, h₂ =>
    have ih := opened_app sMT s u A B W R (fun p => rd (.inr p)) (fun p => f (.inr p))
      ⟨fun p op h => h₁.only (.inr p) op h, fun p h => h₁.all (.inr p) h,
        fun p op d c hr h ht => h₁.path (.inr p) op d c hr h ht⟩ h₂
    { only := fun p op h =>
        match p, op, h with
        | .inl q, op, h => h₁.only (.inl q) op h
        | .inr q, op, h => ih.only q op h
      all := fun p h =>
        match p, h with
        | .inl q, h => h₁.all (.inl q) h
        | .inr q, h => ih.all q h
      path := fun p op d c hr h ht =>
        match p, op, hr, h, ht with
        | .inl q, op, hr, h, ht => h₁.path (.inl q) op d c hr h ht
        | .inr q, op, hr, h, ht => ih.path q op d c hr h ht }

/-- **The three chains' records give the one over the whole.** -/
theorem opened_three {lam K : ℕ} {G : Chains} {Y : Type} {E : ExtSpec} (sMT : ℕ) (D : Desc G Y E)
    (wq : ProtocolQueryLayout lam K D.batch) (x : Y) (π : OneProtocolProof lam D.batch) (a : Out lam G.c₁)
    (b : Out lam G.c₂) (e : Out lam G.c₃)
    (h₁ : TypedOracleCompiler.Joined.Opened sMT G.c₁ G.A₁ (wire₁ wq) a.2.1 (rd₁ D wq x π a b e) (op₁ D π))
    (h₂ : TypedOracleCompiler.Joined.Opened sMT G.c₂ G.A₂ (wire₂ wq) b.2.1 (rd₂ D wq x π a b e) (op₂ D π))
    (h₃ : TypedOracleCompiler.Joined.Opened sMT G.c₃ G.A₃ (wire₃ wq) e.2.1 (rd₃ D wq x π a b e) (op₃ D π)) :
    TypedOracleCompiler.Joined.Opened sMT G.sh G.ann wq.sh (glue a b e).2.1
      (readS D wq x π (glue a b e).1 (glue a b e).2.1) π.opens := by
  show TypedOracleCompiler.Joined.Opened sMT (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh
    (RT.app a.2.1 (RT.app b.2.1 e.2.1)) (TypedOracleCompiler.Joined.rd D wq x π a b e) π.opens
  refine opened_app sMT _ _ _ _ _ _ _ _ ?_ (opened_app sMT _ _ _ _ _ _ _ _ ?_ ?_)
  · rw [RT.fst_app]
    exact h₁
  · rw [RT.snd_app, RT.fst_app]
    exact h₂
  · rw [RT.snd_app, RT.snd_app]
    exact h₃

end OnBytes.Maker
