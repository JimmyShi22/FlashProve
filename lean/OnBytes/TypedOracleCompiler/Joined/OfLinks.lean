-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/OfLinks.lean: what is owed for a file whose verifier is made from its three
chains' descriptions.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


OnBytes/TypedOracleCompiler/Joined/Top.lean lists what is owed for a file. Two entries tie the file's decision to
the description: where the file's verifier accepts, none of the three chains rejects (`decides`);
and the decision depends on the oracles only where it reads (`isLocal`). CompileK/Joined/Row.lean
makes the file's verifier from three interactive oracle reductions in a row. At such a file
`decides` is proved, and `isLocal` is proved from one law for each chain.

Main names:
  `Row.Snd`, `Row.links`: the three chains' descriptions as the top takes them (`Links`): the stages
    as reductions, with the data of which their soundness clauses speak.
  `Row.all_out`: the three reductions in a row decide as the row does.
  `fileHoles_of_row`, `fileHolesLate_of_row`: the top's two lists at such a file.
  `qb_okg_of_row`: the laws of such a file's wire record, with the number of openings computed.

Limits: `isLocal` is not gone: in its place stand the three laws of `Row.IsLocal`, which are owed of
the description. Nothing here says that a real file's chains have this form.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Joined.RowCount
import OnBytes.TypedOracleCompiler.Joined.Top

set_option autoImplicit false

noncomputable section

namespace CompileK.Joined.Row
open Iop
open _root_.Compile.Joined (Chains Desc)
open _root_.TypedOracleCompiler.Joined (Links)

variable {G : Chains} {Y : Type} {E : ExtSpec} (Rw : Row G Y E)

/-- The data of which the three chains' soundness clauses speak (`Links`,
OnBytes/TypedOracleCompiler/Joined/Top.lean, where each field is explained). A statement is a pair of an explicit
and an implicit part. -/
structure Snd where
  W₀ : Type
  W₁ : Type
  W₂ : Type
  on₀ : Y × E.Str → Prop
  on₁ : Rw.X₁ × Rw.E₁.Str → Prop
  on₂ : Rw.X₂ × Rw.E₂.Str → Prop
  R₀ : Y × E.Str → W₀ → Prop
  R₁ : Rw.X₁ × Rw.E₁.Str → W₁ → Prop
  R₂ : Rw.X₂ × Rw.E₂.Str → W₂ → Prop
  e₁ : Y × E.Str → Tr G.c₁ → W₁ → W₀
  e₂ : Rw.X₁ × Rw.E₁.Str → Tr G.c₂ → W₂ → W₁
  e₃ : Rw.X₂ × Rw.E₂.Str → Tr G.c₃ → Unit → W₂
  ε₁ : Err G.c₁
  ε₂ : Err G.c₂
  ε₃ : Err G.c₃
  d₀ : W₀
  d₁ : W₁

/-- the three chains' descriptions as the top takes them: each stage as a reduction between
statements -/
def links (P : Rw.Snd) : Links G (Y × E.Str) where
  A₁ := Rw.X₁ × Rw.E₁.Str
  A₂ := Rw.X₂ × Rw.E₂.Str
  W₀ := P.W₀
  W₁ := P.W₁
  W₂ := P.W₂
  out₁ := Rw.S₁.ior.red.out
  out₂ := Rw.S₂.ior.red.out
  out₃ := fun a τ => Rw.S₃.out a.1 a.2 τ
  on₀ := P.on₀
  on₁ := P.on₁
  on₂ := P.on₂
  R₀ := P.R₀
  R₁ := P.R₁
  R₂ := P.R₂
  e₁ := P.e₁
  e₂ := P.e₂
  e₃ := P.e₃
  ε₁ := P.ε₁
  ε₂ := P.ε₂
  ε₃ := P.ε₃
  d₀ := P.d₀
  d₁ := P.d₁

/-- the three reductions in a row decide as the row does -/
theorem all_out (P : Rw.Snd) (x : Y) (y : E.Str) (τ : Tr G.sh) :
    (Rw.links P).all.out (x, y) τ = Rw.ior.out x y τ := by
  show Option.bind (Option.map _ (Rw.S₁.out x y (Tr.fst (s := G.c₁) τ))) _ =
    Option.bind (Rw.S₁.out x y (Tr.fst (s := G.c₁) τ)) _
  cases Rw.S₁.out x y (Tr.fst (s := G.c₁) τ) with
  | none => rfl
  | some x₁ =>
    show Option.bind (Option.map _ (Rw.S₂.out x₁ (Rw.S₁.imp y (Tr.fst (s := G.c₁) τ))
        (Tr.fst (s := G.c₂) (Tr.snd (s := G.c₁) τ)))) _ =
      Option.bind (Rw.S₂.out x₁ (Rw.S₁.imp y (Tr.fst (s := G.c₁) τ))
        (Tr.fst (s := G.c₂) (Tr.snd (s := G.c₁) τ))) _
    cases Rw.S₂.out x₁ (Rw.S₁.imp y (Tr.fst (s := G.c₁) τ))
      (Tr.fst (s := G.c₂) (Tr.snd (s := G.c₁) τ)) <;> rfl

end CompileK.Joined.Row

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row Opens Src)

/-! ## The top's two lists at such a file -/

section Lists
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type}
  {E : ExtSpec} {F : FileW W G Y E} {Rw : Row G Y E} {P : Rw.Snd} {prjE : Body L → Option E.Sym}
  {early : Y → Y}

/-- All that is owed for a file whose verifier is made from a row and decides on `early x`: the
entry `decides` is proved; for `isLocal` stand the three chains' own laws. -/
theorem fileHoles_of_row (hD : F.D = Rw.desc early) (hloc : Rw.IsLocal) (laws : G.Laws)
    (wire : F.wq.OKG) (prjE_emb : ∀ a, prjE (F.embE a) = some a) (knows : (Rw.links P).Knows) :
    FileHoles F (Rw.links P) prjE early where
  isLocal := by rw [hD]; exact Rw.desc_isLocal hloc early
  laws := laws
  wire := wire
  prjE_emb := prjE_emb
  knows := knows
  decides := fun x y τ h => by
    rw [hD] at h
    rw [Row.all_out]
    exact h

/-- The same where the query of round n takes in the rest of the instance: the verifier decides on
x itself. -/
theorem fileHolesLate_of_row {n : ℕ} (hD : F.D = Rw.desc id) (hloc : Rw.IsLocal) (laws : G.Laws)
    (wire : F.wq.OKG) (prjE_emb : ∀ a, prjE (F.embE a) = some a)
    (knows : (Rw.links P).KnowsLate early n) (idem : ∀ x, early (early x) = early x) (pos : 0 < n)
    (inFirst : n ≤ G.s₁.length) : FileHolesLate F (Rw.links P) prjE early n where
  isLocal := by rw [hD]; exact Rw.desc_isLocal hloc id
  laws := laws
  wire := wire
  prjE_emb := prjE_emb
  knows := knows
  decides := fun x y τ h => by
    rw [hD] at h
    rw [Row.all_out]
    exact h
  idem := idem
  pos := pos
  inFirst := inFirst

end Lists

/-! ## The wire record of such a file -/

/-- The laws of the wire record of a file whose verifier is made from a row, with the number of
openings computed from the three chains' numbers (CompileK/Joined/RowCount.lean). What is left of
`Wires.qb_okg` (OnBytes/TypedOracleCompiler/Joined/WireOf.lean): each part's wire record is lawful, no tree is
deeper than maxDepth, and the wire record of the external strings is lawful. -/
theorem qb_okg_of_row {lam K : ℕ} {G : Chains} {Y : Type} {E : ExtSpec} (V : Wires lam K G)
    (Rw : Row G Y E) (pre : Y → Y) (ext : WireE E) (decO : DecidableEq (OPos G.sh))
    (maxDepth : ℕ) {n₁ n₂ n₃ k₁ k₂ : ℕ} (hV : V.OKG) (he : ext.OK) (hd : V.DepthLe maxDepth)
    (h₁ : Opens Rw.S₁.ior n₁) (h₂ : Opens Rw.S₂.ior n₂) (h₃ : Opens Rw.S₃.ior n₃)
    (s₁ : Src Rw.S₁.ior k₁) (s₂ : Src Rw.S₂.ior k₂) (p₁ : 1 ≤ k₁) (p₂ : 1 ≤ k₂) :
    (V.qb (Rw.desc pre) ext decO (n₁ + k₁ * (n₂ + k₂ * n₃)) maxDepth).OKG :=
  V.qb_okg (Rw.desc pre) ext decO _ maxDepth hV he
    (Rw.desc_opens (Rw.opens h₁ h₂ h₃ s₁ s₂ p₁ p₂) pre) hd

end TypedOracleCompiler.Joined
