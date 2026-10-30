-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Toy.lean: a test: at the small file of OnBytes/TypedOracleCompiler/Joined/ToyFile.lean every
hypothesis of the soundness theorem for a file is proved, all together, so that the theorem applies
there with nothing left open.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why: a theorem from a list of hypotheses says nothing if the list can never be met. Here it is met,
at a file whose chain 1 sends a tree that is read at two lists, one of them chain 3's.

The description speaks: its clauses are about EVERY statement (`on₀` is true everywhere), its
relation holds of the statements with x true and of no other, and the file's verifier accepts
somewhere and rejects somewhere (`accepts`, `rejects`, ToyFile.lean). So the language is neither
everything nor nothing (`lg_iff`).

Main names:
  `C`            the three chains' descriptions, made of the three tests of the file's verifier;
                 chain 3 tests the string that chain 1 has sent.
  `knows`        the five clauses, with all errors 0.
  `isSome_all_iff`, `decides`   no chain of the description rejects exactly where the file's
                 verifier accepts.
  `fileLaws`, `holes`   THE LIST, every field proved.
  `sound`, `lane`       the soundness theorem for a file, at this file, without a hypothesis.
  `lg_iff`       the language: x is true.
  `worst_eq`     the error a query that the theorem computes from the description: 0.

Limits: a test. The description is sound for a plain reason (a false x is rejected outright), so all
its errors are 0: the two tests on chain 1's string are in the description but soundness does not
need them. Only the case in which no later query takes in more of the instance is met here.
Digests have one bit here, so the theorem's bound, n εs + 2 (n + 1)² / 2^lam, is at least 1 for
every n: at this file the CONCLUSION (`sound`, `lane`) would hold of any event and says nothing.
What the test shows is `holes`: the hypotheses can hold together. That the list can be met says
nothing on whether it is met at a real file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.ToyFile
import OnBytes.TypedOracleCompiler.Joined.Top

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open scoped ENNReal

/-- statements: the instance and the external strings -/
abbrev St : Type := Bool × (oneExternalString 0 Unit).Str

/-- no error in any round -/
def err0 : (s : Shape) → Err s
  | [] => ()
  | _ :: s => (0, err0 s)

/-- chain 1's part of a transcript, with the front -/
def cut₁ (τ : Tr G.sh) : Tr G.c₁ := Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ
/-- chain 2's part, with the joining round -/
def cut₂ (τ : Tr G.sh) : Tr G.c₂ :=
  Tr.fst (s := G.c₂) (t := G.c₃) (Tr.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) τ)
/-- chain 3's part, with the seam -/
def cut₃ (τ : Tr G.sh) : Tr G.c₃ :=
  Tr.snd (s := G.c₂) (t := G.c₃) (Tr.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) τ)

/-- chain 1's string, in chain 1's part -/
def sOf (τ : Tr G.c₁) : Fin 2 → Bool := τ.2.2.1.1.1
/-- chain 1's block -/
def bOf₁ (τ : Tr G.c₁) : Blk := τ.2.2.2.1
/-- chain 3's block -/
def bOf₃ (τ : Tr G.c₃) : Blk := τ.2.2.2.1

theorem sOf_cut₁ (τ : Tr G.sh) : sOf (cut₁ τ) = str₁ τ := rfl
theorem bOf₁_cut₁ (τ : Tr G.sh) : bOf₁ (cut₁ τ) = (G.rho₁ τ.rho).1 := rfl
theorem bOf₃_cut₃ (τ : Tr G.sh) : bOf₃ (cut₃ τ) = (G.rho₃ τ.rho).1 := rfl

/-- The three chains' descriptions, made of the three tests of the file's verifier. Chain 1 rejects
unless x is true and its string holds true at the place that its own block names; it hands on its
string. Chain 2 hands the string on. Chain 3 rejects unless the string, which chain 1 has sent,
holds true at the place that chain 3's block names. The relation of the file's statements: x is
true. -/
@[reducible] def C : Links G St where
  A₁ := Fin 2 → Bool
  A₂ := Fin 2 → Bool
  W₀ := Unit
  W₁ := Unit
  W₂ := Unit
  out₁ := fun a τ => if a.1 && sOf τ (bit (bOf₁ τ)) then some (sOf τ) else none
  out₂ := fun o _ => some o
  out₃ := fun o τ => if o (bit (bOf₃ τ)) then some () else none
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a _ => a.1 = true
  R₁ := fun _ _ => True
  R₂ := fun _ _ => True
  e₁ := fun _ _ _ => ()
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := err0 _
  ε₂ := err0 _
  ε₃ := err0 _
  d₀ := ()
  d₁ := ()

theorem knows : C.Knows where
  know₁ := fun a _ => Doomed.of_forall _ _ fun τ b _ h _ => by
    have h' : (if (a.1 && sOf τ (bit (bOf₁ τ))) = true then some (sOf τ) else none) = some b := h
    by_cases hc : (a.1 && sOf τ (bit (bOf₁ τ))) = true
    · exact (Bool.and_eq_true_iff.1 hc).1
    · rw [if_neg hc] at h'
      cases h'
  know₂ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  know₃ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-- the three chains in a row, on the three parts of a transcript -/
theorem all_out (a : St) (τ : Tr G.sh) :
    C.all.out a τ =
      (C.out₁ a (cut₁ τ)).bind fun b => (C.out₂ b (cut₂ τ)).bind fun c => C.out₃ c (cut₃ τ) := rfl

/-- The description's three tests are those of the file's verifier: none of the chains rejects
exactly where it accepts. -/
theorem isSome_all_iff (x : Bool) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) :
    (C.all.out (x, y) τ).isSome = true ↔ F.D.accept x y τ = true := by
  rw [all_out]
  show ((if (x && str₁ τ (bit (G.rho₁ τ.rho).1)) = true then some (str₁ τ) else none).bind
      fun b => (some b).bind fun c =>
        if c (bit (G.rho₃ τ.rho).1) = true then some () else none).isSome = true ↔
    (x && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) = true
  cases hp : (x && str₁ τ (bit (G.rho₁ τ.rho).1)) <;>
    cases hq : str₁ τ (bit (G.rho₃ τ.rho).1) <;> simp [hq]

theorem decides (x : Bool) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) (h : F.D.accept x y τ = true) :
    (C.all.out (id x, y) τ).isSome = true := (isSome_all_iff x y τ).2 h

/-- the laws of the file's own side -/
theorem fileLaws : FileLaws F prjE := ⟨isLocal, laws, wq_okg, prjE_emb⟩

/-- **The list, every field proved.** -/
theorem holes : FileHoles F C prjE id := ⟨fileLaws, knows, decides⟩

/-- **The soundness theorem for a file applies at this file, with nothing left open.** -/
theorem sound (sMT sFS : ℕ) :
    SoundAt W (F.verify sMT sFS) (UnderTwo F.wq.ext) (C.Lg id) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) :=
  sound_verifyFile F sMT sFS R holes rfl

/-- The same with the event in the open. -/
theorem lane (sMT sFS : ℕ) :
    SoundLane W F.t (F.verify sMT sFS) (UnderTwo F.wq.ext) (C.Lg id) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) :=
  lane_verifyFile F sMT sFS R holes rfl

/-- The language of the file, by its description: x is true. -/
theorem lg_iff (x : Bool) (y : (oneExternalString 0 Unit).Str) : C.Lg id x y ↔ x = true :=
  ⟨fun h => (h trivial).elim fun _ hw => hw, fun h _ => ⟨(), h⟩⟩

theorem worst_err0 : ∀ s : Shape, _root_.Compile.Joined.worst (err0 s) = 0
  | [] => rfl
  | r :: s => by
    show max (((0 : ℕ) : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞))
      (_root_.Compile.Joined.worst (err0 s)) = 0
    rw [worst_err0 s, Nat.cast_zero, ENNReal.zero_div, max_self]

/-- The error a query that the theorem computes from the description: 0. -/
theorem worst_eq (N : ℕ) : C.worst N = 0 := by
  show max (_root_.Compile.Joined.worst (err0 G.c₁))
    (max ((N : ℝ≥0∞) * _root_.Compile.Joined.worst (err0 G.c₂))
      (_root_.Compile.Joined.worst (err0 G.c₃))) = 0
  simp only [worst_err0, mul_zero, max_self]

end TypedOracleCompiler.Joined.Toy
