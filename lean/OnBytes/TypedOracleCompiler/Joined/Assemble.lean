-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Assemble.lean: the proof string of a file, made of what is read for each of its
three chains. Definitions, and the laws by which the parts are had back.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The compiled verifier of a file takes one proof string for the one joined protocol (`FileW.Prf`,
OnBytes/TypedOracleCompiler/Joined/Wire.lean): one list of roots, the plain parts and the openings of all rounds. A
file's bytes are read chain by chain. Here is the step between: what is read for one chain
(`ChainStr`), and the proof string of the whole from three of these and what belongs to no chain.

Main names:
  `opensApp f g`: the openings at the positions of s ++ u, from those of s and those of u; the
    inverse of the cuts `opensL`, `opensR` (OnBytes/TypedOracleCompiler/Joined/CutAfter.lean): `opensL_app`,
    `opensR_app`, `opensApp_LR`; at a position: `opensApp_left`, `opensApp_right`.
  `ChainStr lam c`: for the rounds c of one chain, its first round among them: the roots that the
    chain sends, in their order; the plain parts; the openings at the positions of its oracles.
  `FileW.assemble`: the proof string of the file: the three chains' roots in a row, their plain
    parts in a row, their openings; and the salt of the first chain's first query, the openings of
    the external strings, the request root with the slot's number, path and salt.
  `assemble_pls₁` ... `assemble_pls₃`: the plain parts that the file's verifier hands to each chain
    (`pls₁`, `pls₂`, `pls₃`, OnBytes/TypedOracleCompiler/Joined/Verifier.lean) are the chain's own.
  `assemble_opens₁` ... `assemble_opens₃`: so are the openings at each chain's positions.
  `assemble_roots`, `assemble_drop₁`, `assemble_drop₂`: the roots; what is left of them behind the
    first chain's, and behind the second's.
  `FileW.cut₁` ... `cut₃`, `assemble_cut`: each proof string is assembled from its cuts, given where
    its list of roots is cut.

A tree that a later chain takes over. Its root stands in the sender's list of roots, its positions
are positions of the sender's oracles, and so an opening in it lies in the SENDER's `ChainStr`, also
where the file's bytes hold that opening in the later chain's part.

Limits: definitions and equations; nothing here reads bytes, and nothing says that the verifier
accepts. `ChainStr.opens` has at most one opening at a position. A file's bytes hold two openings of
one leaf wherever two lists of positions meet in it. Which of the two is laid here is the choice of
whoever reads the bytes; the other is seen by nothing in this file, and no test for doubles is made
here. What makes the choice harmless is in OnBytes/TypedOracleCompiler/Joined/Clauses.lean (`notOnce_agree`):
outside the hash event `EM` two accepted openings of one leaf give one symbol.
That theorem says so for a coherent annotation, a wire record with its laws and a writing of symbols
that can be read back (its hco, hW, hprj).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Verifier
import OnBytes.TypedOracleCompiler.Joined.CutAfter

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Openings of two parts in a row -/

/-- the openings at the positions of s ++ u, from those at the positions of s and of u -/
def opensApp : {s u : Shape} → ((p : OPos s) → Option (Opening lam (OSym s p))) →
    ((p : OPos u) → Option (Opening lam (OSym u p))) →
    (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))
  | [], _, _, g, p => g p
  | _ :: _, _, f, _, .inl p => f (.inl p)
  | _ :: _, _, f, g, .inr p => opensApp (fun q => f (.inr q)) g p

theorem opensL_app : ∀ {s u : Shape} (f : (p : OPos s) → Option (Opening lam (OSym s p)))
    (g : (p : OPos u) → Option (Opening lam (OSym u p))) (p : OPos s),
    opensL (opensApp f g) p = f p
  | _ :: _, _, _, _, .inl _ => rfl
  | _ :: _, _, f, g, .inr p => opensL_app (fun q => f (.inr q)) g p

theorem opensR_app : ∀ {s u : Shape} (f : (p : OPos s) → Option (Opening lam (OSym s p)))
    (g : (p : OPos u) → Option (Opening lam (OSym u p))),
    opensR (s := s) (opensApp f g) = g
  | [], _, _, _ => rfl
  | _ :: _, _, f, g => opensR_app (fun q => f (.inr q)) g

/-- openings over s ++ u are those of their two cuts -/
theorem opensApp_LR : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) (p : OPos (s ++ u)),
    opensApp (opensL f) (opensR (s := s) f) p = f p
  | [], _, _, _ => rfl
  | _ :: _, _, _, .inl _ => rfl
  | _ :: s, _, f, .inr p => opensApp_LR (s := s) (fun q => f (.inr q)) p

/-- at a position of the first part -/
theorem opensApp_left {s u : Shape} (f : (p : OPos s) → Option (Opening lam (OSym s p)))
    (g : (p : OPos u) → Option (Opening lam (OSym u p))) (p : OPos s) :
    ((opensApp f g) (OPos.left p)).map
      (fun op => (⟨OSym.ofLeft p op.sym, op.salt, op.path⟩ : Opening lam (OSym s p))) = f p := by
  rw [← opensL_eq, opensL_app]

/-- at a position of the second part -/
theorem opensApp_right {s u : Shape} (f : (p : OPos s) → Option (Opening lam (OSym s p)))
    (g : (p : OPos u) → Option (Opening lam (OSym u p))) (p : OPos u) :
    ((opensApp f g) (OPos.right (s := s) p)).map
      (fun op => (⟨OSym.ofRight (s := s) p op.sym, op.salt, op.path⟩ : Opening lam (OSym u p))) =
      g p := by
  rw [← opensR_eq, opensR_app]

/-! ## What is read for one chain -/

/-- What is read for one chain with the rounds c. -/
structure ChainStr (lam : ℕ) (c : Shape) where
  /-- the roots that the chain sends, in their order -/
  roots : List (Dig lam)
  /-- the plain parts of its rounds -/
  plains : Plains c
  /-- the openings at the positions of its oracles, whichever chain reads them -/
  opens : (p : OPos c) → Option (Opening lam (OSym c p))

/-! ## The proof string of a file -/

namespace FileW
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)

/-- The proof string of the file from its three chains as read, and what belongs to no chain. -/
def assemble (salt : Bits) (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂)
    (k₃ : ChainStr lam G.c₃) (ext : E.Pos → Option (Opening lam E.Sym)) (rtreq : Dig lam)
    (slot : ℕ) (path : List (Dig lam)) (rsalt : Bits) : F.Prf where
  salt := salt
  roots := k₁.roots ++ (k₂.roots ++ k₃.roots)
  plains := Plains.app (s := G.c₁) (t := G.c₂ ++ G.c₃) k₁.plains
    (Plains.app (s := G.c₂) (t := G.c₃) k₂.plains k₃.plains)
  opens := opensApp (s := G.c₁) (u := G.c₂ ++ G.c₃) k₁.opens
    (opensApp (s := G.c₂) (u := G.c₃) k₂.opens k₃.opens)
  ext := ext
  rtreq := rtreq
  slot := slot
  path := path
  rsalt := rsalt

/-- the openings of a proof string at the first chain's positions -/
def opens₁ (π : F.Prf) : (p : OPos G.c₁) → Option (Opening lam (OSym G.c₁ p)) :=
  opensL (s := G.c₁) (u := G.c₂ ++ G.c₃) π.opens

/-- at the second chain's positions -/
def opens₂ (π : F.Prf) : (p : OPos G.c₂) → Option (Opening lam (OSym G.c₂ p)) :=
  opensL (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) π.opens)

/-- at the third chain's positions -/
def opens₃ (π : F.Prf) : (p : OPos G.c₃) → Option (Opening lam (OSym G.c₃ p)) :=
  opensR (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) π.opens)

section Laws
variable (salt : Bits) (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂) (k₃ : ChainStr lam G.c₃)
  (ext : E.Pos → Option (Opening lam E.Sym)) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam))
  (rsalt : Bits)

theorem assemble_pls₁ :
    pls₁ F.D (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₁.plains :=
  Plains.fst_app (s := G.c₁) (t := G.c₂ ++ G.c₃) _ _

theorem assemble_pls₂ :
    pls₂ F.D (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₂.plains := by
  show Plains.fst (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃)
    (Plains.app (s := G.c₁) (t := G.c₂ ++ G.c₃) k₁.plains
      (Plains.app (s := G.c₂) (t := G.c₃) k₂.plains k₃.plains))) = _
  rw [Plains.snd_app, Plains.fst_app]

theorem assemble_pls₃ :
    pls₃ F.D (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₃.plains := by
  show Plains.snd (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃)
    (Plains.app (s := G.c₁) (t := G.c₂ ++ G.c₃) k₁.plains
      (Plains.app (s := G.c₂) (t := G.c₃) k₂.plains k₃.plains))) = _
  rw [Plains.snd_app, Plains.snd_app]

theorem assemble_opens₁ :
    F.opens₁ (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₁.opens :=
  funext fun p => opensL_app (s := G.c₁) (u := G.c₂ ++ G.c₃) _ _ p

theorem assemble_opens₂ :
    F.opens₂ (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₂.opens := by
  show opensL (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃)
    (opensApp (s := G.c₁) (u := G.c₂ ++ G.c₃) k₁.opens
      (opensApp (s := G.c₂) (u := G.c₃) k₂.opens k₃.opens))) = _
  rw [opensR_app]
  exact funext fun p => opensL_app (s := G.c₂) (u := G.c₃) _ _ p

theorem assemble_opens₃ :
    F.opens₃ (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₃.opens := by
  show opensR (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃)
    (opensApp (s := G.c₁) (u := G.c₂ ++ G.c₃) k₁.opens
      (opensApp (s := G.c₂) (u := G.c₃) k₂.opens k₃.opens))) = _
  rw [opensR_app, opensR_app]

theorem assemble_roots :
    (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt).roots =
      k₁.roots ++ (k₂.roots ++ k₃.roots) := rfl

/-- behind the first chain's roots -/
theorem assemble_drop₁ {n : ℕ} (h : k₁.roots.length = n) :
    (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt).roots.drop n = k₂.roots ++ k₃.roots := by
  subst h
  exact List.drop_left

/-- behind the first and the second chain's roots -/
theorem assemble_drop₂ {n m : ℕ} (h : k₁.roots.length = n) (h' : k₂.roots.length = m) :
    ((F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt).roots.drop n).drop m = k₃.roots := by
  rw [assemble_drop₁ F salt k₁ k₂ k₃ ext rtreq slot path rsalt h]
  subst h'
  exact List.drop_left

end Laws

/-- the first chain's part of a proof string whose first n roots are the first chain's -/
def cut₁ (π : F.Prf) (n : ℕ) : ChainStr lam G.c₁ := ⟨π.roots.take n, pls₁ F.D π, F.opens₁ π⟩

/-- the second chain's part: the m roots behind the first n -/
def cut₂ (π : F.Prf) (n m : ℕ) : ChainStr lam G.c₂ :=
  ⟨(π.roots.drop n).take m, pls₂ F.D π, F.opens₂ π⟩

/-- the third chain's part: the roots behind the first n + m -/
def cut₃ (π : F.Prf) (n m : ℕ) : ChainStr lam G.c₃ :=
  ⟨(π.roots.drop n).drop m, pls₃ F.D π, F.opens₃ π⟩

/-- Each proof string is assembled from its cuts, wherever its list of roots is cut. -/
theorem assemble_cut (π : F.Prf) (n m : ℕ) :
    F.assemble π.salt (F.cut₁ π n) (F.cut₂ π n m) (F.cut₃ π n m) π.ext π.rtreq π.slot π.path
      π.rsalt = π := by
  obtain ⟨salt, roots, plains, opens, ext, rtreq, slot, path, rsalt⟩ := π
  have e1 : roots.take n ++ ((roots.drop n).take m ++ (roots.drop n).drop m) = roots := by
    rw [List.take_append_drop, List.take_append_drop]
  have e2 : Plains.app (s := G.c₁) (t := G.c₂ ++ G.c₃)
      (Plains.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) plains)
      (Plains.app (s := G.c₂) (t := G.c₃)
        (Plains.fst (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) plains))
        (Plains.snd (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) plains))) =
      plains := by
    rw [Plains.app_fst_snd, Plains.app_fst_snd]
  have e3 : opensApp (s := G.c₁) (u := G.c₂ ++ G.c₃)
      (opensL (s := G.c₁) (u := G.c₂ ++ G.c₃) opens)
      (opensApp (s := G.c₂) (u := G.c₃)
        (opensL (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) opens))
        (opensR (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) opens))) =
      opens := by
    have i : opensApp (s := G.c₂) (u := G.c₃)
        (opensL (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) opens))
        (opensR (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) opens)) =
        opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) opens :=
      funext fun p => opensApp_LR (s := G.c₂) (u := G.c₃) _ p
    rw [i]
    exact funext fun p => opensApp_LR (s := G.c₁) (u := G.c₂ ++ G.c₃) _ p
  have key : ∀ a b c, a = roots → b = plains → c = opens →
      (⟨salt, a, b, c, ext, rtreq, slot, path, rsalt⟩ : OneProtocolProof lam F.D.batch) =
        ⟨salt, roots, plains, opens, ext, rtreq, slot, path, rsalt⟩ := by
    rintro _ _ _ rfl rfl rfl
    rfl
  exact key _ _ _ e1 e2 e3

end FileW

end TypedOracleCompiler.Joined
