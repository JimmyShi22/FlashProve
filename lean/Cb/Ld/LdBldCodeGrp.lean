-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldCodeGrp.lean: codes for the proximity test over p = 2^64 - 2^32 + 1: the code of one
oracle message among several that are tested together, also when it is read at long positions that
are not its own.

This file continues the builder of codes (Cb/Ld/LdBldCode.lean): a member of a group (main rows
beside mask rows). A group is a set of oracle messages that are read at common long positions and
tested together.

Definitions, and statements in `Cb.Gl.Bld.Spec`; the proofs are in Cb/Ld/LdBldCodeGrpProofs.lean.
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A code `C : LdCode E P` (Cb/Ld/LdRel.lean) has native positions `C.NP` and is read at long positions
P; `C.atPos pos'` (Cb/Ld/LdSig.lean) reads it at other long positions, through the map pos'. The
three forms of a row (`rsLd`; `cpLd`; for a' ≤ a `repLd`, the native form) and a fold's input code
`inCd` are defined in Cb/Ld/LdBldCode.lean.
`GlC C d t` (Cb/Gl/GlLd.lean) says that C is made by interleaving, pairing and forming families from
plain or copied Reed-Solomon codes on subgroups of order at most 2^32, every position of each read
equally often; d is at most the distance of each as read; for t see that file. `GlJ C d t e bad`
(Cb/Gl/GlLdJ.lean) asks moreover conditions on each of these Reed-Solomon codes at a radius e, and
that bad is at least a sum of bounds that it names (`IsGlJ`, `IsGlS` there; `IsGlCpJ`,
Cb/Gl/GlCopy.lean).

Main names:
  `memCd C Z Rm Rz`: main rows Rm under C beside mask rows Rz under Z.
  `Spec.bld_mem_glC`, `Spec.bld_mem_glJ`: `GlC`, `GlJ` of a member from `GlC`, `GlJ` of C and of Z
    at the same d, t, e (the counts, the last argument of `GlJ`, add).
  `Spec.bld_mem_glC_at`, `Spec.bld_mem_glJ_at`: the same for the member read through a map that
    takes each old position exactly m times, 0 < m: at m d, and m e; the same counts.
  `CovOK C cov`: cov names, for each native position, a long position at which it is read.
  `rsLdCov`, `cpLdCov`, `repLdCov`, `memCov`: such maps for the three forms (the position itself;
    for the native form: the first of its 2^(a - a') long positions) and for a member.
    `Spec.bld_cov_rs` to `Spec.bld_cov_mem` state `CovOK` of them, of `memCov` if it holds of the
    maps of C and Z.
  `Spec.bld_finNS_rs` to `Spec.bld_finNS_mem`: the three forms have `LdCode.FinNS`
    (Cb/Obj/LdObjectCtb.lean: a native symbol has finitely many coordinates), which countability
    asks of a code; so has a member if C and Z have.

Why `CovOK`: the base case of a tower has such a map as a parameter (Cb/Ld/LdBase.lean: "where to
look up a native position that the verifier does not read"). Nothing is asked of it there. It enters
the base case's budget of further reads: a native position may be read further if it is read at the
long position where it is looked up. With a junk map the budget holds of fewer sets of further
reads: zero knowledge of the base case is then a statement on fewer readers: weaker, not wrong.
`CovOK` is "the base case's budget holds of every set of further reads": whoever shows that a given
set of reads is within that budget leans on it.

Limits: no group, no shape, no arrangement is given here. This file says nothing on radii of a
re-read member that are no multiples of m. It does not say that any count is small.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldCode
import Cb.Ld.LdBldCodeAt
import Cb.Obj.LdObjectCtb

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

/-- A member of a group: main rows under C beside mask rows under Z. It is the form that the shape
of a group (`GShape`) needs of a member (its field `view`, Cb/Ld/LdGroupFold.lean).
`inCd C Z kk h` is `memCd` at the two cubes, by definition. -/
@[reducible] def memCd {P : Type} (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm] [DecidableEq Rm]
    [Fintype Rz] [DecidableEq Rz] : LdCode E P :=
  (C.il Rm).pair (Z.il Rz)

/-- cov names, for each native position, a long position at which it is read. -/
def CovOK {P : Type} (C : LdCode E P) (cov : C.NP → P) : Prop := ∀ p, p ∈ C.src (cov p)

section Cov
variable (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R]

def rsLdCov : (rsLd a k msg r R).NP → Fin (2 ^ a) := fun p => p.2
def cpLdCov : (cpLd a' a k msg r R).NP → Fin (2 ^ a) := fun p => p.2
def repLdCov : (repLd a' a k msg r h R).NP → Fin (2 ^ a) := fun p =>
  Fin.castLE (Nat.pow_le_pow_right (by norm_num) h) p.2

end Cov

def memCov {P : Type} (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm] [DecidableEq Rm] [Fintype Rz]
    [DecidableEq Rz] (cC : C.NP → P) (cZ : Z.NP → P) : (memCd C Z Rm Rz).NP → P := Sum.elim cC cZ

namespace Spec

def bld_mem_glC : Prop :=
  ∀ (P : Type) [Fintype P] (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm] [DecidableEq Rm]
      [Fintype Rz] [DecidableEq Rz] (d t : ℕ),
    GlC C d t → GlC Z d t → GlC (memCd C Z Rm Rz) d t

def bld_mem_glJ : Prop :=
  ∀ (P : Type) [Fintype P] (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm] [DecidableEq Rm]
      [Fintype Rz] [DecidableEq Rz] (d t e bC bZ : ℕ),
    GlJ C d t e bC → GlJ Z d t e bZ → GlJ (memCd C Z Rm Rz) d t e (bC + bZ)

def bld_mem_glC_at : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm]
      [DecidableEq Rm] [Fintype Rz] [DecidableEq Rz] (d t : ℕ) (pos' : P' → P) (m : ℕ),
    GlC C d t → GlC Z d t → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) →
    GlC ((memCd C Z Rm Rz).atPos pos') (m * d) t

def bld_mem_glJ_at : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm]
      [DecidableEq Rm] [Fintype Rz] [DecidableEq Rz] (d t e bC bZ : ℕ) (pos' : P' → P) (m : ℕ),
    GlJ C d t e bC → GlJ Z d t e bZ → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) →
    GlJ ((memCd C Z Rm Rz).atPos pos') (m * d) t (m * e) (bC + bZ)

/-- States: for a' ≤ a, the map x ↦ x modulo 2^a' (`cpDn a' a`, Cb/Gl/GlCopy.lean), from 2^a
positions to 2^a', takes each short position exactly 2^(a - a') times, and 0 < 2^(a - a'). -/
def bld_dn_even : Prop :=
  ∀ a' a : ℕ, a' ≤ a →
    0 < 2 ^ (a - a') ∧
    ∀ y : Fin (2 ^ a'), cnt (fun x : Fin (2 ^ a) => cpDn a' a x = y) = 2 ^ (a - a')

/-- States: for a' ≤ a, the native form `repLd a' a k msg r h R` is the short code at its own
length, `rsLd a' k msg r R`, read through `cpDn a' a`. -/
def bld_rep_eq : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R],
    repLd a' a k msg r h R = (rsLd a' k msg r R).atPos (cpDn a' a)

def bld_cov_rs : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R],
    CovOK (rsLd a k msg r R) (rsLdCov a k msg r R)
def bld_cov_cp : Prop :=
  ∀ (a' a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R],
    CovOK (cpLd a' a k msg r R) (cpLdCov a' a k msg r R)
def bld_cov_rep : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R],
    CovOK (repLd a' a k msg r h R) (repLdCov a' a k msg r h R)
def bld_cov_mem : Prop :=
  ∀ (P : Type) (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm] [DecidableEq Rm] [Fintype Rz]
      [DecidableEq Rz] (cC : C.NP → P) (cZ : Z.NP → P),
    CovOK C cC → CovOK Z cZ → CovOK (memCd C Z Rm Rz) (memCov C Z Rm Rz cC cZ)

def bld_finNS_rs : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R], (rsLd a k msg r R).FinNS
def bld_finNS_cp : Prop :=
  ∀ (a' a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R], (cpLd a' a k msg r R).FinNS
def bld_finNS_rep : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R],
    (repLd a' a k msg r h R).FinNS
def bld_finNS_mem : Prop :=
  ∀ (P : Type) (C Z : LdCode E P) (Rm Rz : Type) [Fintype Rm] [DecidableEq Rm]
      [Fintype Rz] [DecidableEq Rz],
    C.FinNS → Z.FinNS → (memCd C Z Rm Rz).FinNS

end Spec
end Cb.Gl.Bld
