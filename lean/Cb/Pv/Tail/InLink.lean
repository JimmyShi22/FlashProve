-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/InLink.lean: the smallness test's round as a block of a link: what a frame with two
sendings asks of the block behind the first sending, paid from Cb/Pv/Tail/Know.lean and
Cb/Pv/Tail/CellMap.lean.

A link's frame takes, for the block behind the sending of the reads: its `KnowAt` between two
joints on one type of cores; and a seam: the joint in front of the block gives the base joint in
front of the sending, the agreement of the late entries with their forms in the early entries
(`Cb.Sub.Agree`, Cb/Sub/Late.lean), and the ledger on early and late entries.

Main names:
  `reCore`, `knowAt_reCore`: a joint with another core; `KnowAt` reads no core.
  `symL`, `cellValS`, `cellVal_eq`: the cells as a function of the symbols alone: whatever part of
    the messages holds the symbols, the cells are read off that part.
  `agree_in`: before the round the late entries agree with their forms, under three laws on the
    frame's letters: the early entry at the place of a cell is that cell (`hc`); the form of a late
    entry is the form of its read, on the cells' places (`ha`); a late entry is the committed read
    at its place (`ht`).
  `Host`: the frame's letters. `Host.let`: the letters of Cb/Pv/Tail/Block.lean at them: what rides
    is the base joint in front of the sending and the ledger on early and late entries.
  `host_know`: the block's `KnowAt` at these letters, with the frame's cores.
  `host_seam`: the seam.

Limits: the three laws are premises: no frame is shown to meet them. The messages of `Host` are
those that stand when the matrix is drawn: the early ones and the reads; see the Limits of
Cb/Pv/Tail/Block.lean on what may not be among them.

Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.Late
import Cb.Pv.Tail.CellMap
import Cb.Pv.Tail.Know

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop TWhole

/-! ## Another core -/

/-- The joint A with the core c. -/
def reCore {K K' X W : Type} {Ex : ExtSpec} (A : IOR.Rels K X Ex W) (c : W → K') :
    IOR.Rels K' X Ex W := ⟨A.rel, A.relR, A.on, c⟩

theorem knowAt_reCore {K K' M Xi Xo Wi Wo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape} (h : KnowAt R A B ext ε)
    (c : M × Wi → K') (c' : M × Wo → K') : KnowAt R (reCore A c) (reCore B c') ext ε :=
  ⟨h.point, h.isLocal, h.onOut, h.know⟩

variable {K : Type} [Field K] {s : Size}

/-! ## The cells as a function of the symbols -/

/-- The symbols of all matrices. -/
abbrev Syms (K : Type) (s : Size) : Type :=
  ∀ μ : Fin s.NM, Fin (Alg.symRows (s.m μ)) → Fin (s.k μ) → K

/-- Letters whose messages are the symbols themselves. -/
def symL (K : Type) [Field K] (s : Size) : Letters K s where
  X := Unit
  M := Syms K s
  E := ⟨Unit, Empty, Unit, fun _ e => e.elim⟩
  W := Dig K s
  w := fun _ _ _ _ => 0
  sym := fun y => y
  tab := fun _ _ _ _ => 0
  dig := fun Z => Z
  ride := fun _ _ _ => True

/-- The cells behind given symbols, as elements of the field. -/
noncomputable def cellValS (y : Syms K s) : JCell s → K := cellVal (symL K s) y

theorem cellVal_eq (Λ : Letters K s) (msg : Λ.M) : cellVal Λ msg = cellValS (Λ.sym msg) := rfl

/-! ## Agreement -/

theorem agree_in (Λ : Letters K s) (p : ℕ) [CharP K p] (hu : s.Uniq p) {J₁ J₂ : Type}
    [Fintype J₁] [Fintype J₂] (a : Λ.X → J₂ → Aff K J₁) (m₁ : Λ.M → J₁ → K) (u : Λ.M → J₂ → K)
    (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hc : ∀ msg j, m₁ msg (ic j) = cellValS (Λ.sym msg) j)
    (ha : ∀ x j v, (a x j).val v = (affRead Λ x (it j)).val fun i => v (ic i))
    (ht : ∀ msg j, u msg j = Λ.tab msg (it j).1 (it j).2.1 (it j).2.2)
    {x : Λ.X} {msg : Λ.M} (h : relIn Λ x msg) : Cb.Sub.Agree (a x) (m₁ msg) (u msg) := by
  intro j
  rw [ha, ht, agree_cellVal Λ p hu h (it j), cellVal_eq]
  congr 1
  funext i
  exact (hc msg i).symm

/-! ## The frame's letters -/

/-- What a frame with a sending in front of the block brings. -/
structure Host (K : Type) (s : Size) (J₁ J₂ : Type) where
  /-- the statement in front, without the ledger; the implicit instance -/
  Xe : Type
  Ex : ExtSpec
  /-- the messages when the matrix is drawn; the early ones; the late ones -/
  M : Type
  M₁ : Type
  U₁ : Type
  left : M → M₁
  right : M → U₁
  /-- the further witness in front of the sending and behind it; the cores -/
  Wp : Type
  Wp₁ : Type
  Kc : Type
  bk₁ : U₁ → Wp₁ → Wp
  /-- the base joint in front of the sending -/
  B₀ : IOR.Rels Kc Xe Ex (M₁ × Wp)
  /-- the early and the late entries -/
  msg₁ : M₁ → J₁ → K
  ent : U₁ → J₂ → K
  /-- the weights of the reads, the symbols, the reads, the digits -/
  w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → K
  sym : M₁ → Syms K s
  tab : U₁ → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → K
  dig : Wp₁ → Dig K s

variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]

namespace Host
variable (Q : Host K s J₁ J₂)

/-- The letters of Cb/Pv/Tail/Block.lean. What rides: the base joint in front of the sending, and
the ledger on early and late entries. -/
def «let» : Letters K s where
  X := Q.Xe × Ledger K (J₁ ⊕ J₂)
  M := Q.M
  E := Q.Ex
  W := Q.Wp₁
  w := fun x => Q.w x.1
  sym := fun m => Q.sym (Q.left m)
  tab := fun m => Q.tab (Q.right m)
  dig := Q.dig
  ride := fun b m w' =>
    Q.B₀.relR (b.1.1, b.2) (Q.left m, Q.bk₁ (Q.right m) w') ∧
      Ledger.Holds b.1.2 (Sum.elim (Q.msg₁ (Q.left m)) (Q.ent (Q.right m)))

end Host

variable (Q : Host K s J₁ J₂)

/-- The block's soundness property at the frame's letters, with the frame's cores. -/
theorem host_know (hs : s.OK) (c c' : Q.M × Q.Wp₁ → Q.Kc) :
    KnowAt (R Q.let) (reCore (A Q.let) c) (reCore (B Q.let) c') Cb.Sub.idW (eps Q.let) :=
  knowAt_reCore (knowAt Q.let hs) c c'

/-- The seam in front of the block. -/
theorem host_seam (p : ℕ) [CharP K p] (hu : s.Uniq p) (a : Q.Xe → J₂ → Aff K J₁)
    (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hc : ∀ m₁ j, Q.msg₁ m₁ (ic j) = cellValS (Q.sym m₁) j)
    (ha : ∀ (x : Q.let.X) j v,
      (a x.1 j).val v = (affRead Q.let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, Q.ent u j = Q.tab u (it j).1 (it j).2.1 (it j).2.2)
    (c : Q.M × Q.Wp₁ → Q.Kc) :
    ∀ b m w', (reCore (A Q.let) c).relR b (m, w') →
      Q.B₀.relR (b.1.1, b.2) (Q.left m, Q.bk₁ (Q.right m) w') ∧
        Cb.Sub.Agree (a b.1.1) (Q.msg₁ (Q.left m)) (Q.ent (Q.right m)) ∧
        Ledger.Holds b.1.2 (Sum.elim (Q.msg₁ (Q.left m)) (Q.ent (Q.right m))) := by
  rintro b m w' ⟨⟨h1, h2⟩, h3⟩
  exact ⟨h1, agree_in Q.let p hu (fun x => a x.1) (fun m => Q.msg₁ (Q.left m))
    (fun m => Q.ent (Q.right m)) ic it (fun msg j => hc (Q.left msg) j) ha
    (fun msg j => ht (Q.right msg) j) h3, h2⟩

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.knowAt_reCore
#print axioms Cb.Pv.Tail.agree_in
#print axioms Cb.Pv.Tail.host_know
#print axioms Cb.Pv.Tail.host_seam
