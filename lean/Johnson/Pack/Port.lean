-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/Port.lean: the code and the oracle message of a shape of the programs, as objects of
the library, with laws and distance.

Definitions, statements and proofs. The verifier that is written after the programs (OnBytes/)
describes an oracle message by a record, `OnBytes.OracleShape`: main rows under one code, all over
the base field or all over the extension field, and mask rows under a second code, over the
extension field. OnBytes/Slice/ has one row under a code of the programs as a code of the library,
in two forms (OnBytes/Slice/LinkAt.lean: the programs' points; the tail's coefficients before the
message's), each with its laws and its distance (OnBytes/Slice/LdOfFacts.lean): `ldOf`, whose words
stand on the code's own positions and are read modulo its length, and `ldRep`, whose words have a
symbol at each position at which they are read. This file sets the rows of both tables side by side,
for every shape. The library's own builders of oracle messages are not used: they fix one field, one
stage and one layout for all rows.
Main names:
  `ldOf_dist_at`: one row under C, read at 2^a ≥ 2^C.a positions, has the distance 2^(a - C.a)
    (2^C.a - (r + l) + 1).
  `portCode cs s`: the code of the shape s under the codes cs: `((ldOf main a).il rows).pair ((ldRep
    mask a).il rows')`, a the larger of the two logarithms of length. The mask rows take `ldRep`: by
    the verifier's text (`TreeShape`, `columnOf`, OnBytes/Iop/Ground.lean) the leaf of the position
    x holds the main rows' symbols at x and a copy of the mask rows' symbols at x modulo their
    length, and an opened column is read as it stands; so what a file can hold is a word on all 2^a
    positions.
  `CodeOK cs s`: for both codes: logN ≤ 32 and r + ell ≤ 2^logN.
  `port_laws`, `port_dist`: under `CodeOK`: the laws; the distance d, for every d that is at most
    the distance as read of each table that has a row.
  `portOm`: the oracle message: main rows are sent over the base field if mainDeg = 1, mask rows
    over the extension field.
  `port_half`, `port_john`: it is within unique decoding (`OMsg.Half`), or below the Johnson radius
    (`OMsg.John`), from conditions on numbers and, for the second, a sample map that is a
    zero-evader.
  `port_J`, `port_Q`: it has mainRows ell + maskRows ell' entries and mainRows r + maskRows r' tail
    entries.
  `PSend`, `PSend.sig`, `PSend.Meets`, `port_holes`: the shapes of one sending as a signature;
    lists, evasion and laws of its members (Johnson/Pack/Floor.lean).
Limits: the main rows take `ldOf`: that is the word of the tree only where the main code has the
length 2^a. A shape with rows of both tables whose mask code is the longer would have its main rows'
word on fewer positions than the tree; by its text the verifier's book of trees refuses such a tree
(OnBytes/Iop/Ground.lean: logNzk ≤ logN); no lemma here says so. Several oracle messages of one
prover's message may share a tree; a tree that is shorter than the list of positions of a test is
opened at the position modulo its length: neither is spoken of here (the second:
Johnson/Pack/Group.lean). Codes of at most 2^32 positions (beyond that the programs' points lie on
several cosets, and OnBytes/Slice/ claims nothing). The sample map, the order of pairs, the seeds
and the radii are parameters here; that a sample map is the programs' is not said;
Johnson/Pack/PortZ.lean defines one. A message that is over the base field whole:
Johnson/Pack/PortF.lean. A message's entries are elements of the extension field by the type
`OMsg.Msg`; the format binds the word that is sent, not the message. No list of the programs' shapes
stands in this file. Nothing on leaf classes, on the honest prover, or on hiding.
-/
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.MembFacts
import Johnson.Pack.Floor
import Johnson.Pack.Lay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

/-- One row under C, read at 2^a ≥ 2^C.a positions: the distance as read. -/
theorem ldOf_dist_at (C : Fmt.M1.Code) (a : ℕ) (hle : C.a ≤ a) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldOf C a).Dist (2 ^ (a - C.a) * (2 ^ C.a - (C.r + C.l) + 1)) := by
  intro m r hmr
  have key : ∀ x : Fin (2 ^ a), (ldOf C C.a).T ((ldOf C C.a).enc m r) (posIn C x) ≠ 0 →
      (ldOf C a).T ((ldOf C a).enc m r) x ≠ 0 := by
    intro x hx h
    refine hx (funext fun s => ?_)
    have h1 : (ldOf C a).enc m r (posIn C x) () = 0 := congrFun h ()
    show (ldOf C C.a).enc m r (posIn C (posIn C x)) () = 0
    rw [posIn_self]
    exact h1
  refine (Nat.mul_le_mul_left _ (ldOf_dist C ha hk m r hmr)).trans (le_trans (le_of_eq ?_)
    (cnt_mono key))
  exact (CodeRep.cnt_comp_even (posIn C) (2 ^ (a - C.a)) (cnt_posIn C hle)
    fun y => (ldOf C C.a).T ((ldOf C C.a).enc m r) y ≠ 0).symm

theorem dist_mono {E P : Type} [Field E] [Finite P] (C : LdCode E P) {d d' : ℕ} (h : d ≤ d')
    (hD : C.Dist d') : C.Dist d := fun m r hmr => h.trans (hD m r hmr)

/-- An interleaving with no row has every distance. -/
theorem il_fin0_dist {E P : Type} [Field E] [Finite P] (C : LdCode E P) {n : ℕ} (h : n = 0)
    (d : ℕ) : (C.il (Fin n)).Dist d := by
  subst h
  exact fun _ _ hne => absurd ⟨funext fun j => j.1.elim0, funext fun q => q.1.elim0⟩ hne

/-! ### The code of a shape -/

/-- The code of a shape's main rows, and that of its mask rows. -/
def pMain (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : OnBytes.Code :=
  cs.base.getD s.code default
def pMask (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : OnBytes.Code :=
  cs.mask.getD s.maskCode default

abbrev cMain (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : Fmt.M1.Code := codeOf (pMain cs s)
abbrev cMask (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : Fmt.M1.Code := codeOf (pMask cs s)

/-- The logarithm of the number of long positions. -/
def aOf (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : ℕ := max (cMain cs s).a (cMask cs s).a

/-- The code of a shape: its main rows beside its mask rows. A word of mask rows has a symbol at
each of the 2^a positions: in the programs' tree the leaf of the position x holds, after the main
rows' symbols at x, a copy of the mask rows' symbols at x modulo their length. A word that is no
code word may have different symbols at two positions that are equal modulo that length. -/
abbrev portCode (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : LdCode GE (Fin (2 ^ aOf cs s)) :=
  ((ldOf (cMain cs s) (aOf cs s)).il (Fin s.mainRows)).pair
    ((ldRep (cMask cs s) (aOf cs s)).il (Fin s.maskRows))

/-- Two conditions on numbers, for each of the two codes. -/
structure CodeOK (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : Prop where
  a1 : (cMain cs s).a ≤ 32
  k1 : (cMain cs s).r + (cMain cs s).l ≤ 2 ^ (cMain cs s).a
  a2 : (cMask cs s).a ≤ 32
  k2 : (cMask cs s).r + (cMask cs s).l ≤ 2 ^ (cMask cs s).a

/-- A code's distance as read at 2^a positions. -/
def distAt (C : Fmt.M1.Code) (a : ℕ) : ℕ := 2 ^ (a - C.a) * (2 ^ C.a - (C.r + C.l) + 1)

theorem port_laws (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (h : CodeOK cs s) :
    (portCode cs s).Laws :=
  ld_laws_pair GE _ _ _
    (ld_laws_il GE _ _ (Fin s.mainRows) (ldOf_laws (cMain cs s) (aOf cs s) h.a1 h.k1))
    (ld_laws_il GE _ _ (Fin s.maskRows)
      (ldRep_laws (cMask cs s) (aOf cs s) (le_max_right _ _) h.a2 h.k2))

theorem port_dist (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (h : CodeOK cs s) (d : ℕ)
    (h1 : s.mainRows = 0 ∨ d ≤ distAt (cMain cs s) (aOf cs s))
    (h2 : s.maskRows = 0 ∨ d ≤ distAt (cMask cs s) (aOf cs s)) : (portCode cs s).Dist d :=
  ld_dist_pair GE _ _ _ d
    (h1.elim (fun z => il_fin0_dist _ z d) fun g =>
      ld_dist_il GE _ _ (Fin s.mainRows) d
        (dist_mono _ g (ldOf_dist_at (cMain cs s) (aOf cs s) (le_max_left _ _) h.a1 h.k1)))
    (h2.elim (fun z => il_fin0_dist _ z d) fun g =>
      ld_dist_il GE _ _ (Fin s.maskRows) d
        (dist_mono _ g (ldRep_dist (cMask cs s) (aOf cs s) (le_max_right _ _) h.a2 h.k2)))

theorem port_J (cs : OnBytes.Codes) (s : OnBytes.OracleShape) :
    Fintype.card (portCode cs s).J =
      s.mainRows * (pMain cs s).ell + s.maskRows * (pMask cs s).ell := by
  show Fintype.card ((Fin s.mainRows × Fin (pMain cs s).ell) ⊕
    (Fin s.maskRows × Fin (pMask cs s).ell)) = _
  simp

theorem port_Q (cs : OnBytes.Codes) (s : OnBytes.OracleShape) :
    Fintype.card (portCode cs s).Q = s.mainRows * (pMain cs s).r + s.maskRows * (pMask cs s).r := by
  show Fintype.card ((Fin s.mainRows × Fin (pMain cs s).r) ⊕
    (Fin s.maskRows × Fin (pMask cs s).r)) = _
  simp

/-- Is the table of a native position sent over the base field. -/
def tabF (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : (portCode cs s).NP → Bool
  | .inl _ => s.mainDeg == 1
  | .inr _ => false

/-- The oracle message of a shape. e: the radius. The sample map and the order are parameters. -/
noncomputable def portOm (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)
    (Z : Sample GE (portCode cs s).J)
    (rank : ((portCode cs s).J → GE) × ((portCode cs s).Q → GE) → ℕ) : OMsg GE where
  P := Fin (2 ^ aOf cs s)
  C := portCode cs s
  Z := Z
  e := e
  rank := rank
  Sy := fun p => (portCode cs s).NS p → RowTy (tabF cs s p)
  up := fun p f x => upRow (tabF cs s p) (f x)
  sy0 := fun p _ => row0 (tabF cs s p)

/-- What laws and distance ask, on numbers alone. -/
structure PBase (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (d : ℕ) : Prop where
  ok : CodeOK cs s
  d1 : s.mainRows = 0 ∨ d ≤ distAt (cMain cs s) (aOf cs s)
  d2 : s.maskRows = 0 ∨ d ≤ distAt (cMask cs s) (aOf cs s)

theorem port_half (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)
    (Z : Sample GE (portCode cs s).J)
    (rank : ((portCode cs s).J → GE) × ((portCode cs s).Q → GE) → ℕ) (d : ℕ)
    (g : PBase cs s d) (h : 2 * e < d) : (portOm cs s e Z rank).Half d 1 :=
  ⟨port_laws cs s g.ok, port_dist cs s g.ok d g.d1 g.d2, h, rfl⟩

theorem port_john (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)
    (Z : Sample GE (portCode cs s).J)
    (rank : ((portCode cs s).J → GE) × ((portCode cs s).Q → GE) → ℕ) (d L : ℕ)
    (g : PBase cs s d)
    (hJ : InJohnson (Fintype.card (Fin (2 ^ aOf cs s))) d e)
    (hL : L = listMax (Fintype.card (Fin (2 ^ aOf cs s))) d e) (hZ : Z.OK) :
    (portOm cs s e Z rank).John d L :=
  ⟨port_laws cs s g.ok, port_dist cs s g.ok d g.d1 g.d2, hJ, hL, hZ⟩

/-! ### One sending -/

/-- The shapes of one sending, each with its radius, sample map and order. -/
structure PSend (cs : OnBytes.Codes) where
  n : ℕ
  shape : Fin n → OnBytes.OracleShape
  e : Fin n → ℕ
  Z : ∀ i, Sample GE (portCode cs (shape i)).J
  rank : ∀ i, ((portCode cs (shape i)).J → GE) × ((portCode cs (shape i)).Q → GE) → ℕ
  ans : ∀ i, Fintype.card (Z i).S = (shape i).answers

/-- The signature of a sending. -/
noncomputable def PSend.sig {cs : OnBytes.Codes} (L : PSend cs) : Sig GE where
  O := Fin L.n
  om := fun i => portOm cs (L.shape i) (L.e i) (L.Z i) (L.rank i)

/-- Of each message: within unique decoding, or below the Johnson radius with a zero-evader. -/
def PSend.Meets {cs : OnBytes.Codes} (L : PSend cs) (d Ls : Fin L.n → ℕ) : Prop :=
  ∀ i, PBase cs (L.shape i) (d i) ∧
    ((2 * L.e i < d i ∧ Ls i = 1) ∨
      (InJohnson (Fintype.card (Fin (2 ^ aOf cs (L.shape i)))) (d i) (L.e i) ∧
        Ls i = listMax (Fintype.card (Fin (2 ^ aOf cs (L.shape i)))) (d i) (L.e i) ∧ (L.Z i).OK))

theorem port_holes {cs : OnBytes.Codes} (L : PSend cs) (d Ls : Fin L.n → ℕ) (g : L.Meets d Ls) :
    Cb.Pack.HList L.sig Ls ∧ Cb.Pack.HEvades L.sig ∧ Cb.Pack.HLaws L.sig :=
  Cb.Pack.holes_of_members GF L.sig d Ls fun i =>
    (g i).2.elim
      (fun h => Or.inl (Or.inl (by
        rw [h.2]
        exact port_half cs (L.shape i) (L.e i) (L.Z i) (L.rank i) (d i) (g i).1 h.1)))
      fun h => Or.inl (Or.inr
        (port_john cs (L.shape i) (L.e i) (L.Z i) (L.rank i) (d i) (Ls i) (g i).1 h.1 h.2.1 h.2.2))

end Johnson.Pack

#print axioms Johnson.Pack.ldOf_dist_at
#print axioms Johnson.Pack.port_laws
#print axioms Johnson.Pack.port_dist
#print axioms Johnson.Pack.port_J
#print axioms Johnson.Pack.port_john
#print axioms Johnson.Pack.PSend.sig
#print axioms Johnson.Pack.port_holes
