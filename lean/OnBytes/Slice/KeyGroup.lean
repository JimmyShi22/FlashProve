-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyGroup.lean: a group of sent messages at the first stage of a proximity test.

A proximity test (OnBytes/Slice/Stage.lean) begins with a claim on the tables of its first stage:
main rows on a cube beside carried mask rows on a smaller cube, all read at the positions of one
range. In a key's chains these rows were sent earlier, in several prover messages, each under a tree
of its own, and a tree may be shorter than the range. This file says how sent messages sit in a
stage, with no reference to a protocol.

A sent message has a format of its own (Mb): the code of a main row, the code of a mask row, the
depth of its tree, the numbers of its main and mask rows, and ONE radius, counted in positions of
its own tree. The radius belongs to the message and not to a test, so that a message that two tests
read has one decoding (Mb.fix): the message some encoding of which is within the radius of the sent
word, and nothing if there is none. Below half the distance there is at most one (Mb.fix_eq).

A seat (Site) places the rows of a message among the rows of a stage. The places are maps into the
two cubes. No order of bits is fixed here. A group (Gp) is a finite family of messages with seats in
one stage. Gp.Tie says when a word on the stage's tables is what was sent: a member's main rows at
their places, its mask rows at their places and read at the position modulo the length of the
member's tree, and 0 on every row that no member has. Gp.word is such a word (Gp.tie_word).

Main definitions: Mb, Mb.cd, Mb.word, Mb.IsDec, Mb.fix, Mb.Uniq, Site, Site.atJ, Site.atQ, Site.Tie,
Gp, Gp.Tie, Gp.Apart, Gp.word, symW, symF, Lay, Mb.ofOrc, frOf, Gp.one, Gp.two, Gp.three.

Main theorems: Mb.fix_eq, Mb.fix_none, Mb.fix_some, Mb.fit_cd, Mb.uniq_of, Site.share, Site.fixed,
Site.one_message, Gp.tie_word.

Not claimed. Nothing on which places or which words of a column a given verifier uses. Nothing
beyond half the distance of a message's code.

-/
import OnBytes.Slice.Stage
import OnBytes.Slice.Numbers

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## A sent message -/

/-- The format of a sent message. C: the code of a main row. Z: the code of a mask row. a: the depth
of the message's tree. nM, nZ: the numbers of main and mask rows. e: the message's radius, a count
of positions of its own tree. -/
structure Mb where
  C : Fmt.M1.Code
  Z : Fmt.M1.Code
  a : ℕ
  nM : ℕ
  nZ : ℕ
  e : ℕ

namespace Mb
variable (M : Mb)

/-- the positions of the message's tree -/
abbrev Ps : Type := Fin (2 ^ M.a)

/-- The message's code: its main rows beside its mask rows, the mask code repeated to the tree's
length. -/
abbrev cd : LdCode GE M.Ps :=
  ((ldOf M.C M.a).il (Fin M.nM)).pair ((ldRep M.Z M.a).il (Fin M.nZ))

/-- A word of the message's code from two readers: cm x i is the symbol of main row i at the
position x, cz x i that of mask row i. -/
def word (cm cz : ℕ → ℕ → GE) : M.cd.Word := fun p =>
  match p with
  | .inl x => fun r => cm x.val r.1.val
  | .inr x => fun r => cz x.val r.1.val

/-- Some encoding of m is within the message's radius of the word y. -/
def IsDec (y : M.cd.Word) (m : M.cd.J → GE) : Prop := ∃ r, M.cd.Near M.e y (M.cd.enc m r)

open Classical in
/-- **The decoding of a sent word**: a message some encoding of which is within the radius, and
nothing if there is none. -/
noncomputable def fix (y : M.cd.Word) : Option (M.cd.J → GE) :=
  if h : ∃ m, M.IsDec y m then some h.choose else none

/-- The radius is below half the number d, and the message's code has the laws and the distance
d. -/
structure Uniq (d : ℕ) : Prop where
  fit : Fit M.cd d
  half : 2 * M.e < d

variable {M}

/-- What the decoding returns is within the radius. -/
theorem fix_some {y : M.cd.Word} {m : M.cd.J → GE} (h : M.fix y = some m) : M.IsDec y m := by
  unfold fix at h
  split at h
  · next hex =>
    obtain rfl := Option.some.inj h
    exact hex.choose_spec
  · cases h

/-- If the decoding returns nothing, nothing is within the radius. -/
theorem fix_none {y : M.cd.Word} (h : M.fix y = none) (m : M.cd.J → GE) : ¬ M.IsDec y m := by
  intro hm
  unfold fix at h
  rw [dif_pos ⟨m, hm⟩] at h
  cases h

/-- Below half the distance two messages within the radius of one word are equal. -/
theorem isDec_unique {d : ℕ} (hU : M.Uniq d) {y : M.cd.Word} {m m' : M.cd.J → GE}
    (h : M.IsDec y m) (h' : M.IsDec y m') : m = m' := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨r', hr'⟩ := h'
  have hL := hU.fit.list hU.half y
  have hs : Subsingleton
      {w : (M.cd.J → GE) × (M.cd.Q → GE) // M.cd.Near M.e y (M.cd.enc w.1 w.2)} :=
    (Finite.card_le_one_iff_subsingleton).1 hL
  have := congrArg Subtype.val (hs.elim ⟨(m, r), hr⟩ ⟨(m', r'), hr'⟩)
  exact congrArg Prod.fst this

/-- **Below half the distance the decoding is the one message within the radius.** -/
theorem fix_eq {d : ℕ} (hU : M.Uniq d) {y : M.cd.Word} {m : M.cd.J → GE} (h : M.IsDec y m) :
    M.fix y = some m := by
  cases hf : M.fix y with
  | none => exact absurd h (fix_none hf m)
  | some m' => rw [isDec_unique hU (fix_some hf) h]

end Mb

/-! ## The distance of a message's code -/

/-- A table without rows has the laws and every distance. -/
theorem fit_il_empty {E P : Type} [Field E] [Fintype P] (C : LdCode E P) (R : Type) [Fintype R]
    [DecidableEq R] [IsEmpty R] (d : ℕ) : Fit (C.il R) d where
  laws :=
    { encLin := ⟨fun _ _ => funext fun _ => funext fun s => isEmptyElim s.1,
        fun _ _ => funext fun _ => funext fun s => isEmptyElim s.1⟩
      tLin := ⟨fun _ _ => funext fun _ => funext fun α => isEmptyElim α.1,
        fun _ _ => funext fun _ => funext fun α => isEmptyElim α.1⟩
      inj := fun _ _ _ => ⟨funext fun j => isEmptyElim j.1, funext fun q => isEmptyElim q.1⟩
      loc := fun _ _ _ _ => funext fun α => isEmptyElim α.1 }
  dist := fun _ _ h => absurd ⟨funext fun j => isEmptyElim j.1, funext fun q => isEmptyElim q.1⟩ h

namespace Mb
variable (M : Mb)

/-- What is asked of a message's sizes, for each kind of row that it has. A main row is as long as
the tree, its points are different and it has no more coefficients than positions. A mask row is not
longer than the tree, and the same holds of it. -/
structure Sized : Prop where
  main : 0 < M.nM → M.C.a = M.a ∧ M.a ≤ 32 ∧ M.C.r + M.C.l ≤ 2 ^ M.a
  mask : 0 < M.nZ → M.Z.a ≤ M.a ∧ M.Z.a ≤ 32 ∧ M.Z.r + M.Z.l ≤ 2 ^ M.Z.a

/-- The distance of a main row. -/
def dM : ℕ := 2 ^ M.a - (M.C.r + M.C.l) + 1

/-- The distance of a mask row, repeated to the tree's length. -/
def dZ : ℕ := 2 ^ (M.a - M.Z.a) * (2 ^ M.Z.a - (M.Z.r + M.Z.l) + 1)

variable {M}

/-- **The message's code has the laws and the distance d**, if d is at most the distance of each
kind of row that the message has. -/
theorem fit_cd (h : M.Sized) {d : ℕ} (hM : 0 < M.nM → d ≤ M.dM) (hZ : 0 < M.nZ → d ≤ M.dZ) :
    Fit M.cd d := by
  have h1 : Fit ((ldOf M.C M.a).il (Fin M.nM)) d := by
    rcases Nat.eq_zero_or_pos M.nM with h0 | h0
    · haveI : IsEmpty (Fin M.nM) := by rw [h0]; infer_instance
      exact fit_il_empty _ _ d
    · obtain ⟨ha, h32, hk⟩ := h.main h0
      exact ((fit_ldOf M.C M.a ha h32 hk).mono (hM h0)).il _
  have h2 : Fit ((ldRep M.Z M.a).il (Fin M.nZ)) d := by
    rcases Nat.eq_zero_or_pos M.nZ with h0 | h0
    · haveI : IsEmpty (Fin M.nZ) := by rw [h0]; infer_instance
      exact fit_il_empty _ _ d
    · obtain ⟨ha, h32, hk⟩ := h.mask h0
      exact ((fit_ldRep M.Z M.a ha h32 hk).mono (hZ h0)).il _
  exact h1.pair h2

/-- Unique decoding from the sizes: twice the radius is below the distance of each kind of row that
the message has. -/
theorem uniq_of (h : M.Sized) (hM : 0 < M.nM → 2 * M.e < M.dM) (hZ : 0 < M.nZ → 2 * M.e < M.dZ) :
    M.Uniq (2 * M.e + 1) :=
  ⟨fit_cd h hM hZ, Nat.lt_succ_self _⟩

end Mb

/-! ## A message's seat in a stage -/

/-- **A seat**: how the rows of the message M sit among the rows of the stage s. pM, pZ: the places
of its main and mask rows. The message's tree is not longer than the stage's range. If the message
has a main row, its main code is the stage's and its tree is as long as the range. If it has a mask
row, its mask code is the stage's and is not longer than its tree. Nothing is asked of the code of a
kind of row that the message does not have, so a message may have seats in stages with different
codes. -/
structure Site (s : Sg) (M : Mb) where
  pM : Fin M.nM → Fin (s.h + s.g) → Bool
  pZ : Fin M.nZ → Fin s.h → Bool
  ha : M.a ≤ s.C.a
  hC : Fin M.nM → M.C = s.C
  hM : Fin M.nM → M.a = s.C.a
  hZ : Fin M.nZ → M.Z = s.Z
  hz : Fin M.nZ → M.Z.a ≤ M.a

namespace Site
variable {s : Sg} {M : Mb} (σ : Site s M)

/-- An entry of the message, as an entry of the message on the stage's tables. -/
def atJ : M.cd.J → s.cIn.J
  | .inl x => .inl (σ.pM x.1, Fin.cast (congrArg Fmt.M1.Code.l (σ.hC x.1)) x.2)
  | .inr x => .inr (σ.pZ x.1, Fin.cast (congrArg Fmt.M1.Code.l (σ.hZ x.1)) x.2)

/-- An entry of the message's tails, as an entry of the tails on the stage's tables. -/
def atQ : M.cd.Q → s.cIn.Q
  | .inl x => .inl (σ.pM x.1, Fin.cast (congrArg Fmt.M1.Code.r (σ.hC x.1)) x.2)
  | .inr x => .inr (σ.pZ x.1, Fin.cast (congrArg Fmt.M1.Code.r (σ.hZ x.1)) x.2)

/-- A position of the stage's range, as a position of the message's tree: modulo its length. -/
def red (M : Mb) (x : s.Ps) : M.Ps := ⟨x.val % 2 ^ M.a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- **The word f on the stage's tables holds the sent word y at the seat's rows.** A main row is
read at the position itself. A mask row is read at the position modulo the length of the message's
tree. -/
structure Tie (y : M.cd.Word) (f : s.cIn.Word) : Prop where
  main : ∀ (x : Fin (2 ^ s.C.a)) (r : Fin M.nM), f (.inl x) (σ.pM r, ()) =
    y (.inl (Fin.cast (congrArg (fun C : Fmt.M1.Code => 2 ^ C.a) (σ.hC r).symm) x)) (r, ())
  mask : ∀ (x : Fin (2 ^ s.C.a)) (r : Fin M.nZ),
    f (.inr x) (σ.pZ r, ()) = y (.inr (red M x)) (r, ())

/-- As many positions of the range go to each position of the message's tree. -/
theorem cnt_red (ha : M.a ≤ s.C.a) (y : M.Ps) :
    cnt (fun x : s.Ps => red M x = y) = 2 ^ (s.C.a - M.a) := by
  rw [cnt_congr (fun x : s.Ps => (Fin.ext_iff : red M x = y ↔ _)), ← Nat.pow_div ha (by decide)]
  exact CodeRep.cnt_mod (Nat.pow_dvd_pow 2 ha) y

/-- Where the stage's word and an encoding on the stage's tables have the same symbol, the sent word
and the encoding of the seat's share have the same symbol at the position of the message's tree. -/
theorem agree {y : M.cd.Word} {f : s.cIn.Word} (hT : σ.Tie y f) (w : s.cIn.N.Wit) (x : s.Ps)
    (heq : s.cIn.T f x = s.cIn.T (s.cIn.enc w.1 w.2) x) :
    M.cd.T y (red M x) =
      M.cd.T (M.cd.enc (fun j => w.1 (σ.atJ j)) fun q => w.2 (σ.atQ q)) (red M x) := by
  obtain ⟨C, Z, a, nM, nZ, e0⟩ := M
  obtain ⟨pM, pZ, ha, hC, hM, hZ, hz⟩ := σ
  dsimp only at ha hC hM hZ hz
  funext α
  rcases α with ⟨r, ⟨⟩⟩ | ⟨r, ⟨⟩⟩
  · have h1 := hC r
    have h2 := hM r
    subst h1 h2
    have hr : red (s := s) ⟨s.C, Z, s.C.a, nM, nZ, e0⟩ x = x :=
      Fin.ext (Nat.mod_eq_of_lt x.isLt)
    rw [hr]
    exact (hT.main (posIn s.C x) r).symm.trans (congrFun heq (.inl (pM r, ())))
  · have h1 := hZ r
    subst h1
    have hp : posIn s.Z (red (s := s) ⟨C, s.Z, a, nM, nZ, e0⟩ x) = posIn s.Z x :=
      Fin.ext (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (hz r)))
    refine (hT.mask x r).symm.trans ((congrFun heq (.inr (pZ r, ()))).trans ?_)
    show (ldOf s.Z s.Z.a).enc _ _ (posIn s.Z x) () =
      (ldOf s.Z s.Z.a).enc _ _ (posIn s.Z (red (s := s) ⟨C, s.Z, a, nM, nZ, e0⟩ x)) ()
    rw [hp]
    rfl

/-- **A share of a jointly close word is close.** Let an encoding on the stage's tables be within e
positions of the range of a word that holds the sent word y. Each position of the message's tree is
read at 2^(s.C.a - M.a) positions of the range. If e is below (M.e + 1) times that number, the
encoding of the seat's share is within the message's own radius of y. -/
theorem share {y : M.cd.Word} {f : s.cIn.Word} (hT : σ.Tie y f) {e : ℕ}
    (hfit : e < (M.e + 1) * 2 ^ (s.C.a - M.a)) (w : s.cIn.N.Wit)
    (hn : offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) ≤ e) :
    M.IsDec y fun j => w.1 (σ.atJ j) := by
  refine ⟨fun q => w.2 (σ.atQ q), ?_⟩
  have h1 := CodeRep.cnt_comp_even (red (s := s) M) (2 ^ (s.C.a - M.a)) (cnt_red σ.ha)
    fun x' => M.cd.T y x' ≠
      M.cd.T (M.cd.enc (fun j => w.1 (σ.atJ j)) fun q => w.2 (σ.atQ q)) x'
  have h2 : cnt (fun x : s.Ps => M.cd.T y (red M x) ≠
      M.cd.T (M.cd.enc (fun j => w.1 (σ.atJ j)) fun q => w.2 (σ.atQ q)) (red M x)) ≤ e :=
    (cnt_mono fun x hx heq => hx (σ.agree hT w x heq)).trans hn
  rw [h1] at h2
  show cnt _ ≤ M.e
  by_contra hlt
  have h3 := Nat.mul_le_mul_left (2 ^ (s.C.a - M.a)) (Nat.succ_le_of_lt (not_le.1 hlt))
  rw [Nat.mul_comm] at hfit
  exact absurd (lt_of_le_of_lt (h3.trans h2) hfit) (lt_irrefl _)

/-- **A witness on the stage's tables has the message's decoding at the seat.** -/
theorem fixed {d : ℕ} (hU : M.Uniq d) {y : M.cd.Word} {f : s.cIn.Word} (hT : σ.Tie y f) {e : ℕ}
    (hfit : e < (M.e + 1) * 2 ^ (s.C.a - M.a)) (w : s.cIn.N.Wit)
    (hn : offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) ≤ e) :
    M.fix y = some fun j => w.1 (σ.atJ j) :=
  Mb.fix_eq hU (σ.share hT hfit w hn)

/-- **One message under two groups.** A message with seats in two stages, whose one radius is below
half its distance and fits both stages' radii: close encodings on the two stages' tables have the
same share at the two seats. -/
theorem one_message {s' : Sg} (σ' : Site s' M) {d : ℕ} (hU : M.Uniq d) {y : M.cd.Word}
    {f : s.cIn.Word} {f' : s'.cIn.Word} (hT : σ.Tie y f) (hT' : σ'.Tie y f') {e e' : ℕ}
    (hfit : e < (M.e + 1) * 2 ^ (s.C.a - M.a)) (hfit' : e' < (M.e + 1) * 2 ^ (s'.C.a - M.a))
    (w : s.cIn.N.Wit) (w' : s'.cIn.N.Wit)
    (hn : offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) ≤ e)
    (hn' : offCnt (Ex := s'.cIn.ext) f' (s'.cIn.enc w'.1 w'.2) ≤ e') :
    (fun j => w.1 (σ.atJ j)) = fun j => w'.1 (σ'.atJ j) :=
  Option.some.inj ((σ.fixed hU hT hfit w hn).symm.trans (σ'.fixed hU hT' hfit' w' hn'))

end Site

/-! ## A group -/

/-- **A group at the stage s**: finitely many sent messages, each with a seat. -/
structure Gp (s : Sg) where
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  mb : ι → Mb
  seat : ∀ i, Site s (mb i)

attribute [instance] Gp.fin Gp.dec

namespace Gp
variable {s : Sg} (G : Gp s)

/-- the members' sent words -/
abbrev Words : Type := ∀ i, (G.mb i).cd.Word
/-- the members' messages -/
abbrev Msgs : Type := ∀ i, (G.mb i).cd.J → GE
/-- the entries of all members' messages -/
abbrev J : Type := Σ i, (G.mb i).cd.J
/-- the members' main rows, and their mask rows -/
abbrev RM : Type := Σ i, Fin (G.mb i).nM
/-- See RM. -/
abbrev RZ : Type := Σ i, Fin (G.mb i).nZ

/-- An entry of a member's message, as an entry of the message on the stage's tables. -/
def ent (n : G.J) : s.cIn.J := (G.seat n.1).atJ n.2

/-- No two rows of the group have the same place. -/
structure Apart : Prop where
  main : ∀ n n' : G.RM, (G.seat n.1).pM n.2 = (G.seat n'.1).pM n'.2 → n = n'
  mask : ∀ n n' : G.RZ, (G.seat n.1).pZ n.2 = (G.seat n'.1).pZ n'.2 → n = n'

/-- **The word f on the stage's tables is what was sent**: it holds each member's word at the
member's seat, and 0 on the rows that no member has. -/
structure Tie (y : G.Words) (f : s.cIn.Word) : Prop where
  mem : ∀ i, (G.seat i).Tie (y i) f
  freeM : ∀ (x : Fin (2 ^ s.C.a)) (b : Fin (s.h + s.g) → Bool),
    (∀ n : G.RM, (G.seat n.1).pM n.2 ≠ b) → f (.inl x) (b, ()) = 0
  freeZ : ∀ (x : Fin (2 ^ s.C.a)) (b : Fin s.h → Bool),
    (∀ n : G.RZ, (G.seat n.1).pZ n.2 ≠ b) → f (.inr x) (b, ()) = 0

/-- **The group's word**, made of the members' sent words. -/
def word (y : G.Words) : s.cIn.Word := fun p =>
  match p with
  | .inl x => fun b => ∑ n : G.RM, if (G.seat n.1).pM n.2 = b.1 then
      y n.1 (.inl (Fin.cast (congrArg (fun C : Fmt.M1.Code => 2 ^ C.a) ((G.seat n.1).hC n.2).symm)
        x)) (n.2, ()) else 0
  | .inr x => fun b => ∑ n : G.RZ, if (G.seat n.1).pZ n.2 = b.1 then
      y n.1 (.inr (Site.red (G.mb n.1) x)) (n.2, ()) else 0

/-- The group's word is what was sent, if no two rows have the same place. -/
theorem tie_word (hA : G.Apart) (y : G.Words) : G.Tie y (G.word y) where
  mem i :=
    { main := fun _ r =>
        (Finset.sum_eq_single (⟨i, r⟩ : G.RM)
          (fun _ _ hne => if_neg fun h => hne (hA.main _ _ h))
          (fun h => absurd (Finset.mem_univ _) h)).trans (if_pos rfl)
      mask := fun _ r =>
        (Finset.sum_eq_single (⟨i, r⟩ : G.RZ)
          (fun _ _ hne => if_neg fun h => hne (hA.mask _ _ h))
          (fun h => absurd (Finset.mem_univ _) h)).trans (if_pos rfl) }
  freeM _ _ hb := Finset.sum_eq_zero fun n _ => if_neg (hb n)
  freeZ _ _ hb := Finset.sum_eq_zero fun n _ => if_neg (hb n)

/-- The members' decodings. -/
noncomputable def fix (y : G.Words) : ∀ i, Option ((G.mb i).cd.J → GE) :=
  fun i => (G.mb i).fix (y i)

end Gp

/-! ## Words from written oracles -/

/-- The three words from word number k on of the column at x, as an element of the extension
field. -/
def symW (d : PQ.RD) (o : (wRound d).Orc) (x k : ℕ) : GE :=
  toE (wordAt d o x k, wordAt d o x (k + 1), wordAt d o x (k + 2))

/-- Word number k of the column at x, as an element of the base field in the extension field. -/
def symF (d : PQ.RD) (o : (wRound d).Orc) (x k : ℕ) : GE := algebraMap GF GE (toF (wordAt d o x k))

/-- Where a message's rows stand in a column of its tree. base: a main symbol is one word, an
element of the base field (otherwise three words). oM, oZ: the first word of the main symbols and of
the mask symbols. -/
structure Lay where
  base : Bool
  oM : ℕ
  oZ : ℕ

/-- **A written oracle as the sent word of a message.** -/
def Mb.ofOrc (M : Mb) (L : Lay) (d : PQ.RD) (o : (wRound d).Orc) : M.cd.Word :=
  M.word (fun x i => if L.base then symF d o x (L.oM + i) else symW d o x (L.oM + 3 * i))
    fun x i => symW d o x (L.oZ + 3 * i)

/-- **A written oracle as the word of a stage's fresh mask rows**, which stand from word oF on in
the columns of a tree of depth a. -/
def frOf (s : Sg) (a oF : ℕ) (d : PQ.RD) (o : (wRound d).Orc) : s.cFr.Word :=
  fun x b => symW d o (x.val % 2 ^ a) (oF + 3 * Sz.rowNo b.1)

/-! ## Groups of one, two and three members -/

/-- A group of one member. -/
def Gp.one {s : Sg} (M : Mb) (σ : Site s M) : Gp s :=
  { ι := Unit, mb := fun _ => M, seat := fun _ => σ }

/-- The names of two members. -/
inductive Duo
  | a
  | b
  deriving DecidableEq, Fintype

/-- One thing for each of two names. -/
def Duo.pick {T : Duo → Type} (x : T .a) (y : T .b) : ∀ i, T i
  | .a => x
  | .b => y

/-- A group of two members. -/
def Gp.two {s : Sg} (Ma Mb' : Mb) (σa : Site s Ma) (σb : Site s Mb') : Gp s :=
  { ι := Duo
    mb := Duo.pick (T := fun _ => Mb) Ma Mb'
    seat := Duo.pick (T := fun i => Site s (Duo.pick (T := fun _ => Mb) Ma Mb' i)) σa σb }

/-- The names of three members. -/
inductive Tri
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- One thing for each of three names. -/
def Tri.pick {T : Tri → Type} (x : T .a) (y : T .b) (z : T .c) : ∀ i, T i
  | .a => x
  | .b => y
  | .c => z

/-- A group of three members. -/
def Gp.three {s : Sg} (Ma Mb' Mc : Mb) (σa : Site s Ma) (σb : Site s Mb') (σc : Site s Mc) : Gp s :=
  { ι := Tri
    mb := Tri.pick (T := fun _ => Mb) Ma Mb' Mc
    seat := Tri.pick (T := fun i => Site s (Tri.pick (T := fun _ => Mb) Ma Mb' Mc i)) σa σb σc }

/-- The word of a group of one member whose tree was sent in the written round d. -/
def Gp.oneWord {s : Sg} (M : Mb) (σ : Site s M) (L : Lay) (d : PQ.RD) (o : (wRound d).Orc) :
    s.cIn.Word :=
  (Gp.one M σ).word fun _ => M.ofOrc L d o

/-- The word of a group of three members whose trees were sent in three written rounds. -/
def Gp.threeWord {s : Sg} (Ma Mb' Mc : Mb) (σa : Site s Ma) (σb : Site s Mb') (σc : Site s Mc)
    (La Lb Lc : Lay) (da db dc : PQ.RD) (oa : (wRound da).Orc) (ob : (wRound db).Orc)
    (oc : (wRound dc).Orc) : s.cIn.Word :=
  (Gp.three Ma Mb' Mc σa σb σc).word
    (Tri.pick (T := fun i => ((Gp.three Ma Mb' Mc σa σb σc).mb i).cd.Word)
      (Ma.ofOrc La da oa) (Mb'.ofOrc Lb db ob) (Mc.ofOrc Lc dc oc))

end OnBytes.Slice
