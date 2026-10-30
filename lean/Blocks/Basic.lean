-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Basic.lean: helper definitions for the interactive protocols of Blocks/.

Conventions.
* Points with coordinates in E and lists of challenges are functions ℕ → E (0 beyond their length),
  and entries of vectors are indexed by natural numbers, 0 outside the range. So a term of a
  construction need not carry a proof about an index.
* The first coordinate of a point belongs to the most significant bit of an index (an index i‖j has
  the row bits first).

Also here: `Role`, the part that a vector plays (tested, promised, pad); `Kf`, the field of
a vector by its flag, with `Kf.toE`, the inclusion in E; `NoOrc`, a shape whose prover messages
have no oracle part, with `Tr.eq_of_noOrc`: such a transcript is given by its verifier messages and
its plain parts.
-/
import Iop.Shape
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Algebra.Defs

namespace Blocks
open Iop

variable {E : Type} [Field E]

/-- eq(a, z) for the m coordinates a (off), .., a (off + m - 1) and the m-bit number z:
the product over t of a_t if bit t of z (counted from the top) is 1, and of 1 - a_t if it is 0. -/
def eqN (m off : ℕ) (a : ℕ → E) (z : ℕ) : E :=
  ∏ t ∈ Finset.range m, (if z.testBit (m - 1 - t) then a (off + t) else 1 - a (off + t))

/-- A list as a function on ℕ, 0 beyond its end. -/
def ofList (l : List E) : ℕ → E := fun t => l.getD t 0

/-- A vector as a function on ℕ, 0 beyond its end. -/
def nat {K : Type} [Zero K] {n : ℕ} (v : Fin n → K) : ℕ → K := fun t =>
  if h : t < n then v ⟨t, h⟩ else 0

theorem nat_fun_of_lt {K : Type} [Zero K] {n : ℕ} (f : ℕ → K) {t : ℕ} (h : t < n) :
    nat (fun i : Fin n => f i.val) t = f t := by
  unfold nat
  rw [dif_pos h]

/-- A round whose prover message consists of the oracles w a : Fin (n a) → Sy a, a : A, and of a
plain part. One position is (a, j). -/
@[reducible] def wordsRound (A : Type) (n : A → ℕ) (Sy : A → Type) (Plain Chal : Type)
    [Fintype Chal] [Nonempty Chal] (dSy : ∀ a, Sy a) (dPlain : Plain) : Round where
  Orc := ∀ a, Fin (n a) → Sy a
  Pos := Σ a, Fin (n a)
  Sym := fun p => Sy p.1
  rd := fun o p => o p.1 p.2
  Plain := Plain
  Chal := Chal
  dOrc := fun a _ => dSy a
  dPlain := dPlain

/-- A round without oracles. -/
@[reducible] def plainRound (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dPlain : Plain) :
    Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Empty
  rd := fun _ p => p.elim
  Plain := Plain
  Chal := Chal
  dOrc := ()
  dPlain := dPlain

/-- The oracles of these rounds are strings (`Round.IsPoint`, Iop/Shape.lean: a round whose oracle
part is a string that is read symbol by symbol, over a finite set of positions). Here for
`wordsRound`; below for `plainRound` (`plainPoint`), and, from the same of the parts, for two lists
of rounds in a row (`pointApp`) and for n copies of a round before a list (`pointRep`). -/
def wordsPoint (A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (Sy : A → Type)
    (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dSy : ∀ a, Sy a) (dPlain : Plain) :
    (wordsRound A n Sy Plain Chal dSy dPlain).IsPoint where
  finPos := inferInstanceAs (Fintype (Σ a, Fin (n a)))
  decPos := inferInstanceAs (DecidableEq (Σ a, Fin (n a)))
  ofSyms := fun f a j => f ⟨a, j⟩
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun p => dSy p.1

def plainPoint (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dPlain : Plain) :
    (plainRound Plain Chal dPlain).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun p => p.elim

def pointApp : {s t : Shape} → s.IsPoint → t.IsPoint → Shape.IsPoint (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (a, as), b => (a, pointApp as b)

def pointRep (r : Round) (h : r.IsPoint) :
    (n : ℕ) → {t : Shape} → t.IsPoint → Shape.IsPoint (List.replicate n r ++ t)
  | 0, _, b => b
  | n + 1, _, b => (h, pointRep r h n b)

/-- Oracle positions of t, as positions of s ++ t. -/
def posR : {s t : Shape} → OPos t → OPos (s ++ t)
  | [], _, p => p
  | _ :: s, _, p => .inr (posR (s := s) p)

/-- To which part, s or t, a position belongs. -/
def posCase : {s t : Shape} → OPos (s ++ t) → OPos s ⊕ OPos t
  | [], _, p => .inr p
  | _ :: _, _, .inl p => .inl (.inl p)
  | _ :: s, _, .inr p => (posCase (s := s) p).map .inr id

/-- The messages and challenges of n equal rounds. -/
def trList (r : Round) : (n : ℕ) → Tr (List.replicate n r) → List (r.Msg × r.Chal)
  | 0, _ => []
  | n + 1, (m, c, a) => (m, c) :: trList r n a

/-- one round of a sumcheck: two scalars; then a challenge (used by the levels,
Blocks/LevelDef.lean, among others) -/
abbrev LinSh.rSC (E : Type) [Field E] [Fintype E] : Round := plainRound (E × E) E (0, 0)
inductive Role | tested | promised | pad
  deriving DecidableEq

/-- The field of a vector: F if its flag is set (packed cells, digits,
multiplicities), else E. -/
def Kf (F E : Type) : Bool → Type
  | true => F
  | false => E

instance Kf.fintype (F E : Type) [Fintype F] [Fintype E] : ∀ b, Fintype (Kf F E b)
  | true => inferInstanceAs (Fintype F)
  | false => inferInstanceAs (Fintype E)

instance Kf.nonempty (F E : Type) [Nonempty F] [Nonempty E] : ∀ b, Nonempty (Kf F E b)
  | true => inferInstanceAs (Nonempty F)
  | false => inferInstanceAs (Nonempty E)

/-- the inclusion in E -/
def Kf.toE {F E : Type} [Field F] [Field E] [Algebra F E] : {b : Bool} → Kf F E b → E
  | true, a => algebraMap F E a
  | false, a => a

/-- No prover message of the list of rounds has an oracle part. -/
def NoOrc : Shape → Prop
  | [] => True
  | r :: s => Subsingleton r.Orc ∧ NoOrc s

theorem NoOrc.append : ∀ {s t : Shape}, NoOrc s → NoOrc t → NoOrc (s ++ t)
  | [], _, _, h => h
  | _ :: _, _, h, h' => ⟨h.1, NoOrc.append h.2 h'⟩

theorem NoOrc.replicate {r : Round} (h : Subsingleton r.Orc) : ∀ n : ℕ, NoOrc (List.replicate n r)
  | 0 => trivial
  | n + 1 => ⟨h, NoOrc.replicate h n⟩

/-- A transcript without oracles is given by the verifier messages and the plain parts. -/
theorem Tr.eq_of_noOrc :
    ∀ {s : Shape}, NoOrc s → ∀ {a b : Tr s}, a.rho = b.rho → a.plains = b.plains → a = b
  | [], _, (), (), _, _ => rfl
  | r :: s, h, ((o, p), c, a), ((o', p'), c', a'), hρ, hπ => by
      have h1 : c = c' := congrArg Prod.fst hρ
      have h2 : a.rho = a'.rho := congrArg Prod.snd hρ
      have h3 : p = p' := congrArg Prod.fst hπ
      have h4 : a.plains = a'.plains := congrArg Prod.snd hπ
      have h5 : o = o' := h.1.elim o o'
      rw [h1, h3, h5, Tr.eq_of_noOrc h.2 h2 h4]

end Blocks
