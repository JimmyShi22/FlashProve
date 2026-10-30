-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/BlockFront.lean: a block's vectors sent encoded: the encoded rounds.

How. A block's list of rounds s (Blocks/Block.lean) comes with encoding data d : `EncData F E s`:
which vectors each round sends, and under which codes. `encShape s d` has received words in place of
the vectors: same plain parts, same challenges. Each vector is sent as the encoding of its full
message (message, encoding randomness, zeros). (Words of this library: lean/GLOSSARY.md.)

Fields. Each vector has a flag: over F (e.g. packed cells, digits, multiplicities) or over E. A
vector over F has its entries, its encoding randomness and the symbols of its encoding in F.
Relations and claims take all entries in E, through the inclusion. Under `Enc.Props` what a word
over F decodes to is over F (`toE_ofE_of_decodes`, by `DecodesTo.exists_liftWord`,
Blocks/Decode.lean).

Notation: `e`: a `REnc F E r`: how the oracle part of one round of a block is sent: as the vectors a
: A; the vector a has `rows a` rows of `(code a).msg` entries; `e.mrow`, `e.q`: `e.A → ℕ`: number
of row variables; number of positions read in each vector and its masks; `VIdx s d`: the vectors of
all rounds.
-/
import Blocks.BlockLib
import Blocks.Decode
import Blocks.LevelDef
import Mathlib.Data.FinEnum
noncomputable section -- Lean tags what it cannot compile

set_option linter.unusedSectionVars false

namespace Blocks
open Iop Prob
open scoped ENNReal

/-! ## The field of a vector -/

section Kf
variable {F E : Type}

instance Kf.instZero [Zero F] [Zero E] : ∀ b, Zero (Kf F E b)
  | true => inferInstanceAs (Zero F)
  | false => inferInstanceAs (Zero E)

variable [Field F] [Field E] [Algebra F E]

theorem Kf.toE_zero : ∀ b : Bool, (0 : Kf F E b).toE = 0
  | true => map_zero (algebraMap F E)
  | false => rfl

/-- back from E: a left inverse of the inclusion -/
def Kf.ofE : {b : Bool} → E → Kf F E b
  | true, x => Function.invFun (algebraMap F E) x
  | false, x => x

theorem Kf.ofE_toE : ∀ {b : Bool} (x : Kf F E b), Kf.ofE (x.toE) = x
  | true, x => Function.leftInverse_invFun (algebraMap F E).injective x
  | false, _ => rfl

theorem Kf.toE_mem_range :
    ∀ {b : Bool} (_ : b = true) (x : Kf F E b), x.toE ∈ Set.range (algebraMap F E)
  | true, _, x => ⟨x, rfl⟩

/-- the encoding of a row over its field -/
def encK (C : Code.Enc F) :
    {b : Bool} → (Fin C.msg → Kf F E b) → (Fin C.r → Kf F E b) → Fin C.n → Kf F E b
  | true, m, ρ => C.G.mulVec (C.fm (K := F) m ρ)
  | false, m, ρ => (C.GE E).mulVec (C.fm (K := E) m ρ)

/-- A row over F is encoded by the encoder of the code itself, over F; so the hiding property of the
code applies to it as it is. -/
theorem encK_true (C : Code.Enc F) (m : Fin C.msg → F) (ρ : Fin C.r → F) :
    encK (E := E) C (b := true) m ρ = C.enc m ρ := rfl

/-- A row over E is encoded over E. -/
theorem encK_false (C : Code.Enc F) (m : Fin C.msg → E) (ρ : Fin C.r → E) :
    encK C (b := false) m ρ = C.encE E m ρ := rfl

/-- Mapped into E, the encoding over the field of the row is the encoding over E. -/
theorem toE_encK (C : Code.Enc F) :
    ∀ {b : Bool} (m : Fin C.msg → Kf F E b) (ρ : Fin C.r → Kf F E b) (p : Fin C.n),
      (encK C m ρ p).toE = (C.GE E).mulVec (C.fm (fun j => (m j).toE) fun t => (ρ t).toE) p
  | true, m, ρ, p => by
      have h1 : (C.fm (fun j => algebraMap F E (m j)) fun t => algebraMap F E (ρ t)) =
          Code.liftWord E (C.fm (K := F) m ρ) :=
        funext fun i => C.fm_map (algebraMap F E) (map_zero _) m ρ i
      show algebraMap F E (C.G.mulVec (C.fm (K := F) m ρ) p) =
        (C.G.map (algebraMap F E)).mulVec
          (C.fm (fun j => algebraMap F E (m j)) fun t => algebraMap F E (ρ t)) p
      rw [h1, Code.mulVec_map_liftWord]
      rfl
  | false, _, _, _ => rfl

/-- Under `Enc.Props`, what a word over the field of its vector decodes to is over that field:
`Kf.ofE` and the inclusion leave the decoded entries unchanged. -/
theorem toE_ofE_of_decodes [Fintype F] [Fintype E] {C : Code.Enc F} (hC : C.Props E) {R : Type} :
    ∀ {b : Bool} (w : Fin C.n → R → Kf F E b) (M : R → Fin C.k → E),
      DecodesTo (C.GE E) C.e (fun i p => (w p i).toE) M →
      ∀ i (j : ℕ), (Kf.ofE (F := F) (b := b) (nat (M i) j)).toE = nat (M i) j
  | false, _, _, _, _, _ => rfl
  | true, w, M, h, i, j => by
      obtain ⟨M₀, -, rfl⟩ := DecodesTo.exists_liftWord
        (G := C.G) (f := fun i p => (w p i : F)) (hasDist_G hC) hC.unique h
      have h2 : nat (Code.liftWord E (M₀ i)) j = algebraMap F E (nat (M₀ i) j) := by
        unfold nat
        split_ifs
        · rfl
        · exact (map_zero _).symm
      rw [h2]
      exact congrArg (algebraMap F E) (Function.leftInverse_invFun (algebraMap F E).injective _)

end Kf

/-- How the oracle part of one round of a block is sent: as the vectors a : A; the vector a has
`rows a` rows of `(code a).msg` entries. -/
structure REnc (F E : Type) (r : Round) where
  A : Type
  [finA : Fintype A]
  [decA : DecidableEq A]
  code : A → Code.Enc F
  rows : A → ℕ
  mrow : A → ℕ
  role : A → Role
  q : A → ℕ
  /-- is the vector over F (else over E) -/
  overF : A → Bool
  [nePos : ∀ a, Nonempty (Fin (code a).n)]
  vec : r.Orc ≃ (∀ a, Fin (rows a) → Fin (code a).msg → Kf F E (overF a))

attribute [instance] REnc.finA REnc.decA REnc.nePos

/-- Encoding data for all rounds of a list. -/
def EncData (F E : Type) : Shape → Type 1
  | [] => PUnit
  | r :: s => REnc F E r × EncData F E s

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

def EncData.app : {s t : Shape} → EncData F E s → EncData F E t → EncData F E (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (e, a), b => (e, EncData.app a b)

/-- The round with words in place of the vectors. One symbol is one column of one vector. -/
@[reducible] def REnc.round {r : Round} (e : REnc F E r) : Round :=
  wordsRound e.A (fun a => (e.code a).n) (fun a => Fin (e.rows a) → Kf F E (e.overF a))
    r.Plain r.Chal (fun _ _ => 0) r.dPlain

/-- The encoded rounds. -/
def encShape : (s : Shape) → EncData F E s → Shape
  | [], _ => []
  | _ :: s, (e, d) => e.round :: encShape s d

def encPoint : (s : Shape) → (d : EncData F E s) → (encShape s d).IsPoint
  | [], _ => ()
  | r :: s, (e, d) =>
    (wordsPoint e.A (fun a => (e.code a).n) (fun a => Fin (e.rows a) → Kf F E (e.overF a))
        r.Plain r.Chal (fun _ _ => 0) r.dPlain,
      encPoint s d)

/-- The vectors of all rounds. -/
def VIdx : (s : Shape) → EncData F E s → Type
  | [], _ => Empty
  | _ :: s, (e, d) => e.A ⊕ VIdx s d

instance instFintypeVIdx : ∀ (s : Shape) (d : EncData F E s), Fintype (VIdx s d)
  | [], _ => inferInstanceAs (Fintype Empty)
  | _ :: s, (e, d) => by
      haveI := instFintypeVIdx s d
      exact inferInstanceAs (Fintype (e.A ⊕ VIdx s d))

def vcode : (s : Shape) → (d : EncData F E s) → VIdx s d → Code.Enc F
  | _ :: _, (e, _), .inl a => e.code a
  | _ :: s, (_, d), .inr v => vcode s d v

def vrows : (s : Shape) → (d : EncData F E s) → VIdx s d → ℕ
  | _ :: _, (e, _), .inl a => e.rows a
  | _ :: s, (_, d), .inr v => vrows s d v

def vmrow : (s : Shape) → (d : EncData F E s) → VIdx s d → ℕ
  | _ :: _, (e, _), .inl a => e.mrow a
  | _ :: s, (_, d), .inr v => vmrow s d v

def vrole : (s : Shape) → (d : EncData F E s) → VIdx s d → Role
  | _ :: _, (e, _), .inl a => e.role a
  | _ :: s, (_, d), .inr v => vrole s d v

def vq : (s : Shape) → (d : EncData F E s) → VIdx s d → ℕ
  | _ :: _, (e, _), .inl a => e.q a
  | _ :: s, (_, d), .inr v => vq s d v

def vover : (s : Shape) → (d : EncData F E s) → VIdx s d → Bool
  | _ :: _, (e, _), .inl a => e.overF a
  | _ :: s, (_, d), .inr v => vover s d v

theorem vne : ∀ (s : Shape) (d : EncData F E s) (v : VIdx s d), Nonempty (Fin (vcode s d v).n)
  | _ :: _, (e, _), .inl a => e.nePos a
  | _ :: s, (_, d), .inr v => vne s d v

/-- message parts of all vectors, in E; below: encoding randomness, full messages, words -/
abbrev Vecs (s : Shape) (d : EncData F E s) : Type :=
  ∀ v : VIdx s d, Fin (vrows s d v) → Fin (vcode s d v).msg → E
/-- the vectors over their own fields -/
abbrev VecsK (s : Shape) (d : EncData F E s) : Type :=
  ∀ v : VIdx s d, Fin (vrows s d v) → Fin (vcode s d v).msg → Kf F E (vover s d v)
abbrev Fulls (s : Shape) (d : EncData F E s) : Type :=
  ∀ v : VIdx s d, Fin (vrows s d v) → Fin (vcode s d v).k → E
abbrev Wrds (s : Shape) (d : EncData F E s) : Type :=
  ∀ v : VIdx s d, Fin (vcode s d v).n → Fin (vrows s d v) → E

/-! ### Both lists of rounds have the same challenges and plain parts -/

def rhoUp : (s : Shape) → (d : EncData F E s) → Rho s → Rho (encShape s d)
  | [], _, _ => ()
  | _ :: s, (_, d), (c, ρ) => (c, rhoUp s d ρ)

/-! ### Words and vectors of a transcript -/

/-- the words in a transcript of the encoded rounds, mapped into E -/
def ewords : (s : Shape) → (d : EncData F E s) → Tr (encShape s d) → Wrds s d
  | _ :: _, (_, _), (m, _, _), .inl a => fun p i => (m.1 a p i).toE
  | _ :: s, (_, d), (_, _, τ), .inr v => ewords s d τ v

/-- the vectors in a transcript of the unencoded rounds, over their own fields -/
def vecsK : (s : Shape) → (d : EncData F E s) → Tr s → VecsK s d
  | _ :: _, (e, _), (m, _, _), .inl a => e.vec m.1 a
  | _ :: s, (_, d), (_, _, τ), .inr v => vecsK s d τ v

/-- the vectors of one message, mapped into E -/
def REnc.vecE {r : Round} (e : REnc F E r) (o : r.Orc) (a : e.A)
    (i : Fin (e.rows a)) (j : Fin (e.code a).msg) : E :=
  (e.vec o a i j).toE

/-- the vectors in a transcript of the unencoded rounds, mapped into E -/
def vecs : (s : Shape) → (d : EncData F E s) → Tr s → Vecs s d
  | _ :: _, (e, _), (m, _, _), .inl a => e.vecE m.1 a
  | _ :: s, (_, d), (_, _, τ), .inr v => vecs s d τ v

theorem toE_vecsK :
    ∀ (s : Shape) (d : EncData F E s) (τ : Tr s) (v : VIdx s d)
        (i : Fin (vrows s d v)) (j : Fin (vcode s d v).msg),
      (vecsK s d τ v i j).toE = vecs s d τ v i j
  | _ :: _, (_, _), (_, _, _), .inl _, _, _ => rfl
  | _ :: s, (_, d), (_, _, τ), .inr v, i, j => toE_vecsK s d τ v i j

end

section Sound
variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-- The words of the transcript decode to the full messages M. -/
def DecAll (s : Shape) (d : EncData F E s) (τ : Tr (encShape s d)) (M : Fulls s d) : Prop :=
  ∀ v,
    cnt (fun p => ∃ i, ewords s d τ v p i ≠ ((vcode s d v).GE E).mulVec (M v i) p) ≤ (vcode s d v).e

end Sound

/-! ## The encodings of one round's vectors -/

section Honest
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E]

/-- the encodings of one round's vectors -/
def REnc.words {r : Round} (e : REnc F E r) (o : r.Orc)
    (R : ∀ a, Fin (e.rows a) → Fin (e.code a).r → Kf F E (e.overF a)) : e.round.Orc :=
  fun a p i => encK (e.code a) (e.vec o a i) (R a i) p

end Honest

/-! ## The vectors of two lists of rounds in a row

Entries are indexed by natural numbers (0 outside the range), so that no statement needs a cast
between the types of the two indexings. -/

section Append
variable {F E : Type} [Field F] [Field E] [Algebra F E]

/-- a vector of s, as a vector of s ++ t -/
def vL :
    {s t : Shape} → (d : EncData F E s) → (d' : EncData F E t) → VIdx s d → VIdx (s ++ t) (d.app d')
  | _ :: _, _, (_, _), _, .inl a => .inl a
  | _ :: _, _, (_, d), d', .inr v => .inr (vL d d' v)

/-- a vector of t, as a vector of s ++ t -/
def vR :
    {s t : Shape} → (d : EncData F E s) → (d' : EncData F E t) →
    VIdx t d' → VIdx (s ++ t) (d.app d')
  | [], _, _, _, v => v
  | _ :: _, _, (_, d), d', v => .inr (vR d d' v)

theorem vcode_vL :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx s d),
      vcode _ (d.app d') (vL d d' v) = vcode s d v
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: _, _, (_, d), d', .inr v => vcode_vL d d' v

theorem vcode_vR :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx t d'),
      vcode _ (d.app d') (vR d d' v) = vcode t d' v
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, d), d', v => vcode_vR d d' v

theorem vrows_vL :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx s d),
      vrows _ (d.app d') (vL d d' v) = vrows s d v
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: _, _, (_, d), d', .inr v => vrows_vL d d' v

theorem vrows_vR :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx t d'),
      vrows _ (d.app d') (vR d d' v) = vrows t d' v
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, d), d', v => vrows_vR d d' v

/-- entry (i, j) of the vector v of an unencoded transcript, 0 outside the range -/
def vecsN (s : Shape) (d : EncData F E s) (τ : Tr s) (v : VIdx s d) : ℕ → ℕ → E := fun i j =>
  nat (fun i' => nat (vecs s d τ v i') j) i

theorem vecsN_vL :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (τ : Tr (s ++ t)) (v : VIdx s d),
      vecsN _ (d.app d') τ (vL d d' v) = vecsN s d (Tr.fst τ) v
  | _ :: _, _, (_, _), _, (_, _, _), .inl _ => rfl
  | _ :: _, _, (_, d), d', (_, _, τ), .inr v => vecsN_vL d d' τ v

theorem vecsN_vR :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (τ : Tr (s ++ t)) (v : VIdx t d'),
      vecsN _ (d.app d') τ (vR d d' v) = vecsN t d' (Tr.snd (s := s) τ) v
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, d), d', (_, _, τ), v => vecsN_vR d d' τ v

theorem vecsN_apply (s : Shape) (d : EncData F E s) (τ : Tr s) (v : VIdx s d)
    (i : Fin (vrows s d v)) (j : Fin (vcode s d v).msg) :
    vecsN s d τ v i.val j.val = vecs s d τ v i j := by
  unfold vecsN nat
  rw [dif_pos i.2]
  exact dif_pos j.2

end Append

/-! ## Encoding data for the rounds of Blocks/BlockLib.lean, and of `vRoundK` -/

section Lib
variable {F : Type} [Field F] (E : Type) [Field E] [Algebra F E]

/-- Encoding data for a round `vRound` whose vector a has (code a).msg entries in a row. -/
def REnc.ofV (A : Type) [Fintype A] [DecidableEq A] (code : A → Code.Enc F)
    (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ) [∀ a, Nonempty (Fin (code a).n)]
    (K C : Type) [Fintype C] [Nonempty C] :
    REnc F E (vRound E A rows (fun a => (code a).msg) K C) where
  A := A
  code := code
  rows := rows
  mrow := mrow
  role := role
  q := q
  overF := fun _ => false
  vec := Equiv.refl _

/-- A round of a block whose vectors are over F or over E, by a flag for each vector. -/
@[reducible] def vRoundK (F : Type) [Field F] [Algebra F E] (A : Type) (overF : A → Bool)
    (rows len : A → ℕ) (K C : Type) [Fintype C] [Nonempty C] : Round where
  Orc := ∀ a, Fin (rows a) → Fin (len a) → Kf F E (overF a)
  Pos := Empty
  Sym := fun _ => Empty
  rd := fun _ p => p.elim
  Plain := K → E
  Chal := C
  dOrc := fun _ _ _ => 0
  dPlain := fun _ => 0

/-- Encoding data for a round `vRoundK`. -/
def REnc.ofVK (A : Type) [Fintype A] [DecidableEq A] (overF : A → Bool) (code : A → Code.Enc F)
    (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ) [∀ a, Nonempty (Fin (code a).n)] (K C : Type)
    [Fintype C] [Nonempty C] :
    REnc F E (vRoundK E F A overF rows (fun a => (code a).msg) K C) where
  A := A
  code := code
  rows := rows
  mrow := mrow
  role := role
  q := q
  overF := overF
  vec := Equiv.refl _

/-- Encoding data for a round `vRoundK` whose lengths are those of the codes by an equation, not by
definition. -/
def REnc.ofVKc (A : Type) [Fintype A] [DecidableEq A] (overF : A → Bool)
    (code : A → Code.Enc F) (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ) (len : A → ℕ)
    (hlen : ∀ a, (code a).msg = len a) [∀ a, Nonempty (Fin (code a).n)] (K C : Type)
    [Fintype C] [Nonempty C] :
    REnc F E (vRoundK E F A overF rows len K C) where
  A := A
  code := code
  rows := rows
  mrow := mrow
  role := role
  q := q
  overF := overF
  vec := Equiv.piCongrRight fun a =>
    Equiv.piCongrRight fun _ => Equiv.arrowCongr (finCongr (hlen a)).symm (Equiv.refl _)

/-- Indexed by natural numbers, the entries are those of the message. -/
theorem REnc.nat_vecE_ofVKc (A : Type) [Fintype A] [DecidableEq A] (overF : A → Bool)
    (code : A → Code.Enc F) (rows mrow : A → ℕ) (role : A → Role) (q : A → ℕ) (len : A → ℕ)
    (hlen : ∀ a, (code a).msg = len a) [∀ a, Nonempty (Fin (code a).n)] (K C : Type) [Fintype C]
    [Nonempty C] (o : (vRoundK E F A overF rows len K C).Orc) (a : A) (i : Fin (rows a)) (t : ℕ) :
    nat ((REnc.ofVKc E A overF code rows mrow role q len hlen K C).vecE o a i) t =
      nat (fun j => (o a i j).toE) t := by
  unfold nat
  by_cases h : t < (code a).msg
  · have h' : t < len a := hlen a ▸ h
    rw [dif_pos h',
      dif_pos
        (show t < ((REnc.ofVKc E A overF code rows mrow role q len hlen K C).code a).msg from h)]
    rfl
  · have h' : ¬ t < len a := hlen a ▸ h
    rw [dif_neg h',
      dif_neg
        (show ¬ t < ((REnc.ofVKc E A overF code rows mrow role q len hlen K C).code a).msg from h)]

/-- Encoding data for a round without vectors. -/
def REnc.none (F : Type) [Field F] [Algebra F E] (K C : Type) [Fintype C] [Nonempty C] :
    REnc F E (vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) K C) where
  A := Empty
  code := fun a => Empty.elim a
  rows := fun a => Empty.elim a
  mrow := fun a => Empty.elim a
  role := fun a => Empty.elim a
  q := fun a => Empty.elim a
  overF := fun a => Empty.elim a
  nePos := fun a => Empty.elim a
  vec := ⟨fun _ a => Empty.elim a,
    fun _ a => Empty.elim a,
    fun _ => funext fun a => Empty.elim a,
    fun _ => funext fun a => Empty.elim a⟩

variable {E}

theorem sum_vIdx_cons {M : Type} [AddCommMonoid M] {r : Round} {s : Shape} (e : REnc F E r)
    (d : EncData F E s) (f : VIdx (r :: s) (e, d) → M) :
    ∑ v, f v = ∑ a, f (.inl a) + ∑ v, f (.inr v) :=
  Fintype.sum_sum_type f

end Lib

end Blocks
