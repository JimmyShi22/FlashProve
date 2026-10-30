-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OCompM.lean: a rule of the format written over a variable monad, read in the monad of trees of
queries and run at an oracle, gives what the same function gives in the identity monad with that
oracle as a function: the base of that equation, and the count of queries.

Definitions that compute, and theorems. No rule of the format is stated here but the hash over an
oracle (Fmt/Rules23.lean: `HM`, `HO`).

Why: the definition's verifier is a tree of queries, that is, an oracle computation
(ZKCP/Defs.lean: `OComp lam`; it is a monad there). The format's rules that hash are written once,
over a variable monad m and a variable "ask". At m := trees, ask := `askB` they are trees, so that
they can be part of a verifier (Run/TransportO.lean: `WrO.parse`); at m := Id they are the
functions that a run evaluates. What connects the two is that "run at f" is a morphism of monads.

Main names:
  `c.det f`: "run at f".
  `det_pure`, `det_bind`: "run at f" is a morphism of monads; also in the forms to which
    do-notation unfolds (`det_pure'`, `det_bind'`, `det_map'`: simp lemmas).
  `c.NoCoin`: pure, bind, map keep it. ZKCP/Main.lean has the same definition under the name
    `OComp.DrawsNoCoin`; that the two are equivalent is `run_draws` in Run/RunIsVProofs.lean.
  `run_of_noCoin`: a tree without coins, run at f in the sense of the definition (a distribution),
    is the point mass at c.det f: so a statement on c.det f is one on c.run f (Run/TransportO.lean:
    `WrO.Back`).
  `askB s`, `oB f`: their doc comments tell them.
  `det_askB`, `det_HM`: one query, and the hash `Fmt.HM askB`, run at f.
  The count: "asks at most" is the definition's `QueryBound`: pure: 0; askB: 1; HM askB: at most 2
    (1 but under the one number with a long answer); bind: the sum (`asks_bind'`, on
    ZKCP/ManyOfOne.lean); a larger number is a bound too (`QueryBound.mono`, ZKCP/ManyOfOne.lean).
  `det_toRom`: the same run in the generic language of trees (Rom/Cache.lean: `OComp.det`,
    Rom/Bridge.lean: `toRom`).

Limits: this file does not say that the morphism passes through loops (folds, maps, for-loops,
recursion on fuel): Run/Hom.lean states it of `List.foldlM` alone; of functions of the format:
Run/HomFmt.lean. This file does not say any rule of sections 4, 5, 7, 8. It does not say that oB f
at the real hash is the format's oracle (`Fmt.oracle`): f is any oracle here. It does not say that
bytes and bits undo each other.

Terms: lean/GLOSSARY.md.
-/
import ZKCP.ManyOfOne
import Rom.Bridge
import Rom.Cache
import Run.CodingBits
import Fmt.Rules23

set_option autoImplicit false

namespace ZKCP
namespace OComp
variable {lam : ℕ} {α β : Type}

/-- The tree's result at the oracle f, every coin toss yielding 0. -/
def det (f : Oracle lam) : OComp lam α → α
  | pure a => a
  | query q k => (k (f q)).det f
  | sample _ k => (k 0).det f

/-- No path has a coin toss. -/
def NoCoin : OComp lam α → Prop
  | pure _ => True
  | query _ k => ∀ r, (k r).NoCoin
  | sample _ _ => False

theorem det_pure (f : Oracle lam) (a : α) : (pure a : OComp lam α).det f = a := rfl

/-- "Run at f" goes through bind. -/
theorem det_bind (f : Oracle lam) (c : OComp lam α) (g : α → OComp lam β) :
    (c.bind g).det f = (g (c.det f)).det f := by
  induction c with
  | pure a => rfl
  | query q k ih => exact ih _
  | sample n k ih => exact ih 0

@[simp] theorem det_pure' (f : Oracle lam) (a : α) : (Pure.pure a : OComp lam α).det f = a := rfl

@[simp] theorem det_bind' (f : Oracle lam) (c : OComp lam α) (g : α → OComp lam β) :
    (c >>= g).det f = (g (c.det f)).det f := det_bind f c g

@[simp] theorem det_map' (f : Oracle lam) (h : α → β) (c : OComp lam α) :
    (h <$> c).det f = h (c.det f) := det_bind f c _

theorem noCoin_pure (a : α) : (pure a : OComp lam α).NoCoin := trivial

theorem NoCoin.bind {c : OComp lam α} {g : α → OComp lam β}
    (hc : c.NoCoin) (hg : ∀ a, (g a).NoCoin) : (c.bind g).NoCoin := by
  induction c with
  | pure a => exact hg a
  | query q k ih => exact fun r => ih r (hc r)
  | sample n k _ => exact hc.elim

theorem noCoin_pure' (a : α) : (Pure.pure a : OComp lam α).NoCoin := trivial

theorem NoCoin.bind' {c : OComp lam α} {g : α → OComp lam β}
    (hc : c.NoCoin) (hg : ∀ a, (g a).NoCoin) : (c >>= g).NoCoin := hc.bind hg

theorem NoCoin.map' {c : OComp lam α} (h : α → β) (hc : c.NoCoin) : (h <$> c).NoCoin :=
  hc.bind fun _ => trivial

/-- A tree without coins, run at f, is the point mass at its result. -/
theorem run_of_noCoin (f : Oracle lam) :
    ∀ (c : OComp lam α), c.NoCoin → c.run f = PMF.pure (c.det f)
  | pure _, _ => rfl
  | query q k, h => run_of_noCoin f (k (f q)) (h (f q))
  | sample _ _, h => h.elim

/-- The count: pure asks nothing. -/
theorem asks_pure' (a : α) (t : ℕ) : (Pure.pure a : OComp lam α).QueryBound t := trivial

/-- The count: if c asks at most s and what follows asks at most t at every value, bind asks at
most s + t. -/
theorem asks_bind' {c : OComp lam α} {g : α → OComp lam β} {s t : ℕ}
    (hc : c.QueryBound s) (hg : ∀ a, (g a).QueryBound t) : (c >>= g).QueryBound (s + t) :=
  QueryBound.bind g t hg c s hc

theorem asks_map' {c : OComp lam α} (h : α → β) {s : ℕ} (hc : c.QueryBound s) :
    (h <$> c).QueryBound s :=
  QueryBound.mapO h c s hc

/-- The same run in the generic language of trees (`Rom.OComp`). -/
theorem det_toRom (g : Rom.Fam (Rom.rom lam)) :
    ∀ (c : OComp lam α), (Rom.toRom c).det g = c.det (g ())
  | pure _ => rfl
  | query q k => det_toRom g (k (g () q))
  | sample _ k => det_toRom g (k 0)

end OComp

instance (lam : ℕ) : LawfulMonad (OComp lam) :=
  LawfulMonad.mk' (m := OComp lam)
    (id_map := fun x => bind_pure_right x)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun x f g => OComp.bind_bind x f g)

end ZKCP

namespace Run
open ZKCP

/-- One query: the byte string's bits (Run/CodingBits.lean; the order of bits is
Fmt/Rules1.lean's); the answer's 256 bits as 32 bytes. -/
def askB (s : ByteArray) : OComp 256 ByteArray :=
  .query (bytesToBits s) fun d => .pure (digToBytes d)

/-- The oracle as a function on byte strings. -/
def oB (f : Oracle 256) (s : ByteArray) : ByteArray := digToBytes (f (bytesToBits s))

@[simp] theorem det_askB (f : Oracle 256) (s : ByteArray) : (askB s).det f = oB f s := rfl

theorem noCoin_askB (s : ByteArray) : (askB s).NoCoin := fun _ => trivial

theorem asks_askB (s : ByteArray) : (askB s).QueryBound 1 := fun _ => trivial

/-- The hash over the tree monad, run at f, is the hash over the function `oB f`. -/
@[simp] theorem det_HM (f : Oracle 256) (number tree index : Nat) (start bytes : ByteArray) :
    (_root_.Fmt.HM askB number tree index start bytes).det f =
      _root_.Fmt.HO (oB f) number tree index start bytes := by
  unfold _root_.Fmt.HM _root_.Fmt.HO
  split <;> rfl

theorem noCoin_HM (number tree index : Nat) (start bytes : ByteArray) :
    (_root_.Fmt.HM askB number tree index start bytes).NoCoin := by
  unfold _root_.Fmt.HM
  split
  · exact fun _ _ => trivial
  · exact noCoin_askB _

/-- The hash asks at most twice. -/
theorem asks_HM (number tree index : Nat) (start bytes : ByteArray) :
    (_root_.Fmt.HM askB number tree index start bytes).QueryBound 2 := by
  unfold _root_.Fmt.HM
  split
  · exact fun _ _ => trivial
  · exact fun _ => trivial

/-- Once, but under the one number with a long answer (162). -/
theorem asks_HM_one (number tree index : Nat) (start bytes : ByteArray) (h : number ≠ 162) :
    (_root_.Fmt.HM askB number tree index start bytes).QueryBound 1 := by
  unfold _root_.Fmt.HM
  rw [if_neg h]
  exact asks_askB _

end Run
