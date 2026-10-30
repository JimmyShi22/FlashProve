-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/FamT.lean: the typed oracle functions `gJ P O` (OnBytes/Maker/Page/Frame.lean) in a
form for evaluation, with the proof that it is `gJ P O` (`famT_eq`). What the K + 1 strings of one
chain query share is computed once for the query. Every answer is made as bytes first; each block of
a chain answer stands behind a thunk, so that it is hashed only if it is read, but for the last
block, which is hashed at once. A query that is asked twice is answered twice.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

After Run/CodingFnThin.lean, which does the same for one chain (`famB`, `decP`, `famP`).

Main names.
  `OnceJ`, `onceJ`, `onceFill` and their ties to `fbCallJ` and `fillJ`:
    Johnson/RunOne/OnceCore.lean.
  `RunJ P`: the two files' functions "once a query", with the law that they are `onceJ`.
  `onceOf`, `takenFb`, `strFb`; `strFb_eq`: the string of a block, from what is computed once, is
    `codeJ`'s.
  `fbTB`, `famTB`, `decT`, `famT`; `famT_eq`: `famT P R O = gJ P O`.

Limits. What an evaluator computes how often is a fact about the compiler, no theorem. An array of
K + 1 thunks is laid at every chain query. The interface L is an implicit parameter throughout, as
in Frame.lean: the first principle of Run/CodingFnThin.lean (the interface behind a function of
Unit) is not followed: the form can be evaluated at an interface that has code. The one `RunJ` of
this file is `RunJ.plain` (msg and nonce each read the plain part once a query); one made of
`onceFill`: Johnson/RunOne/OnceD.lean (`onceD`). Nothing on soundness.

-/
import Johnson.RunOne.OnceCore
import Run.CodingFnThin

set_option autoImplicit false

namespace Johnson.RunOne

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run
open OnBytes OnBytes.Maker OnBytes.Maker.Page

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-! ## Bytes first -/

variable {K : ℕ}

/-- The two files' functions "once a query", with the law that they are `onceJ`. -/
structure RunJ (P : PageJ L K) where
  key : FbIn 256 L .test → OnceJ
  proof : FbIn 256 L .onl → OnceJ
  hk : ∀ q, key q = onceJ P.key q
  hp : ∀ q, proof q = onceJ P.proof q

/-- At any page: `onceJ` itself (msg and nonce each read the plain part once a query). -/
def RunJ.plain (P : PageJ L K) : RunJ P := ⟨onceJ P.key, onceJ P.proof, fun _ => rfl, fun _ => rfl⟩

/-- The answer of O at a string, as bytes: data; no byte where there is no string. -/
def bytesT (O : ByteArray → ByteArray) : Option ByteArray → ByteArray
  | some s => O s
  | none => ByteArray.empty

theorem ansT_eq (O : ByteArray → ByteArray) (s : Option ByteArray) :
    digS (bytesT O s) = ansJ O s := by
  cases s with
  | none => rfl
  | some s => exact digS_eq _

/-- The string of a block of a chain query, from what a partial spelling writes there and what the
query's calls share. -/
def strBT (taken : Option (List Bool)) (c : OnceJ) (j : Fin (K + 1)) : Option ByteArray :=
  match taken with
  | some s => some (bitsToBytes s)
  | none => (c.call K j).map strOf

/-- What the calls of a chain query share, under any tag. -/
def onceOf (P : PageJ L K) (R : RunJ P) : (t : Tag) → FbIn 256 L t → OnceJ
  | .test, q => R.key q
  | .onl, q => R.proof q
  | .link, _ => .nothing

/-- What a partial spelling writes at a block of a chain query. -/
def takenFb (P : PageJ L K) : (t : Tag) → FbIn 256 L t → Fin (K + 1) → Option (List Bool)
  | .test, q, j => P.seeds (q, j)
  | .link, q, j => P.link (q, j)
  | .onl, _, _ => none

/-- The string of a block of a chain query, from what the query's calls share. -/
def strFb (P : PageJ L K) (t : Tag) (q : FbIn 256 L t) (c : OnceJ) (j : Fin (K + 1)) :
    Option ByteArray :=
  strBT (takenFb P t q j) c j

/-- **The strings are `codeJ`'s.** -/
theorem strFb_eq (P : PageJ L K) (R : RunJ P) (t : Tag) (q : FbIn 256 L t) (j : Fin (K + 1)) :
    strFb P t q (onceOf P R t q) j = codeJ P (.fb t) q j := by
  cases t with
  | test =>
    show strBT (P.seeds (q, j)) (R.key q) j = codeJ P (.fb .test) q j
    rw [R.hk]
    unfold strBT codeJ
    show _ = match P.seeds (q, j) with
      | some s => some (bitsToBytes s)
      | none => (fbCallJ P.key K q j).map strOf
    rw [onceJ_call]
  | onl =>
    show strBT none (R.proof q) j = codeJ P (.fb .onl) q j
    rw [R.hp]
    show ((onceJ P.proof q).call K j).map strOf = (fbCallJ P.proof K q j).map strOf
    rw [onceJ_call]
  | link =>
    show strBT (P.link (q, j)) .nothing j = codeJ P (.fb .link) q j
    unfold strBT codeJ
    show _ = match P.link (q, j) with
      | some s => some (bitsToBytes s)
      | none => (none : Option Fmt.OQ).map strOf
    rfl

/-- K + 1 blocks, each behind a thunk. -/
def thunksOf (K : ℕ) (f : Fin (K + 1) → ByteArray) : Array (Thunk ByteArray) :=
  Array.ofFn (n := K + 1) fun j => Thunk.mk fun _ => f j

/-- The bytes behind the i-th thunk; no byte where there is none. -/
def thAt (th : Array (Thunk ByteArray)) (i : ℕ) : ByteArray :=
  match th[i]? with
  | some x => x.get
  | none => ByteArray.empty

theorem thAt_thunksOf (f : Fin (K + 1) → ByteArray) (j : Fin (K + 1)) :
    thAt (thunksOf K f) j.val = f j := by
  unfold thAt thunksOf
  rw [Array.getElem?_ofFn, dif_pos j.isLt]
  rfl

/-- The K + 1 blocks of a chain answer as data, from what the query's calls share. -/
def fbTB (P : PageJ L K) (O : ByteArray → ByteArray) (t : Tag) (q : FbIn 256 L t) (c : OnceJ) :
    Array (Thunk ByteArray) :=
  thunksOf K fun j => bytesT O (strFb P t q c j)

/-- **The answer to a typed query as data**: one string's answer, or K + 1 thunks. What the K + 1
strings share is computed where it stands, once. -/
def famTB (P : PageJ L K) (R : RunJ P) (O : ByteArray → ByteArray) :
    (o : OracleName) → domOf 256 L o → Array (Thunk ByteArray)
  | .leaf, q => #[Thunk.pure (bytesT O (codeJ P .leaf q (0 : Fin 1)))]
  | .node, q => #[Thunk.pure (bytesT O (codeJ P .node q (0 : Fin 1)))]
  | .rleaf, q => #[Thunk.pure (bytesT O (codeJ P .rleaf q (0 : Fin 1)))]
  | .rnode, q => #[Thunk.pure (bytesT O (codeJ P .rnode q (0 : Fin 1)))]
  | .fb t, q => fbTB P O t q (onceOf P R t q)
  | .fbw _ _, _ => #[]
  | .g t, q => #[Thunk.pure (bytesT O (codeJ P (.g t) q (0 : Fin 1)))]
  | .ann, _ => #[]
  | .other, q => #[Thunk.pure (bytesT O (codeJ P .other q (0 : Fin 1)))]

/-- The data as a typed answer. -/
def decT (K : ℕ) : (o : OracleName) → Array (Thunk ByteArray) → rngOf 256 K o
  | .leaf, a => digS (thAt a 0)
  | .node, a => digS (thAt a 0)
  | .rleaf, a => digS (thAt a 0)
  | .rnode, a => digS (thAt a 0)
  | .fb _, a => (fun k => digS (thAt a k.val), digS (thAt a K))
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .g _, a => digS (thAt a 0)
  | .ann, _ => ()
  | .other, a => digS (thAt a 0)

/-- **The typed oracle functions, for a run.** -/
def famT (P : PageJ L K) (R : RunJ P) (O : ByteArray → ByteArray) : Fam (typedOracleFamily 256 K L) :=
  fun o q => decT K o (famTB P R O o q)

/-- **The tie to `gJ`.** -/
theorem famT_eq (P : PageJ L K) (R : RunJ P) (O : ByteArray → ByteArray) :
    famT P R O = gJ P O := by
  funext o q
  cases o with
  | leaf => exact ansT_eq O (codeJ P .leaf q (0 : Fin 1))
  | node => exact ansT_eq O (codeJ P .node q (0 : Fin 1))
  | rleaf => exact ansT_eq O (codeJ P .rleaf q (0 : Fin 1))
  | rnode => exact ansT_eq O (codeJ P .rnode q (0 : Fin 1))
  | g t => exact ansT_eq O (codeJ P (.g t) q (0 : Fin 1))
  | other => exact ansT_eq O (codeJ P .other q (0 : Fin 1))
  | ann => rfl
  | fbw _ _ => rfl
  | fb t =>
    have key : ∀ (f : Fin (K + 1) → Option ByteArray),
        (∀ j, f j = codeJ P (.fb t) q j) →
        decT K (.fb t) (thunksOf K fun j => bytesT O (f j)) = gJ P O (.fb t) q := by
      intro f hf
      have hb : ∀ j : Fin (K + 1),
          digS (thAt (thunksOf K fun j => bytesT O (f j)) j.val) =
            ansJ O (codeJ P (.fb t) q j) := by
        intro j
        rw [thAt_thunksOf, ansT_eq, hf]
      refine Prod.ext ?_ ?_
      · funext k
        exact hb k.castSucc
      · exact hb (Fin.last K)
    exact key _ fun j => strFb_eq P R t q j

end Johnson.RunOne

#print axioms Johnson.RunOne.ansT_eq
#print axioms Johnson.RunOne.strFb_eq
#print axioms Johnson.RunOne.thAt_thunksOf
#print axioms Johnson.RunOne.famT_eq
