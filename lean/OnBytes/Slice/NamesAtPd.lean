-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NamesAtPd.lean: "the compiled verifier accepts what was read" does not read the
statement in the description; with the digest of the parameter bytes as an argument.

OnBytes/Slice/NamesAt.lean shows that of `Tie.CompiledAcceptsXAt` (`compiledAt_reStated`). The two
sides stand at two descriptions whose interfaces have types that are equal, but not by evaluation;
the proof writes the body of `Run.PQ.famX` once more over components and rounds. This file says
eight of its declarations again for `Tie.famXPd` and `Tie.CompiledAcceptsXAtPd`
(OnBytes/Tie/FamPd.lean, StoredAtPd.lean), with a byte string pd in the place of the format's
digest. `Parts`, `pdG`, `leafG` and their laws are NamesAt's, which is not changed; the component
`params` is not read here.

Main definitions: `firstGPd`, `famGPd`.
Main theorems: `famXPd_parts`, `famXPd_reStated`, `compiledAtPd_reStated`.

What is not claimed. What the head of OnBytes/Slice/NamesAt.lean does not claim. Nothing on
soundness; no probability.

-/
import OnBytes.Slice.NamesAt
import OnBytes.Tie.StoredAtPd

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf inFile firstXPd famXPd CompiledAcceptsXAtPd)

/-- The text of `Tie.firstXPd` over components and rounds. -/
def firstGPd (P : Parts) (pd : ByteArray) (ds : List RD) (dec : View → Bool) (K : ℕ)
    (q : FbIn 256 (P.L ds dec) .link) (j : Fin (K + 1)) : Option Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, P.label, Fmt.zero32,
            firstBytes pd (P.stm (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (pdG P ds dec) K q j

/-- The text of `Tie.famXPd` over components and rounds. -/
def famGPd (P : Parts) (pd : ByteArray) (ds : List RD) (dec : View → Bool)
    (O : ByteArray → ByteArray) (K : ℕ) :
    Fam (spec 256 K (P.L ds dec))
  | .leaf, q => ansOf O (leafG P ds dec q)
  | .node, q => ansOf O (nodeCallC P.cfg q)
  | .fb .link, q =>
    (fun k => ansOf O (firstGPd P pd ds dec K q k.castSucc), ansOf O (firstGPd P pd ds dec K q
        (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- `Tie.firstXPd` at a description is `firstGPd` at the description's components and rounds. -/
theorem firstGPd_parts (D : XD) (dec : View → Bool) (pd : ByteArray) (K : ℕ) (q : FbIn 256
    (D.L dec) .link)
    (j : Fin (K + 1)) : firstXPd D dec pd K q j = firstGPd (partsOf D) pd D.ds dec K q j := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold firstXPd firstGPd
  rw [pdG_parts]
  cases round with
  | succ n => rfl
  | zero =>
    cases head with
    | f1 cms x salt => rcases cms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> cases x <;> rfl
    | f2 _ _ => rfl
    | f3 _ _ => rfl
    | f4 _ _ => rfl
    | f5 => rfl

/-- `Tie.famXPd` at a description is `famGPd` at the description's components and rounds. -/
theorem famXPd_parts (D : XD) (dec : View → Bool) (pd : ByteArray) (O : ByteArray → ByteArray)
    (K : ℕ) :
    famXPd D dec pd O K = famGPd (partsOf D) pd D.ds dec O K := by
  funext o
  match o with
  | .leaf =>
    funext q
    exact congrArg (ansOf O) (leafG_parts D dec q)
  | .node => rfl
  | .fb .link =>
    funext q
    exact Prod.ext (funext fun k => congrArg (ansOf O) (firstGPd_parts D dec pd K q k.castSucc))
      (congrArg (ansOf O) (firstGPd_parts D dec pd K q (Fin.last K)))
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

/-- `famGPd` along an equation between two lists of rounds. The number of blocks is a function Kf of
the rounds. -/
theorem famGPd_heq (P : Parts) (pd : ByteArray) (Kf : List RD → ℕ) (dec : View → Bool)
    (O : ByteArray → ByteArray)
    (ds ds' : List RD) (h : ds' = ds) :
    HEq (famGPd P pd ds' dec O (Kf ds' + 1)) (famGPd P pd ds dec O (Kf ds + 1)) := by
  subst h
  rfl

/-- The typed oracle functions that O induces at S with another statement are those that it induces
at S. The two have types that are equal, but not by evaluation. -/
theorem famXPd_reStated (pd : ByteArray) (S : Fmt.SpecX) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (O : ByteArray → ByteArray) :
    HEq (famXPd (xdOf (reStated S x) stm) dec pd O ((xdOf (reStated S x) stm).K + 1))
      (famXPd (xdOf S stm) dec pd O ((xdOf S stm).K + 1)) := by
  rw [famXPd_parts, famXPd_parts]
  exact famGPd_heq (partsOf (xdOf S stm)) pd (kMax fun e k =>
      (bsRound S.base.plan.field e k).b) dec O
    (rds (inFile S.base)) (rds (inFile (reStated S x).base)) (_root_.Run.rds_congr _ _ rfl rfl)

/-- One direction of `compiledAtPd_reStated`. -/
theorem compiledAtPd_to (pd : ByteArray) (O : ByteArray → ByteArray) (S : Fmt.SpecX) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (r0 r1 : ByteArray)
    (o : Fmt.ChainOut) (h : CompiledAcceptsXAtPd pd O (reStated S x) stm dec r0 r1 o) :
    CompiledAcceptsXAtPd pd O S stm dec r0 r1 o := by
  obtain ⟨π', hty', hv'⟩ := h
  obtain ⟨π, g, hty, hg, hv⟩ := accept_to (ckP S.base.plan.field)
    (kMax fun e k => (bsRound S.base.plan.field e k).b) (fun K => chalP S.base.plan.field K)
    (xdOf S stm).a (xdOf S stm).xs dec (rds (inFile S.base)) (rds (inFile (reStated S x).base))
    (_root_.Run.rds_congr _ _ rfl rfl) S.base.plan.salt S.base.cfg (256 + 8 * S.base.plan.salt)
    (bytesToDig r0) (bytesToDig r1) o (famXPd (xdOf (reStated S x) stm) dec pd O _) π' hty' hv'
  have e : g = famXPd (xdOf S stm) dec pd O ((xdOf S stm).K + 1) :=
    eq_of_heq (hg.trans (famXPd_reStated pd S x stm dec O))
  subst e
  exact ⟨π, hty, hv⟩

/-- **`CompiledAcceptsXAtPd` does not read the statement in the description.** For every byte string
pd, function O on byte strings, description S, string x, function `stm`, decision, pair of roots and
chain as read: the compiled verifier accepts at S with the statement x, under the typed oracle
functions that O induces there, if and only if it accepts at S, under those that O induces there. -/
theorem compiledAtPd_reStated (pd : ByteArray) (O : ByteArray → ByteArray) (S : Fmt.SpecX)
    (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (r0 r1 : ByteArray)
    (o : Fmt.ChainOut) :
    CompiledAcceptsXAtPd pd O
        (reStated S x) stm dec r0 r1 o ↔ CompiledAcceptsXAtPd pd O S stm dec r0 r1 o :=
  ⟨compiledAtPd_to pd O S x stm dec r0 r1 o,
    fun h => compiledAtPd_to pd O (reStated S x) S.base.statement stm dec r0 r1 o h⟩

end OnBytes.Slice
