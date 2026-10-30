-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneWorldChain.lean: a checker on bytes that asks one random oracle, for a chain that
opens stored tables, and a bound on the chance that it says yes while the language fails.

OnBytes/Slice/OneWorld.lean bounds an experiment over one random oracle on bit strings with any
checker that meets two conditions (`hfit`, `hrt`). This file builds such a checker from the
library's strict reader and a decision, for any description S0 of a chain that opens stored tables.

The checker `chainChk`. A function `pre` reads off the maker's output two roots, some bytes and a
place in them, or refuses. The checker then tests that the roots have 32 bytes and that the
description with the statement of these roots is within the limits (`withinX`). It reads the chain
by the reader that asks (`readAskR`, OnBytes/Tie/AskX.lean): every hash of the chain is one question
to the oracle, two for a round's query, but for the one call on the parameter bytes, which is
answered with BLAKE2b's digest of them as a fixed value. (That the reader makes one call on the
parameter bytes is read off its text.) It applies a last test `fin` to the place where the chain
ended, takes the decision on the view, and types what was read. Its yes is that all of this
succeeds.

Main definitions: `chainPost`, `chainChk`, `chainRoots`, `FitsRead`, `RootsIn`.
Main theorems.
 `chainChk_fit`      the checker meets the condition `hfit` of `one_world`, given `FitsRead` and
                     `RootsIn`.
 `chainChk_roots`    the roots that the checker returns are those that `pre` gives (`hrt`).
 `one_world_chain`   with probability at most
                     (t + 2 + tR + tV) * e + 2 (t + 2 + tR + tV + 1)^2 / 2^256 the checker says yes
                     while the pair of strings that is read off the one-block entries of the maker's
                     own trace under the two roots is outside the language. tR is
                     `CostX.fileNX S0 * 2`.

The hypotheses. `SoundLAny`: the protocol made from S0 and the decision is round-by-round sound for
the language, each error count at most e as a share of its round's challenge values. S0 is within
the limits. m is an implementation of the typed oracles by one oracle in which a leaf's and a node's
answer is one block. `RootsIn`: the statement's items of the opened tables hold the roots.
`FitsRead`: on what the reader has read and the typing has typed, a yes of the compiled verifier
under the typed oracle functions that the oracle induces by the format's spelling (`famX`) is a yes
under the family that is read out of the oracle through m.

What is not claimed. All content lies in `SoundLAny` at a named language and a small e, and in
`FitsRead`: both are hypotheses here. OnBytes/Slice/FitsReadAt.lean shows `FitsRead` of one m, under
hypotheses of its own. What "read off" means is m's matter: a string that the maker asked counts as
a leaf or a vertex if m reads it back as one, and its answer is taken through m. Nothing in this
file says that m spells a leaf or a vertex as the format's hash call. `FitsRead` binds m only at
what an accepted run asks. Where the maker's queries determine no symbol at a place, the string has
the library's fixed filling there.
The checker is not the program, which is the Lean port built from OnBytes/: the program does not
call it, hashes with BLAKE2b, does not test `withinX`, and reads a whole file, of which `pre` and
`fin` stand for the parts before and behind the chain. Nothing here ties the checker at BLAKE2b to
the program. No probability is stated of the program or of BLAKE2b.
`pre`, `fin`, `stm` and `dec` are plain functions, fixed before the oracle is drawn. They cannot ask
it: a hash inside one of them is a fixed function. A chain whose statement or decision takes more
from the maker than the two roots is not covered. An entry for tables with a record is such a chain:
its seeds are hashes of the table's name (OnBytes/Entry/Table.lean). BLAKE2b's digest of the
parameter bytes stands in the checker as a plain value, and so does the configuration's digest in
S0.
The limits allow a chain that opens one table or none. The root of a table that is not opened is
free, and `RootsIn` says nothing of it. One chain; no key is checked: both roots are the maker's.
That the checker says yes on any bytes under any oracle is not proved.


That the hypotheses hold together at any description is not
shown here. Nothing on the C++ verifier. The bound says nothing once it reaches 1.

-/
import OnBytes.Slice.OneWorld
import OnBytes.Slice.NamesAt
import OnBytes.Tie.AskX

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (xdOf withinX CompiledAcceptsXAt pinned readInAt readInPinned_compiled readAskR
  readAskR_det readAskR_bound)

variable {γ : Type}

section
variable (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)

/-- What the checker makes of what the reader returns: nothing if the reader has refused, if the
last test fails at the place where the chain ended, if the decision says no on the view, or if the
typing refuses; otherwise the two roots and the typed string. The typing reads no statement, and
neither does the view. -/
def chainPost (r0 r1 : ByteArray) (fin : ℕ → Bool) :
    Option (Fmt.ChainOut × ℕ) → Option (LinkOut 256 ((xdOf S0 stm).L dec))
  | none => none
  | some (o, n) =>
    if fin n && dec (Fmt.viewX (reStated S0 (stm r0 r1)) o) then
      (toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o).map fun π =>
          (bytesToDig r0, bytesToDig r1, asLink (xdOf S0 stm) dec π)
    else none

/-- **The checker on bytes that asks the oracle.** `pre` gives two roots, bytes, a place and a last
test, or refuses. The checker says yes if both roots have 32 bytes, the description with the
statement of these roots is within the limits, the reader that asks reads a chain from that place,
and `chainPost` returns something. It returns the two roots and the typed string. The program does
not call it. -/
def chainChk (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    OComp (rom 256) (Option (LinkOut 256 ((xdOf S0 stm).L dec))) :=
  match pre x with
  | none => OComp.pure none
  | some (r0, r1, b, i, fin) =>
    if r0.size = 32 ∧ r1.size = 32 ∧ withinX (reStated S0 (stm r0 r1)) = true then
      (readAskR (reStated S0 (stm r0 r1)) [] b i).bind fun rd =>
        OComp.pure (chainPost S0 stm dec r0 r1 fin rd)
    else OComp.pure none

/-- The statement's item of every table that the chain opens holds that table's root: item 0 the
first root, item 1 the second, for all roots of 32 bytes. An item other than 1 counts as the first
table's; within the limits there are items 0 and 1 alone. -/
def RootsIn : Prop :=
  ∀ r0 r1 : ByteArray, r0.size = 32 → r1.size = 32 → ∀ t ∈ S0.stored.flatten,
    Fmt.itemRoot (stm r0 r1) t.item = some (if t.item == 1 then r1 else r0)

/-- On what the reader has read under any roots and the typing has typed: if the compiled verifier
says yes under the typed oracle functions that the oracle induces by the format's spelling, it says
yes under the family that is read out of the oracle through m. -/
def FitsRead (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256) : Prop :=
  ∀ (g : Fam (rom 256)) (r0 r1 b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (n : ℕ)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up),
    Fmt.readChainX (m := Id) (Fmt.HO (pinned (oB (g ())) S0.base.params))
      (reStated S0 (stm r0 r1)) [] b i = some (o, n) →
    toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
      (xdOf S0 stm).xs dec o = some π →
    (theRunAny (xdOf S0 stm) dec r0 r1 π).det
      (famX (xdOf S0 stm) dec (oB (g ())) ((xdOf S0 stm).K + 1)) = true →
    (theRunAny (xdOf S0 stm) dec r0 r1 π).det (readBlocks m g) = true

/-- The checker tosses no coin and asks the oracle at most `CostX.fileNX S0 * 2` strings, whatever
the maker's output. -/
theorem chainChk_bound (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (x : γ) : (chainChk S0 stm dec pre x).NoCoin ∧
      (chainChk S0 stm dec pre x).QueryBound (Tie.CostX.fileNX S0 * 2) := by
  unfold chainChk
  split
  · exact ⟨trivial, trivial⟩
  · rename_i r0 r1 b i fin _
    split
    · have hb := readAskR_bound (reStated S0 (stm r0 r1)) [] b i
      rw [Tie.CostX.fileNX_congr (reStated S0 (stm r0 r1)) S0 rfl rfl] at hb
      refine ⟨hb.1.bind fun _ => trivial, ?_⟩
      have h : ((readAskR (reStated S0 (stm r0 r1)) [] b i).bind fun rd =>
          OComp.pure (chainPost S0 stm dec r0 r1 fin rd)).QueryBound
            (Tie.CostX.fileNX S0 * 2 + 0) := hb.2.bind fun _ => trivial
      exact h
    · exact ⟨trivial, trivial⟩

/-- **The checker meets the condition `hfit` of `one_world`.** Under every oracle, the compiled Link
verifier accepts what the checker returns, under the family that is read out of the oracle through
m. Asked: `RootsIn` and `FitsRead`. -/
theorem chainChk_fit (hroots : RootsIn S0 stm)
    (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256)
    (hfits : FitsRead S0 stm dec m)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (g : Fam (rom 256)) (x : γ) (lo : LinkOut 256 ((xdOf S0 stm).L dec))
    (h : (chainChk S0 stm dec pre x).det g = some lo) :
    (vLS (WkAny (xdOf S0 stm) dec) (256 + 8 * S0.base.plan.salt) 256 lo.1 lo.2.1 lo.2.2).det
      (readBlocks m g) = true := by
  unfold chainChk at h
  split at h
  · cases h
  · rename_i r0 r1 b i fin _
    split at h
    · rename_i hc
      obtain ⟨h0, h1, hw⟩ := hc
      rw [OComp.det_bind, readAskR_det] at h
      have h' : chainPost S0 stm dec r0 r1 fin
          (Fmt.readChainX (m := Id) (Fmt.HO (pinned (oB (g ())) S0.base.params))
            (reStated S0 (stm r0 r1)) [] b i) = some lo := h
      cases e : Fmt.readChainX (m := Id) (Fmt.HO (pinned (oB (g ())) S0.base.params))
          (reStated S0 (stm r0 r1)) [] b i with
      | none =>
        rw [e] at h'
        cases h'
      | some on =>
        obtain ⟨o, n⟩ := on
        rw [e] at h'
        have h2 : (if fin n && dec (Fmt.viewX (reStated S0 (stm r0 r1)) o) then
            (toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds
              (xdOf S0 stm).a (xdOf S0 stm).xs dec o).map fun π =>
                (bytesToDig r0, bytesToDig r1, asLink (xdOf S0 stm) dec π)
          else none) = some lo := h'
        split at h2
        · rename_i hb
          obtain ⟨π, hπ, rfl⟩ := Option.map_eq_some_iff.1 h2
          have hdec : dec (Fmt.viewX (reStated S0 (stm r0 r1)) o) = true :=
            (Bool.and_eq_true_iff.1 hb).2
          have hread : readInAt (pinned (oB (g ())) (reStated S0 (stm r0 r1)).base.params)
              (reStated S0 (stm r0 r1)) b i ⟨[]⟩ =
                some (⟨o, viewOf (reStated S0 (stm r0 r1)) o, n⟩, ⟨o.seen⟩) := by
            unfold readInAt
            show (match Fmt.readChainX (m := Id) (Fmt.HO (pinned (oB (g ())) S0.base.params))
              (reStated S0 (stm r0 r1)) [] b i with
              | none => none
              | some (o, j) =>
                some ((⟨o, viewOf (reStated S0 (stm r0 r1)) o, j⟩ : ChainRead),
                  (⟨o.seen⟩ : Session))) = _
            rw [e]
          have hc := readInPinned_compiled (oB (g ())) (fun s => size_digToBytes _)
            (reStated S0 (stm r0 r1)) stm dec r0 r1 h0 h1 hw rfl (hroots r0 r1 h0 h1) ⟨[]⟩ b i _ _
            hread ((congrArg dec (viewOf_eq _ o)).trans hdec)
          obtain ⟨π', hty, hv⟩ :=
            (compiledAt_reStated (oB (g ())) S0 (stm r0 r1) stm dec r0 r1 o).1 hc
          have eπ : π' = π := Option.some.inj (hty.symm.trans hπ)
          subst eπ
          exact hfits g r0 r1 b i o n π' e hπ
            ((congrArg (OComp.det _) (vls_any (xdOf S0 stm) dec (256 + 8 * S0.base.plan.salt)
              (bytesToDig r0) (bytesToDig r1) π')).symm.trans hv)
        · cases h2
    · cases h

/-- The two roots that the checker can return, read off the maker's output. -/
def chainRoots (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    Option (Dig 256 × Dig 256) :=
  (pre x).map fun p => (bytesToDig p.1, bytesToDig p.2.1)

/-- The roots that the checker returns are those that `pre` reads off the maker's output. -/
theorem chainChk_roots (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (g : Fam (rom 256)) (x : γ) (lo : LinkOut 256 ((xdOf S0 stm).L dec))
    (h : (chainChk S0 stm dec pre x).det g = some lo) :
    chainRoots pre x = some (lo.1, lo.2.1) := by
  unfold chainChk at h
  unfold chainRoots
  split at h
  · cases h
  · rename_i r0 r1 b i fin hpre
    rw [hpre]
    split at h
    · rw [OComp.det_bind] at h
      have h' : chainPost S0 stm dec r0 r1 fin
          ((readAskR (reStated S0 (stm r0 r1)) [] b i).det g) = some lo := h
      cases e : (readAskR (reStated S0 (stm r0 r1)) [] b i).det g with
      | none =>
        rw [e] at h'
        cases h'
      | some on =>
        obtain ⟨o, n⟩ := on
        rw [e] at h'
        have h2 : (if fin n && dec (Fmt.viewX (reStated S0 (stm r0 r1)) o) then
            (toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds
              (xdOf S0 stm).a (xdOf S0 stm).xs dec o).map fun π =>
                (bytesToDig r0, bytesToDig r1, asLink (xdOf S0 stm) dec π)
          else none) = some lo := h'
        split at h2
        · obtain ⟨π, -, rfl⟩ := Option.map_eq_some_iff.1 h2
          rfl
        · cases h2
    · cases h

/-- **One world, for a chain that opens stored tables.** The oracle is a function from all bit
strings to strings of 256 bits, each value drawn uniformly and independently. A maker with at most t
queries puts out a value, off which `pre` reads two roots, bytes, a place and a last test. The
checker `chainChk` reads the chain from these bytes, asking the same oracle for every hash but the
digest of the parameter bytes, decides, and types. With probability at most
(t + 2 + tR + tV) * e + 2 (t + 2 + tR + tV + 1)^2 / 2^256 it says yes while the pair of strings that
is read off the one-block entries of THE MAKER's OWN TRACE under the two roots is outside the
language. tR is `CostX.fileNX S0 * 2`; tV is the library's bound on the compiled verifier's typed
queries. The 2 and tV come from the proof (OnBytes/Slice/OneWorld.lean): in the experiment no
compiled verifier runs. Asked: S0 is within the limits; `SoundLAny` at e; in m a leaf's and a
node's answer is one block; `RootsIn`; `FitsRead`. `FitsRead` is a hypothesis on m, and the strings
are read off through m. The checker is not the program, and no probability is stated of the program
or of BLAKE2b. That the checker says yes on anything is not shown. The roots are the maker's choice.
The bound says nothing once it reaches 1. -/
theorem one_world_chain (hw : withinX S0 = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (hs : SoundLAny (xdOf S0 stm) dec Lg εs) (hroots : RootsIn S0 stm)
    (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256)
    (hl : m.blocks Batch.OracleName.leaf = 1) (hn : m.blocks Batch.OracleName.node = 1)
    (hfits : FitsRead S0 stm dec m)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (A : OComp (rom 256) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr (twoExp A (chainChk S0 stm dec pre))
        (fun _ => twoWinOne (WkAny (xdOf S0 stm) dec) m Lg fun _ y => y) ≤
      ((t + 2 + Tie.CostX.fileNX S0 * 2 +
          tVQB (WkAny (xdOf S0 stm) dec).Lk (WkAny (xdOf S0 stm) dec).depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + 2 + Tie.CostX.fileNX S0 * 2 +
          tVQB (WkAny (xdOf S0 stm) dec).Lk (WkAny (xdOf S0 stm) dec).depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2
          / 2 ^ 256 :=
  one_world (WkAny (xdOf S0 stm) dec)
    (okgAny (xdOf S0 stm) dec (within_work S0 stm hw) (within_okx S0 stm hw)) Lg εs
    (linkAt_any (within_work S0 stm hw) (within_okx S0 stm hw) Lg εs hs)
    (256 + 8 * S0.base.plan.salt) 256 m hl hn (chainChk S0 stm dec pre) (chainRoots pre)
    (Tie.CostX.fileNX S0 * 2) (fun x => (chainChk_bound S0 stm dec pre x).1)
    (fun x => (chainChk_bound S0 stm dec pre x).2)
    (chainChk_fit S0 stm dec hroots m hfits pre) (chainChk_roots S0 stm dec pre) A t hA

end

end OnBytes.Slice
