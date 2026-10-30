-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainChkAsk.lean: the checker on bytes with the digest of the parameter bytes as an
argument, the checker that asks the oracle for that digest too, and the equation between their
values.

Why. The checker `chainChk` (OnBytes/Slice/OneWorldChain.lean) asks an oracle for every hash but
one: the digest of the parameter bytes stands in it as a constant, BLAKE2b's. A verifier that hashes
by the oracle asks for that digest too. OnBytes/Slice/AtSet.lean leads a bound for every table T of
values of the oracle at a finite set of strings to a bound for the oracle; there a yes stands under
the oracle with the table put over it (`over S T g`), and a part's checker is evaluated under g.
This file has what that step wants of the checkers' VALUES, and no more: the checker that holds the
table's value as its constant has, under g, the value that the asking checker has under g with the
table put over it. `pinOn` (OnBytes/Slice/AtSet.lean) is not used. An instance of the join need not
go by `chainChkPd` or `ReadsNot`: a part whose checker answers by the tables has its value by
`det_pinOn` (OnBytes/Slice/AtSet.lean). `chainChk` serves the configuration's digest
alone. For the digest of the parameter bytes such a part has `pinOn` of the like of `chainChkAsk`
as its checker: OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean.

Main definitions.
 `Tie.askPinnedAt params pd`, `Tie.pinnedAt O params pd`   `Tie.askPinned` and `Tie.pinned` with the
                       value pd as an argument.
 `Tie.readBy ask`, `Tie.readByR ask`   the library's strict reader at the hash that asks by any
                       `ask`.
 `chainChkBy ask`      `chainChk`'s text with that reader.
 `chainChkPd pd`       the checker with pd in the place of the digest of the parameter bytes.
 `chainChkAsk`         the checker that asks the oracle for every hash of the chain's reader.
 `chainChkFn O`        the checker's text as a plain function of a function O on byte strings,
                       nothing pinned.
 `s0Of params`         the bit string at which the asking checker asks for the digest of `params`.
 `ReadsNot F B`        the value of F at a function on byte strings does not depend on that
                       function's values at the strings of B.
Main theorems.
 `chainChk_eq_pd`      `chainChk` is `chainChkPd` at the format's own digest.
 `det_chainChkPd_fn`, `det_chainChkAsk_fn`   the two checkers' values at an oracle, as values of
                       `chainChkFn`.
 `HO_bitsOf`, `chainChkAsk_bitsOf`, `chainChkAsk_oBits`   for O with answers of 32 bytes the asking
                       checker's value at the oracle on bit strings that is made from O is the plain
                       function at O; its case at the format's oracle.
 `oB_over`             the oracle with a table put at `s0Of params` alone, as a function on byte
                       strings, is g's function with the table's value pinned at `Tie.digestStr
                       params`.
 `det_chainChkPd`      (chainChkPd .. (the table's value) ..).det g = (chainChkAsk ..).det (over
                       {s0Of params} T g).
 `det_chainChkPd_of`   the same for a larger set S that holds `s0Of params`, UNDER A HYPOTHESIS: the
                       plain function does not read its argument at the other strings of S.
 `chainChkPd_bound`, `chainChkAsk_bound`   both toss no coin and ask at most `CostX.fileNX S0 * 2`
                       strings.

What is not claimed. NO BOUND HERE. For the like of `chainChkAsk` answered by a table:
OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean. For `chainChkPd` at a pd other than the format's digest none
stands. For a larger set the hypothesis `ReadsNot` is proved of nothing. By a reading of the
reader's text it asks one call with the number 169, its own, so it should hold where the other
strings of S are strings of calls with that number. A proof would go through the reader's functions
and the library's beneath them once more, as OnBytes/Tie/HomX.lean and OnBytes/Tie/CostX.lean do. No
lemma of the library says that two hashes which agree by call number are read alike. The
configuration's digest is a constant of the description. Equations between values; both sides may be
"no". No probability. The checkers are not the program (the Lean port built from OnBytes/); nor are
they the C++ verifier.

-/
import OnBytes.Slice.ChainChkAt
import OnBytes.Slice.AtSet

set_option autoImplicit false

namespace OnBytes.Tie
open ZKCP

/-! ## The value as an argument -/

/-- `askPinned` with the value as an argument: the string of the call that hashes `params` is
answered, without a question, with pd. Every other string is one question to the oracle. -/
def askPinnedAt (params pd s : ByteArray) : OComp 256 ByteArray :=
  if s = digestStr params then pure pd else Run.askB s

/-- `pinned` with the value as an argument: O, but for the string of the call that hashes `params`,
which is answered with pd. -/
def pinnedAt (O : ByteArray → ByteArray) (params pd : ByteArray) : ByteArray → ByteArray :=
  fun s => if s = digestStr params then pd else O s

/-- `askPinned` is `askPinnedAt` at the format's own digest. -/
theorem askPinned_eq_at (params : ByteArray) :
    askPinned params = askPinnedAt params (Fmt.paramsDigest params) := rfl

/-- `pinned` is `pinnedAt` at the format's own digest. -/
theorem pinned_eq_at (O : ByteArray → ByteArray) (params : ByteArray) :
    pinned O params = pinnedAt O params (Fmt.paramsDigest params) := rfl

/-- At the oracle f, `askPinnedAt params pd s` gives what `pinnedAt (Run.oB f) params pd` gives. -/
theorem det_askPinnedAt (f : ZKCP.Oracle 256) (params pd s : ByteArray) :
    (askPinnedAt params pd s).det f = pinnedAt (Run.oB f) params pd s := by
  unfold askPinnedAt pinnedAt
  split <;> rfl

/-- `askPinnedAt params pd s` tosses no coin and asks at most one question. -/
theorem qp_askPinnedAt (params pd s : ByteArray) :
    (Run.qp 256).le (askPinnedAt params pd s) 1 fun _ => True := by
  unfold askPinnedAt
  split
  · exact ⟨trivial, trivial, trivial⟩
  · exact ⟨Run.noCoin_askB s, Run.asks_askB s, OComp.all_true _⟩

/-- `Run.askB s` tosses no coin and asks at most one question. -/
theorem qp_askB (s : ByteArray) : (Run.qp 256).le (Run.askB s) 1 fun _ => True :=
  ⟨Run.noCoin_askB s, Run.asks_askB s, OComp.all_true _⟩

/-! ## The reader, at any way of asking -/

/-- The library's strict reader of a chain that opens stored tables, at the hash that asks by `ask`.
`readAsk` is this at `askPinned S.base.params`. The program does not call it. -/
def readBy (ask : ByteArray → OComp 256 ByteArray) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) : OComp 256 (Option (Fmt.ChainOut × Nat)) :=
  Fmt.readChainX (Fmt.HM ask) S seen b i

/-- The same as a tree in the library's generic language, over the family with one oracle. -/
def readByR (ask : ByteArray → OComp 256 ByteArray) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) : Rom.OComp (Rom.rom 256) (Option (Fmt.ChainOut × Nat)) :=
  Rom.toRom (readBy ask S seen b i)

/-- `readAskR` is `readByR` at `askPinned S.base.params`. -/
theorem readAskR_eq_by (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    readAskR S seen b i = readByR (askPinned S.base.params) S seen b i := rfl

/-- If at the oracle f every `ask s` gives `O s`, the result at f of the reader that asks by `ask`
is what the strict reader reads, in the identity monad, at the hash that O induces. An equation
between two results; both may be "refused". -/
theorem readBy_det (f : ZKCP.Oracle 256) (ask : ByteArray → OComp 256 ByteArray)
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det f = O s) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) :
    (readBy ask S seen b i).det f = Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i := by
  have hon : (Run.detHom f).on (Fmt.HM ask) = Fmt.HO O := by
    funext number tree index start bytes
    have e : (fun s => (Run.detHom f).app (ask s)) = O := funext h
    exact ((Run.detHom f).HM ask number tree index start bytes).trans
      ((congrArg (fun a => Fmt.HM (m := Id) a number tree index start bytes) e).trans
        (Fmt.HM_id _ number tree index start bytes))
  rw [← Run.detHom_app f]
  exact (HomX.app_readChainX (Run.detHom f) (Fmt.HM ask) S seen b i).trans
    (congrArg (fun h => Fmt.readChainX (m := Id) h S seen b i) hon)

/-- The same for the generic tree, at a family g with one oracle. -/
theorem readByR_det (g : Rom.Fam (Rom.rom 256)) (ask : ByteArray → OComp 256 ByteArray)
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det (g ()) = O s) (S : Fmt.SpecX)
    (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    (readByR ask S seen b i).det g = Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i :=
  (OComp.det_toRom g (readBy ask S seen b i)).trans (readBy_det (g ()) ask O h S seen b i)

/-- If every `ask s` tosses no coin and asks at most one question, the reader that asks by `ask`
tosses no coin and asks at most `fileNX S * 2` questions on every path. An upper bound; a repeated
question counts again. -/
theorem readByR_bound (ask : ByteArray → OComp 256 ByteArray)
    (h : ∀ s, (Run.qp 256).le (ask s) 1 fun _ => True) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) :
    (readByR ask S seen b i).NoCoin ∧ (readByR ask S seen b i).QueryBound (CostX.fileNX S * 2) :=
  toRom_out (readBy ask S seen b i) (CostX.fileNX S * 2)
    (out_of_qp (readBy ask S seen b i) (CostX.fileNX S * 2)
      (CostX.le_readChainX (Run.qp 256) (Fmt.HM ask) 2
        (fun number tree index start bytes =>
          Run.CostP.HM (Run.qp 256) ask 1 h number tree index start bytes) S seen b i))

end OnBytes.Tie

namespace OnBytes.Slice
open _root_.Iop Rom Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf withinX pinned pinnedAt askPinned askPinnedAt digestStr readByR readByR_det
  readByR_bound)

variable {γ : Type} (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)

/-! ## The checkers -/

/-- `chainChk`'s text with the reader that asks by `ask`. The program does not call it. -/
def chainChkBy (ask : ByteArray → ZKCP.OComp 256 ByteArray)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    OComp (rom 256) (Option (LinkOut 256 ((xdOf S0 stm).L dec))) :=
  match pre x with
  | none => OComp.pure none
  | some (r0, r1, b, i, fin) =>
    if r0.size = 32 ∧ r1.size = 32 ∧ withinX (reStated S0 (stm r0 r1)) = true then
      (readByR ask (reStated S0 (stm r0 r1)) [] b i).bind fun rd =>
        OComp.pure (chainPost S0 stm dec r0 r1 fin rd)
    else OComp.pure none

/-- **The checker with the digest of the parameter bytes as an argument**: `chainChk`'s text, with
pd where `chainChk` has the format's own digest. It asks the oracle for every other hash. -/
def chainChkPd (pd : ByteArray)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    OComp (rom 256) (Option (LinkOut 256 ((xdOf S0 stm).L dec))) :=
  chainChkBy S0 stm dec (askPinnedAt S0.base.params pd) pre x

/-- **The checker that asks the oracle for every hash of the chain's reader**, the digest of the
parameter bytes among them: `chainChk`'s text at `Run.askB`. What stands before the chain, the
statement function and the decision ask nothing; the configuration's digest is not asked for. -/
def chainChkAsk (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    OComp (rom 256) (Option (LinkOut 256 ((xdOf S0 stm).L dec))) :=
  chainChkBy S0 stm dec Run.askB pre x

/-- `chainChk` is `chainChkPd` at the format's own digest of the parameter bytes. -/
theorem chainChk_eq_pd (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (x : γ) :
    chainChk S0 stm dec pre x = chainChkPd S0 stm dec (Fmt.paramsDigest S0.base.params) pre x :=
  rfl

/-- **The checker's text as a plain function of a function O on byte strings**, at the hash that O
induces: nothing is pinned. `chainChkAt O` (OnBytes/Slice/ChainChkAt.lean) is this at `Tie.pinned O
S0.base.params`. -/
def chainChkFn (O : ByteArray → ByteArray)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    Option (LinkOut 256 ((xdOf S0 stm).L dec)) :=
  match pre x with
  | none => none
  | some (r0, r1, b, i, fin) =>
    if r0.size = 32 ∧ r1.size = 32 ∧ withinX (reStated S0 (stm r0 r1)) = true then
      chainPost S0 stm dec r0 r1 fin
        (Fmt.readChainX (m := Id) (Fmt.HO O) (reStated S0 (stm r0 r1)) [] b i)
    else none

/-- `chainChkAt O` is `chainChkFn` at O with the format's digest pinned. -/
theorem chainChkAt_eq_fn (O : ByteArray → ByteArray)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    chainChkAt S0 stm dec O pre x = chainChkFn S0 stm dec (pinned O S0.base.params) pre x := rfl

/-- If at the oracle g every `ask s` gives `O s`, the value at g of the checker that asks by `ask`
is the plain function at O. -/
theorem chainChkBy_det (ask : ByteArray → ZKCP.OComp 256 ByteArray) (g : Fam (rom 256))
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det (g ()) = O s)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkBy S0 stm dec ask pre x).det g = chainChkFn S0 stm dec O pre x := by
  unfold chainChkBy chainChkFn
  cases pre x with
  | none => rfl
  | some p =>
    obtain ⟨r0, r1, b, i, fin⟩ := p
    dsimp only
    by_cases hc : r0.size = 32 ∧ r1.size = 32 ∧ withinX (reStated S0 (stm r0 r1)) = true
    · rw [if_pos hc, if_pos hc, OComp.det_bind, readByR_det g ask O h]
      rfl
    · rw [if_neg hc, if_neg hc]
      rfl

/-- The value at g of the checker that holds pd: the plain function at g's function with pd
pinned. -/
theorem det_chainChkPd_fn (pd : ByteArray) (g : Fam (rom 256))
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkPd S0 stm dec pd pre x).det g =
      chainChkFn S0 stm dec (pinnedAt (oB (g ())) S0.base.params pd) pre x :=
  chainChkBy_det S0 stm dec _ g _ (fun s => Tie.det_askPinnedAt (g ()) S0.base.params pd s) pre x

/-- The value at g of the checker that asks for every hash: the plain function at g's function. -/
theorem det_chainChkAsk_fn (g : Fam (rom 256))
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkAsk S0 stm dec pre x).det g = chainChkFn S0 stm dec (oB (g ())) pre x :=
  chainChkBy_det S0 stm dec _ g _ (fun _ => rfl) pre x

/-! ## At an oracle on bit strings that is made from a function on byte strings -/

/-- For O with answers of 32 bytes: the hash that `bitsOf O` (OnBytes/Slice/ChainChkAt.lean) induces
is the hash that O induces. Nothing is pinned. The two functions on byte strings agree at the
strings of the hash's calls, whose first byte is not the escape of `Run.toBytes`. -/
theorem HO_bitsOf (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) :
    Fmt.HO (oB (bitsOf O ())) = Fmt.HO O := by
  funext n t i st bs
  have hq : ∀ half : UInt8, half = 0 ∨ half = 1 →
      oB (bitsOf O ()) (Fmt.oStr half n t i st bs) = O (Fmt.oStr half n t i st bs) := by
    intro half hh
    show digToBytes (bytesToDig (O (toBytes (bytesToBits (Fmt.oStr half n t i st bs))))) = _
    rw [toBytes_plain _ (plain_oStr half n t i st bs hh), bitsToBytes_bytesToBits,
      digToBytes_bytesToDig _ (hO _)]
  unfold Fmt.HO
  rw [hq 0 (Or.inl rfl), hq 1 (Or.inr rfl)]

/-- **For O with answers of 32 bytes, the asking checker's value at the oracle `bitsOf O` is the
plain function at O.** So every such O is met at a point of the space of oracles on bit strings.
Nothing on soundness; no probability. -/
theorem chainChkAsk_bitsOf (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkAsk S0 stm dec pre x).det (bitsOf O) = chainChkFn S0 stm dec O pre x := by
  rw [det_chainChkAsk_fn]
  unfold chainChkFn
  rw [HO_bitsOf O hO]

/-- The asking checker's value at `Run.oBits`, the library's oracle on bit strings that is made from
the format's hash, is the plain function at the format's oracle. -/
theorem chainChkAsk_oBits
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkAsk S0 stm dec pre x).det oBits = chainChkFn S0 stm dec Fmt.oracle pre x :=
  chainChkAsk_bitsOf S0 stm dec Fmt.oracle Fmt.size_oracle pre x

/-! ## The table put over the oracle -/

/-- The bit string at which the asking checker asks for the digest of `params`. -/
def s0Of (params : ByteArray) : List Bool := bytesToBits (digestStr params)

/-- At a byte string s: the oracle with a table put over it at a set S that holds `s0Of params`, as
a function on byte strings, is g's function with the table's value pinned, unless the bits of s are
another string of S. -/
theorem oB_over_at (S : Finset (List Bool)) (T : List Bool → Dig 256) (g : Fam (rom 256))
    (params : ByteArray) (h0 : s0Of params ∈ S) (s : ByteArray)
    (hs : ¬ (bytesToBits s ∈ S ∧ s ≠ digestStr params)) :
    oB ((over S T g) ()) s = pinnedAt (oB (g ())) params (digToBytes (T (s0Of params))) s := by
  unfold pinnedAt
  by_cases e : s = digestStr params
  · rw [if_pos e, e]
    show digToBytes (over S T g () (s0Of params)) = _
    rw [over_mem T g h0]
  · rw [if_neg e]
    show digToBytes (over S T g () (bytesToBits s)) = digToBytes (g () (bytesToBits s))
    rw [over_not_mem T g fun hm => hs ⟨hm, e⟩]

/-- **The oracle with a table put at `s0Of params` alone**, as a function on byte strings, is g's
function with the table's value pinned at the string of the call that hashes `params`. -/
theorem oB_over (T : List Bool → Dig 256) (g : Fam (rom 256)) (params : ByteArray) :
    oB ((over {s0Of params} T g) ()) =
      pinnedAt (oB (g ())) params (digToBytes (T (s0Of params))) :=
  funext fun s => oB_over_at {s0Of params} T g params (Finset.mem_singleton_self _) s
    fun h => h.2 (bytesToBits_inj (Finset.mem_singleton.1 h.1))

/-- **The checker that holds the table's value has, under g, the value that the asking checker has
under g with the table put at `s0Of params`.** Values alone: `pinOn` (OnBytes/Slice/AtSet.lean) is
not used. Both sides may be "no". No bound is stated here for either checker. -/
theorem det_chainChkPd (T : List Bool → Dig 256) (g : Fam (rom 256))
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkPd S0 stm dec (digToBytes (T (s0Of S0.base.params))) pre x).det g =
      (chainChkAsk S0 stm dec pre x).det (over {s0Of S0.base.params} T g) := by
  rw [det_chainChkPd_fn, det_chainChkAsk_fn, oB_over]

/-- The value of F at a function on byte strings does not depend on that function's values at the
strings of B. -/
def ReadsNot {α : Type} (F : (ByteArray → ByteArray) → α) (B : Set ByteArray) : Prop :=
  ∀ O O' : ByteArray → ByteArray, (∀ s, s ∉ B → O s = O' s) → F O = F O'

/-- **The same for a larger set S that holds `s0Of params`, UNDER A HYPOTHESIS**: on this input the
plain function does not read its argument at the byte strings whose bits are other strings of S.
That hypothesis is proved of nothing here: see the head. -/
theorem det_chainChkPd_of (S : Finset (List Bool)) (T : List Bool → Dig 256) (g : Fam (rom 256))
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ)
    (h0 : s0Of S0.base.params ∈ S)
    (hfree : ReadsNot (fun O => chainChkFn S0 stm dec O pre x)
      {s | bytesToBits s ∈ S ∧ s ≠ digestStr S0.base.params}) :
    (chainChkPd S0 stm dec (digToBytes (T (s0Of S0.base.params))) pre x).det g =
      (chainChkAsk S0 stm dec pre x).det (over S T g) := by
  rw [det_chainChkPd_fn, det_chainChkAsk_fn]
  exact (hfree _ _ fun s hs => oB_over_at S T g S0.base.params h0 s hs).symm

/-! ## No coin, and the count -/

/-- If every `ask s` tosses no coin and asks at most one question, the checker that asks by `ask`
tosses no coin and asks the oracle at most `CostX.fileNX S0 * 2` strings, whatever the maker's
output. -/
theorem chainChkBy_bound (ask : ByteArray → ZKCP.OComp 256 ByteArray)
    (h : ∀ s, (Run.qp 256).le (ask s) 1 fun _ => True)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkBy S0 stm dec ask pre x).NoCoin ∧
      (chainChkBy S0 stm dec ask pre x).QueryBound (Tie.CostX.fileNX S0 * 2) := by
  unfold chainChkBy
  split
  · exact ⟨trivial, trivial⟩
  · rename_i r0 r1 b i fin _
    split
    · have hb := readByR_bound ask h (reStated S0 (stm r0 r1)) [] b i
      rw [Tie.CostX.fileNX_congr (reStated S0 (stm r0 r1)) S0 rfl rfl] at hb
      refine ⟨hb.1.bind fun _ => trivial, ?_⟩
      have h2 : ((readByR ask (reStated S0 (stm r0 r1)) [] b i).bind fun rd =>
          OComp.pure (chainPost S0 stm dec r0 r1 fin rd)).QueryBound
            (Tie.CostX.fileNX S0 * 2 + 0) := hb.2.bind fun _ => trivial
      exact h2
    · exact ⟨trivial, trivial⟩

/-- The checker that holds pd tosses no coin and asks at most `CostX.fileNX S0 * 2` strings. -/
theorem chainChkPd_bound (pd : ByteArray)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChkPd S0 stm dec pd pre x).NoCoin ∧
      (chainChkPd S0 stm dec pd pre x).QueryBound (Tie.CostX.fileNX S0 * 2) :=
  chainChkBy_bound S0 stm dec _ (Tie.qp_askPinnedAt S0.base.params pd) pre x

/-- The checker that asks for every hash tosses no coin and asks at most `CostX.fileNX S0 * 2`
strings. -/
theorem chainChkAsk_bound (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (x : γ) : (chainChkAsk S0 stm dec pre x).NoCoin ∧
      (chainChkAsk S0 stm dec pre x).QueryBound (Tie.CostX.fileNX S0 * 2) :=
  chainChkBy_bound S0 stm dec _ Tie.qp_askB pre x

end OnBytes.Slice
