-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/OneOracle.lean: the two roads over the sibling joined in one statement: what the
strict reader with stored tables has read, the compiled verifier's run over the one oracle accepts,
if the decision does.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

The two roads. (1) OnBytes/TypedOracleCompiler/Run/StoredChain.lean to StoredMain.lean (`stored_core`): what the
reader, at the hash of a function O on byte strings, has read, the evaluable form of the compiled
verifier accepts at the typed oracle functions `famXPd .. O`. (2) OnBytes/TypedOracleCompiler/Run/PageXFit.lean to
PageXRead.lean (`read_verifyBSPd`): the run of `verifyOneProtocol` at `famXPd .. (oB (g ()))` is its run at
the family that the encoding reads out of a function g on bit strings. `thin_verify` ties the
evaluable form to `verifyOneProtocol`. The step between: the reader asks for the digest of the parameter
bytes, a call number 169, and the first query's string holds that digest; so the reader stands at
g's function with that one string pinned at pd, and the typed oracle functions do not see the pin:
no typed query is spelled as a call number 169 (`famXPd_pinnedAt`).

After OnBytes/Tie/DigestPoint.lean (18 declarations by the cut of declarations). The pinned value is
an argument, where the original has the format's digest of the parameter bytes.
As text, but for `_root_.` before `Fmt.` and the new arguments (5). `size_fit`, `size_pblock_any`,
`oStr_number`, `oStr_ne_digestStr`, `fbCallX_number`.
Turned (4).
 `HO_pinnedAt_digest` the original's `digestAt_pinned`, with the value as an argument.
 `famXPd_pinnedAt`  the original's `famX_pinned`, with the value as an argument, at every pd; here
     an instance of `famXPd_agree`.
 `firstXPd_number`  the original's `firstX_number`, at every pd.
 `leafX_number`  by cases on `B.getE q.body`, where the original goes by the body's constructor.
Also (2).
`ansOf_agree`, `famXPd_agree`: two functions
that agree off the calls with the number 169 induce one family. The original's `ansOf_pinned` is not
said: `pinnedAt_agree` (new) stands for it.
Said elsewhere over the sibling (3): `digestStr`, and `pinned`, `size_pinned` as `pinnedAt`,
`size_pinnedAt` (OnBytes/TypedOracleCompiler/Run/PageXTop.lean). Not said (5): `HO_pinned`, `size_oB`,
`readInPinned_compiled`, `pinned_oracle`, `readInPinned_oracle`.
New (2): `pinnedAt_agree`, and
 `read_accepts_oneOracle`  the join. In OnBytes/ the like is spread over
     OnBytes/Tie/DigestPoint.lean (`readInPinned_compiled`), OnBytes/Tie/PageXTop.lean and
     OnBytes/Slice/.

What is not said. One encoding for all roots: not here: OnBytes/TypedOracleCompiler/Run/AllRoots.lean. The join here
stands at one description S, under which the reader reads and at which the encoding is written; S
holds the statement, and the statement holds the roots. One direction: an implication between two
yeses. That the reader reads any file. That any description, bodies or statement's reader meet the
hypotheses. pd is any 256 bits: nothing ties it to the parameter bytes. Nothing on soundness; no
probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.StoredMain

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

/-! ## The number of a call, read off its string -/

/-- `Fmt.fit n` gives n bytes. -/
theorem size_fit (n : ℕ) (b : ByteArray) : (_root_.Fmt.fit n b).size = n := by
  unfold _root_.Fmt.fit
  split
  · rw [ByteArray.size_extract]
    omega
  · rw [ByteArray.size_append, _root_.Fmt.size_zeros]
    omega

/-- The parameter block has 64 bytes, whatever the start. -/
theorem size_pblock_any (n : ℕ) (s : ByteArray) : (_root_.Fmt.pblock n s).size = 64 := by
  unfold _root_.Fmt.pblock
  rw [ByteArray.size_append, ByteArray.size_append, _root_.Fmt.size_four, _root_.Fmt.size_zeros,
  size_fit]

/-- The lowest 16 bits of the word at byte 65 of a call's string are the call's number modulo 65536.
No condition on the arguments. -/
theorem oStr_number (h : UInt8) (n t i : ℕ) (s b : ByteArray) :
    (_root_.Fmt.wordAt (_root_.Fmt.oStr h n t i s b) 65).toNat % 65536 = n % 65536 := by
  have h1 := _root_.Fmt.wordAt_mid (⟨#[h]⟩ ++ _root_.Fmt.pblock n s) (_root_.Fmt.label n t i) b 0
    (by have := _root_.Fmt.size_label n t i; omega)
  rw [ByteArray.size_append, _root_.Fmt.size_one, size_pblock_any] at h1
  have h2 := _root_.Fmt.wordAt_mid ByteArray.empty (_root_.Fmt.u64n (n + 65536 * t))
    (_root_.Fmt.u64n i) 0 (by have := _root_.Fmt.size_u64n (n + 65536 * t); omega)
  rw [ByteArray.empty_append, ByteArray.size_empty] at h2
  have h3 : _root_.Fmt.wordAt (_root_.Fmt.oStr h n t i s b) 65 = _root_.Fmt.wordAt (_root_.Fmt.u64n
    (n + 65536 * t)) 0 := Eq.trans h1 h2
  rw [h3]
  unfold _root_.Fmt.u64n
  rw [_root_.Fmt.wordAt_u64, UInt64.toNat_ofNat']
  omega

/-! ## One string pinned -/

/-- The string of a call whose number is not 169 modulo 65536 is not the pinned string. -/
theorem oStr_ne_digestStr (h : UInt8) (n t i : ℕ) (s b params : ByteArray)
    (hn : n % 65536 ≠ 169) : _root_.Fmt.oStr h n t i s b ≠ digestStr params := by
  intro e
  have h1 := oStr_number h n t i s b
  have h2 := oStr_number 0 169 0 1 _root_.Fmt.zero32 params
  unfold digestStr at e
  rw [e, h2] at h1
  exact hn (by omega)

/-- The hash that `pinnedAt O params pd` induces gives pd as the digest of `params`. -/
theorem HO_pinnedAt_digest (O : ByteArray → ByteArray) (params pd : ByteArray) :
    _root_.Fmt.HO (pinnedAt O params pd) 169 0 1 _root_.Fmt.zero32 params = pd := by
  unfold _root_.Fmt.HO
  rw [if_neg (by decide)]
  show (if _root_.Fmt.oStr 0 169 0 1 _root_.Fmt.zero32 params = digestStr params then
    pd else O _) = _
  exact if_pos rfl

/-- At a call whose number is not 169 modulo 65536, and where there is no call, two functions that
agree at every such call give the same answer. -/
theorem ansOf_agree (O O' : ByteArray → ByteArray)
    (h : ∀ q : _root_.Fmt.OQ, q.number % 65536 ≠ 169 → O (strOf q) = O' (strOf q))
    (c : Option _root_.Fmt.OQ) (hc : ∀ q, c = some q → q.number % 65536 ≠ 169) :
    ansOf O c = ansOf O' c := by
  cases c with
  | none => rfl
  | some q =>
    show bytesToDig (O (strOf q)) = bytesToDig (O' (strOf q))
    rw [h q (hc q rfl)]

/-- `pinnedAt O params pd` and O agree at every call whose number is not 169 modulo 65536. -/
theorem pinnedAt_agree (O : ByteArray → ByteArray) (params pd : ByteArray) (q : _root_.Fmt.OQ)
    (hq : q.number % 65536 ≠ 169) : pinnedAt O params pd (strOf q) = O (strOf q) := by
  have hne : strOf q ≠ digestStr params :=
    oStr_ne_digestStr q.half q.number q.tree q.index q.start q.bytes params hq
  unfold pinnedAt
  rw [if_neg hne]

/-! ## No typed query is a call number 169 -/

section
variable {Bd : Type} (B : BodyD Bd) (D : XD) (dec : View → Bool)

/-- `fbCall` spells a chain query as a call number 160 or 162. -/
theorem fbCallX_number (K : ℕ) (q : FbIn 256 (D.L Bd dec) .link)
    (j : Fin (K + 1)) (c : _root_.Fmt.OQ) (h : fbCall (PDX B D dec) K q j = some c) :
    c.number = 160 ∨ c.number = 162 := by
  unfold fbCall at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact Or.inl rfl
    · cases h
  · injection h with h
    subst h
    exact Or.inr rfl
  · cases h

/-- A chain query is spelled as a call number 160 or 162. -/
theorem firstXPd_number (pd : ByteArray) (K : ℕ) (q : FbIn 256 (D.L Bd dec) .link)
    (j : Fin (K + 1)) (c : _root_.Fmt.OQ) (h : firstXPd B D dec pd K q j = some c) :
    c.number = 160 ∨ c.number = 162 := by
  unfold firstXPd at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact Or.inl rfl
    · cases h
  · cases h
  · exact fbCallX_number B D dec K q j c h

/-- A leaf query is spelled as a call number 164 or 174. -/
theorem leafX_number (q : LeafIn (D.L Bd dec)) (c : _root_.Fmt.OQ)
    (h : leafX B D dec q = some c) : c.number = 164 ∨ c.number = 174 := by
  unfold leafX at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact Or.inr rfl
    · cases h
  · unfold leafCall at h
    obtain ⟨s, -, hs⟩ := Option.map_eq_some_iff.1 h
    subst hs
    exact Or.inl rfl

/-- Two functions on byte strings that agree at every call whose number is not 169 modulo 65536
induce the same typed oracle functions, at every pd: no typed query is spelled as a call with that
number. -/
theorem famXPd_agree (pd : ByteArray) (O O' : ByteArray → ByteArray)
    (h : ∀ q : _root_.Fmt.OQ, q.number % 65536 ≠ 169 → O (strOf q) = O' (strOf q)) (K : ℕ) :
    famXPd B D dec pd O K = famXPd B D dec pd O' K := by
  funext o
  match o with
  | .leaf =>
    funext q
    exact ansOf_agree O O' h _ fun c hc => by
      rcases leafX_number B D dec q c hc with h | h <;> rw [h] <;> decide
  | .node =>
    funext q
    exact ansOf_agree O O' h (nodeCallC D.base.cfg q) fun c hc => by
      have h : c.number = 166 := by
        unfold nodeCallC at hc
        injection hc with hc
        subst hc
        rfl
      rw [h]
      decide
  | .fb .link =>
    funext q
    refine Prod.ext (funext fun k => ?_) ?_
    · exact ansOf_agree O O' h _ fun c hc => by
        rcases firstXPd_number B D dec pd K q _ c hc with h | h <;> rw [h] <;> decide
    · exact ansOf_agree O O' h _ fun c hc => by
        rcases firstXPd_number B D dec pd K q _ c hc with h | h <;> rw [h] <;> decide
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

/-- So the typed oracle functions that `pinnedAt O params v` induces are those that O induces, at
every pd, v and `params`. -/
theorem famXPd_pinnedAt (pd : ByteArray) (O : ByteArray → ByteArray) (params v : ByteArray)
    (K : ℕ) : famXPd B D dec pd (pinnedAt O params v) K = famXPd B D dec pd O K :=
  famXPd_agree B D dec pd _ _ (pinnedAt_agree O params v) K

end

/-! ## The two roads joined -/

section
variable {Bd : Type} (B : BodyD Bd) (S : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (Lf : LeafD (xdOf S stm) B) (dec : View → Bool)
  (hcfg : S.base.cfg.size = 32) (V : StmInv (xdOf S stm))
  (embS : (p : OPos (Twin.up (SOf (xdOf S stm).C (xdOf S stm).ds))) →
    OSym (Twin.up (SOf (xdOf S stm).C (xdOf S stm).ds)) p → Bd)

/-- What the strict reader with stored tables has read, the compiled verifier's run over the one
oracle accepts, if the decision does. g is any function on bit strings, pd any 256 bits. The reader
stands at the hash of the function that g induces on byte strings, but for the one string of the
call that hashes the parameter bytes, which is answered with the bytes of pd. If it has read o under
S, from any byte and under any record of vertices, and the decision says yes on o's view, then the
sibling's typing makes a string π of o, and the run of the sibling's `verifyOneProtocol` on π under the two
roots, at the family that the encoding `implAtPd .. pd` reads out of g, says yes. The other
hypotheses: r0 and r1 have 32 bytes; S's statement is `stm r0 r1`, of fewer than 2^64 bytes, and its
items hold the roots; the description is within the sibling's limits (`XD.ok`) and the bounds
`FitsS`; the chain has random bytes; each table is opened at most once; the configuration's digest
has 32 bytes; a reader for the statement (`StmInv`); of bodies: `LeafD`, `OwnFits`, and `hi`: the
body of every own symbol is spelled as the format spells its leaf. One description: the encoding is
written at S, which holds the statement; that it does not move with the roots is not said here. An
implication between two yeses: nothing on soundness; no probability. -/
theorem read_accepts_oneOracle (pd : Dig 256) (F : FitsS (xdOf S stm).base (xdOf S stm).K)
    (hOwn : OwnFits B (xdOf S stm) Lf embS)
    (hi : ∀ p a, B.own (embS (.inr p) a) =
      some (leafSL (xdOf S stm).C S.base.plan.salt (xdOf S stm).ds ⟨p, a⟩))
    (hok : (xdOf S stm).ok = true) (hn : S.base.rand.isNone = false)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (g : Fam (rom 256)) (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hst : S.base.statement = stm r0 r1) (hlen : (stm r0 r1).size < 2 ^ 64)
    (hroot : ∀ t ∈ S.stored.flatten,
      _root_.Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id)
      (_root_.Fmt.HO (pinnedAt (oB (g ())) S.base.params (digToBytes pd))) S seen b i =
        some (o, j))
    (hdec : dec (_root_.Fmt.viewX S o) = true) :
    ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec).up,
      toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
        (xdOf S stm).xs dec o = some π ∧
      (verifyOneProtocol (lam := 256) (K := (xdOf S stm).K + 1) (L := (xdOf S stm).L Bd dec)
        (256 + 8 * S.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec).up
        (wX (xdOf S stm) dec) embS (embX Bd (xdOf S stm) dec)
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
        (readBlocks (implAtPd B S stm Lf dec hcfg V pd) g) = true := by
  have hO : ∀ s, (pinnedAt (oB (g ())) S.base.params (digToBytes pd) s).size = 32 :=
    size_pinnedAt _ (fun _ => size_digToBytes _) _ _ (size_digToBytes _)
  have hokb : PQ.ok (inFile S.base) = true := by
    have hok' := hok
    unfold XD.ok at hok'
    simp only [Bool.and_eq_true] at hok'
    exact hok'.1.1
  obtain ⟨π, t1, t2⟩ := stored_core S stm dec
    (pinnedAt (oB (g ())) S.base.params (digToBytes pd)) hO B (digToBytes pd) embS r0 r1 h0 h1 hok
    hn honce hst hroot (HO_pinnedAt_digest _ _ _) hi (fun p a => hOwn.notStored (.inr p) a)
    seen b i o j e hdec
  rw [famXPd_pinnedAt] at t2
  refine ⟨π, t1, ?_⟩
  have E := read_verifyBSPd (xdOf S stm) dec B Lf embS pd hcfg V F hOwn g S rfl
    (pinnedAt (oB (g ())) S.base.params (digToBytes pd)) hO
    (own_of_ok (inFile S.base) hokb) hn seen b i o j e
    (bytesToDig r0) (bytesToDig r1)
    (by
      rw [_root_.Run.TieTree.dig_bytes _ h0, _root_.Run.TieTree.dig_bytes _ h1]
      exact hlen) π t1
  refine E.symm.trans ?_
  rw [← thin_verify Unit Unit 256 _ ((xdOf S stm).L Bd dec)
    (famXPd B (xdOf S stm) dec (digToBytes pd) (oB (g ())) ((xdOf S stm).K + 1)) Unit _ _ 256 .link
    _ _ _ _ (fun _ => none) B.embE 0 _ () π]
  exact t2

end

end TypedOracleCompiler.Run.PQ
