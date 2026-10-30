-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3X.lean: the protocol in three stretches with an instance, written into the
sibling's oracles, and the compiler's conclusion for it from soundness instance by instance.

"The library" is the Lean library of the soundness road (Iop/, Compile/, Run/); "the sibling" is a
second form of that road under OnBytes/TypedOracleCompiler/.

Why. `Plain3 G dec` (OnBytes/TypedOracleCompiler/Slice/Plain3.lean) has no instance, and
OnBytes/TypedOracleCompiler/Slice/Plain3Strings.lean writes it into an interface as that interface's Test. Where a
file's statement holds values that its maker chooses (a stored table's record), these have to be an
instance that the first query holds. The library's interface (`Iop.BatchProtocol`) has a Test without an
instance; its Batch has one. So the protocol is laid into the field for Batch, with every round
local and one slot. The compiled verifier fixes a round's query from the round's kind and the
chain's phase alone (`actOf`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), so with local rounds alone
it asks what it asks for a Test, under the tag of Batch, with `early x` in the first query; the
check in the request tree is made only if the chain has joined a shared round (`afterB`), which it
never does here.
 - `Plain3X G dec`, dec : X → three views → Bool: shape and what is read are `Plain3`'s; at x it
   accepts as `Plain3 G (dec x)`;
 - `plain3X_local`; `plain3X_sound_iff`: it is round-by-round sound for Lg with the counts ε exactly
   if for each x `Plain3 G (dec x)` is sound for Lg x with the same ε;
 - `wq3X`, `wq3X_okg`: the maker's wiring of `Plain3`, lawful if that is;
 - `LX3`, `WX3`, `ZX3`: the interface (one slot; what of an instance the first query holds, `early`,
   is a parameter; no later query holds the instance; ITS TEST IS A PARAMETER T, a second protocol
   on the same external string, with its wiring and ways of writing: at a tag whose protocol has no
   round the type of challenge queries is empty, so a second chain that is to be typed in the same
   world needs a protocol there), a wire with bodies that are strings, the written batch protocol;
 - `ZX3_ok`: it meets all that OnBytes/TypedOracleCompiler/Slice/BatchClause.lean asks, IF the wiring is lawful and
   no tree of the three stretches is deeper than 63;
 - `batchAtX3_reply`: the compiler's conclusion from `ReplyLost` at any `early`, IF every count is
   at most the share e, the wiring is lawful and no tree is deeper than 63; `batchAtX3`,
   `judgeAtX3`: under the same three conditions, at `early := id`, from soundness instance by
   instance, and the same as a judge's (OnBytes/TypedOracleCompiler/Slice/BatchJudge.lean), with the strict format;
 - `wq3X_okg_pull`: with challenges as hash blocks (at `G.atP f`) the wiring is lawful, IF K blocks
   are enough for every round and no round has more than 64 bits of work. What is then asked is
   soundness at hash blocks.

Main definitions: `Plain3X`, `wq3X`, `LX3`, `WX3`, `ZX3`.
Main theorems: `plain3X_local`, `plain3X_sound_iff`, `wq3X_okg`, `ZX3_ok`, `batchAtX3_reply`,
`batchAtX3`, `judgeAtX3`, `wq3X_okg_pull`.

Not claimed. NO SOUNDNESS IS PROVED: `ReplyLost`, or that `Plain3 G (dec x)` is sound for each x
with one list of counts, is a hypothesis. ONE G FOR ALL x: shape, rounds and openings do not hang on
the instance; that a file's rounds are the same for every instance is not shown. The decision gets
the same x of which the first query holds `early x`: where a part of x stands in no hash input of a
file, `early` has to forget it, and then `ReplyLost` asks much more than soundness instance by
instance: the forgotten part is free until the end of the transcript, and one list of counts has to
serve all its values. For a decision that tests an equation in the forgotten part this can be false,
and `batchAtX3_reply` is then an implication from a false hypothesis. Nothing is asked or shown of
T: no theorem here reads it. No X, no decision, no language and no stretches are given: nothing
speaks of a record, of a key file, of any file, or of the program. How the typed first query is
spelled as a string of bytes is not said here. That the compiled verifier is the sibling's own for
Batch, a named set of bad traces, and what a leaf query is written as (`Z3_verifier`, `lang3S`,
`leaf_query3` of Plain3Strings.lean for the protocol without an instance) are not said again. The
written protocol could as well stand under the tag of Test in an interface with instances: not done.
What the heads of BatchClause.lean and Plain3Strings.lean do not claim. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ReplyClause
import OnBytes.TypedOracleCompiler.Slice.Plain3Strings

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (ReplyLost replyLost_id_iff below_timesShared_one)
open scoped ENNReal

variable {X : Type} (G : Stretches) (dec : X → PQ.View → PQ.View → PQ.View → Bool)

/-! ## The protocol -/

/-- The protocol in three stretches, with an instance: shape and what is read are `Plain3`'s,
which do not look at the decision; at the instance x it accepts as `Plain3 G (dec x)` does. -/
@[reducible] def Plain3X : InteractiveOracleProof X (oneExternalString (2 ^ G.a) PQ.SgX) where
  shape := G.sh
  blinded := (Plain3 G fun _ _ _ => true).blinded
  extReads := fun _ ρ => (Plain3 G fun _ _ _ => true).extReads () ρ
  reads := fun _ ρ π => (Plain3 G fun _ _ _ => true).reads () ρ π
  accept := fun x y τ => (Plain3 G (dec x)).accept () y τ

/-- The verifier is local, for every decision. -/
theorem plain3X_local : (Plain3X G dec).IsLocal :=
  fun x y y' τ τ' hρ hp he hr => plain3_local G (dec x) () y y' τ τ' hρ hp he hr

/-- Soundness is soundness instance by instance, with one list of counts. -/
theorem plain3X_sound_iff (Lg : X → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (ε : Err G.sh) :
    (Plain3X G dec).Sound Lg ε ↔ ∀ x, (Plain3 G (dec x)).Sound (fun _ => Lg x) ε :=
  ⟨fun h x _ y hn => h x y hn, fun h x y hn => h x () y hn⟩

/-! ## The wiring -/

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones)

/-- The maker's wiring of `Plain3`: its fields do not look at the decision. -/
def wq3X : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (Plain3X G dec)) :=
  ⟨G.wires K chal o, we1 G.a, G.decO, G.nOpen, G.maxDepth⟩

/-- It is lawful if `Plain3`'s is, at any decision. -/
theorem wq3X_okg (d : PQ.View → PQ.View → PQ.View → Bool) (h : (wq3 G K chal o d).OKG) :
    (wq3X G dec K chal o).OKG :=
  ⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩

/-! ## The interface, the wire, the written protocol -/

/- salt: the length of a file's salt, in bytes; early: what of an instance the first query holds; T:
the interface's Test, a second protocol on the same external string, without an instance -/
variable (salt : ℕ) (early : X → X) (T : InteractiveOracleProof Unit (oneExternalString (2 ^ G.a) PQ.SgX))

/-- The interface whose Batch is the protocol with an instance, all rounds local, at one slot: one
external string of 2 ^ a symbols; its Test is the given protocol T; Link has no round; the first
query of Batch holds `early x` of an instance x, and no later query holds the instance; the honest
sides are the library's dummies. (The library's interface has an instance at Batch alone: its Test
is a protocol without one.) -/
@[reducible] def LX3 : _root_.Iop.BatchProtocol Unit X where
  wordLength := 2 ^ G.a
  Symbol := PQ.SgX
  EncodingRandomness := Unit
  encodeIndex := fun _ _ p => (p.val, [])
  decodeIndex := fun _ => some ()
  offline := T
  link := { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
            reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto (Plain3X G dec)
  honestOfflineProver := _root_.Run.dummyH _ fun _ p => (p.val, [])
  honestLinkProver := _root_.Run.dummyH _ fun _ => (fun p => (p.val, []), fun p => (p.val, []))
  honestOnlineBatchProver := _root_.Run.dummyB _ fun _ p => (p.val, [])
  early := early
  late := none

/- wT, eT, pT: Test's wiring and its two ways of writing a symbol -/
variable (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)
  (wT : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → List Bool)
  (pT : (p : OPos T.shape) → List Bool → Option (OSym T.shape p))

/-- A wire of the sibling at that interface, with bodies that are strings. Test's wiring and ways of
writing are given from outside; nothing is asked of them here. -/
def WX3 : QueryLayout 256 (Strings.strung (LX3 G dec early T)) where
  K := K + 1
  T := wT
  Lk := ⟨(), { WireE.two (2 ^ G.a) PQ.SgX (0, []) with depth := G.a },
    inferInstanceAs (DecidableEq Empty), 0, G.a⟩
  B := wq3X G dec K chal o
  depth := G.a
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := embE
  prjE := prjE
  embT := eT
  prjT := pT
  embL := fun p _ => p.elim
  prjL := fun p _ => p.elim
  embB := G.embS salt
  prjB := G.prjS salt

/-- The protocol with an instance, written into the sibling's oracles: under the tag of Batch;
plain parts as they are; symbols as their leaves' own strings. -/
def ZX3 : WrittenB (WX3 G dec K chal o salt early T embE prjE wT eT pT) where
  t := Tag.onl
  Q := BatchInteractiveOracleProof.ofProto (Plain3X G dec)
  wq := wq3X G dec K chal o
  embS := G.embS salt
  prjS := G.prjS salt
  embP := id
  prjP := some

/-- It meets what is asked of a written batch protocol, if the maker's wiring is lawful and no
tree is deeper than 63. -/
theorem ZX3_ok (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG) :
    (ZX3 G dec K chal o salt early T embE prjE wT eT pT).OK :=
  ⟨G.back salt hs, fun _ => rfl, hw, plain3X_local G dec,
    _root_.Iop.BatchOne.BAnn.allLocal_coherent _, (fun _ h => by cases h), rfl,
    fun p => ⟨we1_which G.a p, we1_leaf G.a p⟩⟩

/-- The clause, for any early part. IF for every early part and every external string the prover
has lost at the start towards "every instance with this early part that the verifier accepts is in
the language" (`ReplyLost`, OnBytes/Slice/ReplyState.lean), with counts that are each at most the
share e, the maker's wiring is lawful (at sampled values it is not, wherever a field element is
drawn: see the head of OnBytes/TypedOracleCompiler/Slice/Plain3Strings.lean) and no tree is deeper than 63, THEN the
compiler's conclusion for that language and any reading. -/
theorem batchAtX3_reply (R : Reading (Strings.strung (LX3 G dec early T)) embE)
    (Lg : X → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (εs : ℝ≥0∞) (ε : Err G.sh)
    (hb : Err.Below ε εs) (hS : ReplyLost (Plain3X G dec) ε early Lg)
    (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG) :
    BatchAt (ZX3 G dec K chal o salt early T embE prjE wT eT pT) R Lg εs := by
  have h1 : Err.Below (Err.timesShared 1 (RoundSplits.allLocal G.sh) ε) (((1 : ℕ) : ℝ≥0∞) * εs) :=
    below_timesShared_one le_rfl _ ε εs hb
  rw [Nat.cast_one, one_mul] at h1
  exact batchAt_reply (ZX3 G dec K chal o salt early T embE prjE wT eT pT) R Lg εs ε rfl hS h1
    (ZX3_ok G dec K chal o salt early T embE prjE wT eT pT hs hw) rfl

/-- The clause where the first query holds the whole instance: IF for each instance x the
protocol `Plain3 G (dec x)` is round-by-round sound for the language Lg x, with one list of counts
that are each at most the share e, the maker's wiring is lawful (see `batchAtX3_reply`) and no tree
is deeper than 63, THEN the compiler's conclusion for Lg and any reading. -/
theorem batchAtX3 (R : Reading (Strings.strung (LX3 G dec id T)) embE)
    (Lg : X → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (εs : ℝ≥0∞) (ε : Err G.sh)
    (hb : Err.Below ε εs) (hS : ∀ x, (Plain3 G (dec x)).Sound (fun _ => Lg x) ε)
    (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG) :
    BatchAt (ZX3 G dec K chal o salt id T embE prjE wT eT pT) R Lg εs :=
  batchAtX3_reply G dec K chal o salt id T embE prjE wT eT pT R Lg εs ε hb
    (replyLost_id_iff.2 ((plain3X_sound_iff G dec Lg ε).2 hS)) hs hw

/-- `batchAtX3` as what a part of the join asks of its judge, for the verifier with the strict
format. -/
theorem judgeAtX3 (R : Reading (Strings.strung (LX3 G dec id T)) embE)
    (Lg : X → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (sMT sFS : ℕ) (εs : ℝ≥0∞) (ε : Err G.sh)
    (hb : Err.Below ε εs) (hS : ∀ x, (Plain3 G (dec x)).Sound (fun _ => Lg x) ε)
    (hs : G.Shallow) (hw : (wq3X G dec K chal o).OKG) :
    JudgeAt (WX3 G dec K chal o salt id T embE prjE wT eT pT)
      (judgeBS (ZX3 G dec K chal o salt id T embE prjE wT eT pT) R Lg sMT sFS) εs :=
  judgeAt_BS _ R Lg sMT sFS (ZX3_ok G dec K chal o salt id T embE prjE wT eT pT hs hw) εs
    (batchAtX3 G dec K chal o salt T embE prjE wT eT pT R Lg εs ε hb hS hs hw)

/-- With challenges as hash blocks the wiring is lawful, if K blocks are enough for every round
and no round has more than 64 bits of work. -/
theorem wq3X_okg_pull (f : Fmt.Fld) (o' : (G.atP f).Ones)
    (hK : ∀ d ∈ G.ds₁ ++ (G.ds₂ ++ G.ds₃), (_root_.Run.bsRound f d.entry d.kind).b ≤ K)
    (hwk : ∀ d ∈ G.ds₁ ++ (G.ds₂ ++ G.ds₃), d.entry.work ≤ 64) :
    (wq3X (G.atP f) dec K (_root_.Run.chalP f K) o').OKG :=
  wq3X_okg (G.atP f) dec K (_root_.Run.chalP f K) o' (fun _ _ _ => true)
    (wq3_okg_pull G f K o' (fun _ _ _ => true) hK hwk)

end TypedOracleCompiler.Slice
