-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3Strings.lean: the protocol in three stretches, written into the sibling's
oracles with bodies that are strings; and the clause for it.

OnBytes/TypedOracleCompiler/Slice/Plain3.lean has a protocol in three stretches of written rounds with four seams,
on one external string, for any decision on three views; over the sibling's rounds' data a written
round may send SEVERAL trees. OnBytes/TypedOracleCompiler/Slice/Plain3Wire.lean has its wiring, made by the
sibling's maker, with its laws. This file gives what was missing between these and the clause of
OnBytes/TypedOracleCompiler/Slice/PlainClause.lean:
 - an interface whose Test is that protocol (`L3`), with bodies that are strings;
 - the way of writing a symbol of the protocol's oracles into a leaf's body: its leaf's own string
   (`Stretches.embS`, `Stretches.prjS`; tree by tree as in OnBytes/TypedOracleCompiler/StringsList.lean). If no tree
   is deeper than 63: what is written is read back (`Stretches.back`); the body is the bits of the
   format's label, with the position's OWN tree's numbers, and of column and fill
   (`Stretches.embS_fit`); a leaf query on a symbol whose body passes the code's test is written,
   with the bits of `Fmt.oStr` at the number 164 (`leaf_query3`);
 - a wire of the sibling at that interface (`W3`), its stored symbols' way of writing GIVEN from
   outside;
 - the written protocol (`Z3`); its compiled verifier is the sibling's `vT` at that wire
   (`Z3_verifier`), with the strict format `vTS` (`Z3_verifierS`); it meets what is asked of a
   written protocol if the maker's wiring is lawful (`Z3_ok`);
 - `plainAt3`, AN IMPLICATION: IF the protocol is round-by-round sound for a language, with every
   error at most e, and the maker's wiring is lawful, THEN the four clauses of `PlainAt` for that
   language, at any reading. That the verifier is local is the sibling's `plain3_local`.
   `plainAt3_pull`: the same with verifier's messages as hash blocks, where the wiring is lawful
   by the sibling's `wq3_okg_pull`. `lang3S`: the third clause for the sibling's strict verifier
   `vTS` at that wire.

Main definitions: `embApp`, `prjApp`, `leafApp`, `embSeam`, `prjSeam`, `leafSeam`, `embTail`,
`Fits`, `Stretches.Shallow`, `Stretches.embS`, `Stretches.prjS`, `Stretches.leafS`, `L3`, `W3`,
`Z3`.
Main theorems: `back_app`, `back_seam`, `back_L`, `fits_app`, `fits_seam`, `fits_tail`,
`Stretches.back`, `Stretches.embS_fit`, `Z3_verifier`, `leaf_query3`, `Z3_ok`, `plainAt3`,
`Z3_verifierS`, `lang3S`, `plainAt3_pull`.

Not claimed. No stretches are given: nothing here speaks of a key file, of any file, or of the
program; that a key's three chains are such stretches is not shown. That the protocol is sound for
some language is a hypothesis. WHERE THE WIRING CAN BE LAWFUL: `plainAt3` is for any kit of
verifier's messages. One of the wiring's laws says that uniform blocks give a uniform verifier's
message. By the sibling's and the library's own heads (their word, of the format's sampler; no Lean
statement says it) that fails, with verifier's messages as sampled values, wherever a field element
is drawn; where none is drawn it holds there too. So at stretches that draw a field element the
hypothesis of `plainAt3` cannot hold at sampled values; of the library's two kits it holds there at
hash blocks alone, and the soundness asked is then that of the protocol AT BLOCKS (`G.atP f`). In
`plainAt3_pull` the wiring's laws are met from two bounds on the rounds' entries, which are shown at
no stretches here. The stored symbols' way of writing `embE` is a parameter, and nothing is asked of
it here; a reading's law speaks of it: where `embE` writes one body for two symbols, a reading can
keep at most one of them at a position and salt, and the third clause speaks of fewer strings. No
`embE` and no reading is given here (OnBytes/TypedOracleCompiler/StringsStoredAt.lean's `embX` and `prjX` have the
types of `W3`'s `embE` and `prjE`, at a total code c, of which OnBytes/TypedOracleCompiler/StringsAt.lean gives one;
they are not laid in). That the whole wire `W3` is lawful is not shown and not needed: of it the
clause asks the number of slots alone. The sibling's top theorem is not applied: at this interface
too (no index; every string decodes) it would say nothing; the language of `plainAt3` is the
parameter Lg. The compiled chain is ONE chain through seams and stretches; a key file has three
chains with three labels: nothing here ties the two. `plainAt3` is for `verifyB`; for the strict
verifier the third clause alone is stated, for the named set (`lang3S`); by the sibling's own page
its definitions of the strict format tree by tree are pinned by no theorem. No test on bodies is
shown to be passed in this file (OnBytes/TypedOracleCompiler/StringsWhole.lean, StringsRead.lean and
StringsBounds.lean: under conditions on the trees and the salt). Nothing ties the strict verifier's
length sMT of a leaf's salt to the one length at which the code of leaf queries writes. A round with
more than `maxRt` trees is refused by the sibling's verifier: the third clause is then empty. Here a
≤ the wiring's greatest depth and 2 ^ a symbols fit under depth a, so the two causes of emptiness
that OnBytes/TypedOracleCompiler/Slice/PlainClause.lean's head names do not arise. What OnBytes/TypedOracleCompiler/Strings.lean's
head says is not claimed of a leaf's string is not claimed here either: above all that the numbers
lie in the domain of the format's hash (`Fmt.oStr` and `Fmt.label` are total); at a tree with the
mark "stored" the number is still 164; which chain's run value the 32 bytes are is a parser's
matter, and here there are three chains. One length of salts serves all three stretches. Whether a
stored symbol's body and a prover's symbol's body are apart is not said here
(OnBytes/TypedOracleCompiler/StringsStoredAt.lean: `storedLike_embX`, `storedLike_own`, for its own `embX`; at three
stretches `Stretches.embS_take164` of OnBytes/TypedOracleCompiler/StringsAt.lean with `prjX_none_of_164` of
OnBytes/TypedOracleCompiler/StringsOwn.lean). Nothing on padding. What else the head of
OnBytes/TypedOracleCompiler/Slice/PlainClause.lean says is not claimed is not claimed here either: above all, that
any string is accepted; the oracles are the sibling's typed random oracles, not a hash function on
strings; no page, no family over one oracle.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.StrictClause
import OnBytes.TypedOracleCompiler.Slice.Plain3Wire
import OnBytes.TypedOracleCompiler.StringsList

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.StringsList (ownT rdT leafT rdT_ownT ownT_some ownT_fit)
open scoped ENNReal

/- salt: the length of a file's salt, in bytes -/
variable (salt : ℕ) (C : PQ.CK)

/-! ## Own strings on a shape that is put together -/

/-- Written rounds in front of a shape t: a symbol of theirs is written as its leaf's own string
(the empty string where its tree's code writes nothing); one of t as t's way of writing says. -/
def embApp (t : Shape) (et : (p : OPos t) → OSym t p → List Bool) :
    (ds : List PQ.RD) → (p : OPos (PQ.uL C ds ++ t)) → OSym (PQ.uL C ds ++ t) p → List Bool
  | [], p, a => et p a
  | d :: _, .inl p, a => (ownT salt d.trees p a).getD []
  | _ :: ds, .inr q, a => embApp t et ds q a

/-- And back: a body is read at a position of a written round by the code of that position's own
tree. -/
def prjApp (t : Shape) (pt : (p : OPos t) → List Bool → Option (OSym t p)) :
    (ds : List PQ.RD) → (p : OPos (PQ.uL C ds ++ t)) → List Bool →
      Option (OSym (PQ.uL C ds ++ t) p)
  | [], p, b => pt p b
  | d :: _, .inl p, b => rdT salt d.trees p b
  | _ :: ds, .inr q, b => prjApp t pt ds q b

theorem back_app (t : Shape) (et : (p : OPos t) → OSym t p → List Bool)
    (pt : (p : OPos t) → List Bool → Option (OSym t p)) (ht : ∀ p a, pt p (et p a) = some a) :
    ∀ (ds : List PQ.RD), (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
      ∀ (p : OPos (PQ.uL C ds ++ t)) (a : OSym (PQ.uL C ds ++ t) p),
        prjApp salt C t pt ds p (embApp salt C t et ds p a) = some a
  | [], _, p, a => ht p a
  | d :: _, h, .inl p, a => by
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.1 (ownT_some salt d.trees (h d (List.mem_cons_self ..)) p a)
      show rdT salt d.trees p ((ownT salt d.trees p a).getD []) = some a
      rw [hm]
      exact rdT_ownT salt d.trees p a m hm
  | _ :: ds, h, .inr q, a =>
      back_app t et pt ht ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

/-- The two numbers of a leaf's label and its bytes, on written rounds in front of a shape t. -/
def leafApp (t : Shape) (lt : (p : OPos t) → OSym t p → Nat × Nat × ByteArray) :
    (ds : List PQ.RD) → (p : OPos (PQ.uL C ds ++ t)) → OSym (PQ.uL C ds ++ t) p →
      Nat × Nat × ByteArray
  | [], p, a => lt p a
  | d :: _, .inl p, a => leafT salt d.trees p a
  | _ :: ds, .inr q, a => leafApp t lt ds q a

/-- What it is for a way of writing to give the bits of the format's label and bytes. -/
def Fits {t : Shape} (et : (p : OPos t) → OSym t p → List Bool)
    (lt : (p : OPos t) → OSym t p → Nat × Nat × ByteArray) : Prop :=
  ∀ p a, et p a = _root_.Run.bytesToBits (_root_.Fmt.label 164 (lt p a).1 (lt p a).2.1) ++
    _root_.Run.bytesToBits (lt p a).2.2

theorem fits_app (t : Shape) (et : (p : OPos t) → OSym t p → List Bool)
    (lt : (p : OPos t) → OSym t p → Nat × Nat × ByteArray) (ht : Fits et lt) :
    ∀ (ds : List PQ.RD), (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
      Fits (embApp salt C t et ds) (leafApp salt C t lt ds)
  | [], _, p, a => ht p a
  | d :: _, h, .inl p, a => by
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.1 (ownT_some salt d.trees (h d (List.mem_cons_self ..)) p a)
      show (ownT salt d.trees p a).getD [] = _
      rw [hm]
      exact ownT_fit salt d.trees p a m hm
  | _ :: ds, h, .inr q, a =>
      fits_app t et lt ht ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

/-- A seam in front of a shape t has no position: t's way of writing. -/
def embSeam (s : Seam) (t : Shape) (et : (p : OPos t) → OSym t p → List Bool) :
    (p : OPos (s.r :: t)) → OSym (s.r :: t) p → List Bool
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => et q a

def prjSeam (s : Seam) (t : Shape) (pt : (p : OPos t) → List Bool → Option (OSym t p)) :
    (p : OPos (s.r :: t)) → List Bool → Option (OSym (s.r :: t) p)
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, b => pt q b

def leafSeam (s : Seam) (t : Shape) (lt : (p : OPos t) → OSym t p → Nat × Nat × ByteArray) :
    (p : OPos (s.r :: t)) → OSym (s.r :: t) p → Nat × Nat × ByteArray
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => lt q a

theorem fits_seam (s : Seam) (t : Shape) (et : (p : OPos t) → OSym t p → List Bool)
    (lt : (p : OPos t) → OSym t p → Nat × Nat × ByteArray) (ht : Fits et lt) :
    Fits (embSeam s t et) (leafSeam s t lt)
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => ht q a

theorem back_seam (s : Seam) (t : Shape) (et : (p : OPos t) → OSym t p → List Bool)
    (pt : (p : OPos t) → List Bool → Option (OSym t p)) (ht : ∀ p a, pt p (et p a) = some a) :
    ∀ (p : OPos (s.r :: t)) (a : OSym (s.r :: t) p),
      prjSeam s t pt p (embSeam s t et p a) = some a
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => ht q a

/-- Written rounds with nothing behind them. -/
def embTail (ds : List PQ.RD) (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) : List Bool :=
  (StringsList.ownStr salt C ds ⟨p, a⟩).getD []

theorem back_L (ds : List PQ.RD) (h : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) :
    StringsList.rdLeaf salt C ds p (embTail salt C ds p a) = some a := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (StringsList.ownStr_some salt C ds h ⟨p, a⟩)
  unfold embTail
  rw [hm]
  exact StringsList.rdLeaf_own salt C ds p a m hm

theorem fits_tail (ds : List PQ.RD) (h : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    Fits (embTail salt C ds) fun p a => StringsList.leafSL salt C ds ⟨p, a⟩ := fun p a => by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (StringsList.ownStr_some salt C ds h ⟨p, a⟩)
  unfold embTail
  rw [hm]
  exact StringsList.ownStr_fit salt C ds ⟨p, a⟩ m hm

/-! ## The three stretches -/

namespace Stretches
variable (G : Stretches)

/-- No tree of the three stretches is deeper than 63. -/
def Shallow : Prop :=
  (∀ d ∈ G.ds₁, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) ∧
  (∀ d ∈ G.ds₂, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) ∧
  ∀ d ∈ G.ds₃, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64

/-- A symbol of the protocol's oracles as a body: its leaf's own string. -/
def embS : (p : OPos G.sh) → OSym G.sh p → List Bool :=
  embSeam G.s0 _ (embApp salt G.C G.sh₂
    (embSeam G.s1 _ (embSeam G.s2 _ (embApp salt G.C G.sh₃
      (embSeam G.s3 _ (embTail salt G.C G.ds₃)) G.ds₂))) G.ds₁)

/-- A body read at a position: by the code of that position's own tree. -/
def prjS : (p : OPos G.sh) → List Bool → Option (OSym G.sh p) :=
  prjSeam G.s0 _ (prjApp salt G.C G.sh₂
    (prjSeam G.s1 _ (prjSeam G.s2 _ (prjApp salt G.C G.sh₃
      (prjSeam G.s3 _ (StringsList.rdLeaf salt G.C G.ds₃)) G.ds₂))) G.ds₁)

/-- What is written is read back, if no tree is deeper than 63. No condition on the trees'
numbers, or on how many trees a round sends. -/
theorem back (h : G.Shallow) (p : OPos G.sh) (a : OSym G.sh p) :
    G.prjS salt p (G.embS salt p a) = some a :=
  back_seam G.s0 _ _ _ (back_app salt G.C G.sh₂ _ _
    (back_seam G.s1 _ _ _ (back_seam G.s2 _ _ _ (back_app salt G.C G.sh₃ _ _
      (back_seam G.s3 _ _ _ (back_L salt G.C G.ds₃ h.2.2)) G.ds₂ h.2.1))) G.ds₁ h.1) p a

/-- The two numbers of a leaf's label and its bytes: the word with its OWN tree's number, width and
the salt's words; 2 ^ depth + place; column and fill. -/
def leafS : (p : OPos G.sh) → OSym G.sh p → Nat × Nat × ByteArray :=
  leafSeam G.s0 _ (leafApp salt G.C G.sh₂
    (leafSeam G.s1 _ (leafSeam G.s2 _ (leafApp salt G.C G.sh₃
      (leafSeam G.s3 _ fun p a => StringsList.leafSL salt G.C G.ds₃ ⟨p, a⟩) G.ds₂))) G.ds₁)

/-- The body is the bits of the format's label, with the position's own tree's numbers, and of
column and fill, if no tree is deeper than 63. -/
theorem embS_fit (h : G.Shallow) : Fits (G.embS salt) (G.leafS salt) :=
  fits_seam G.s0 _ _ _ (fits_app salt G.C G.sh₂ _ _
    (fits_seam G.s1 _ _ _ (fits_seam G.s2 _ _ _ (fits_app salt G.C G.sh₃ _ _
      (fits_seam G.s3 _ _ _ (fits_tail salt G.C G.ds₃ h.2.2)) G.ds₂ h.2.1))) G.ds₁ h.1)

end Stretches

/-! ## The interface, the wire, the written protocol -/

variable (G : Stretches) (dec : PQ.View → PQ.View → PQ.View → Bool)

/-- The interface whose Test is the protocol in three stretches: one external string of 2 ^ a
symbols; Link and Batch have no round; the honest sides are the library's dummies. An interface of
the library's type; a body is chosen beside it. -/
@[reducible] def L3 : _root_.Iop.BatchProtocol Unit Unit where
  wordLength := 2 ^ G.a
  Symbol := PQ.SgX
  EncodingRandomness := Unit
  encodeIndex := fun _ _ p => (p.val, [])
  decodeIndex := fun _ => some ()
  offline := Plain3 G dec
  link := { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
            reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto
    { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
      reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
  honestOfflineProver := _root_.Run.dummyH _ fun _ p => (p.val, [])
  honestLinkProver := _root_.Run.dummyH _ fun _ => (fun p => (p.val, []), fun p => (p.val, []))
  honestOnlineBatchProver := _root_.Run.dummyB _ fun _ p => (p.val, [])
  early := id
  late := none

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones)
  (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)

/-- A wire of the sibling at that interface, with bodies that are strings: Test's wiring is the
maker's; the stored symbols' way of writing is given from outside. -/
def W3 : QueryLayout 256 (Strings.strung (L3 G dec)) where
  K := K + 1
  T := wq3 G K chal o dec
  Lk := ⟨(), { WireE.two (2 ^ G.a) PQ.SgX (0, []) with depth := G.a },
    inferInstanceAs (DecidableEq Empty), 0, G.a⟩
  B := ⟨(), we1 G.a, inferInstanceAs (DecidableEq Empty), 0, G.a⟩
  depth := G.a
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := embE
  prjE := prjE
  embT := G.embS salt
  prjT := G.prjS salt
  embL := fun p _ => p.elim
  prjL := fun p _ => p.elim
  embB := fun p _ => p.elim
  prjB := fun p _ => p.elim

/-- The protocol in three stretches, written into the sibling's oracles: under the tag of Test;
plain parts as they are; symbols as their leaves' own strings. -/
def Z3 : Written (W3 salt G dec K chal o embE prjE) where
  t := Tag.test
  P := Plain3 G dec
  wq := wq3 G K chal o dec
  embS := G.embS salt
  prjS := G.prjS salt
  embP := id
  prjP := some

/-- Its compiled verifier is the sibling's `vT` at that wire. -/
theorem Z3_verifier (cm : Dig 256) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (Plain3 G dec))) :
    (Z3 salt G dec K chal o embE prjE).verifier cm π = vT (W3 salt G dec K chal o embE prjE) cm π :=
  rfl

/-- A leaf query on a symbol is written by the code of OnBytes/TypedOracleCompiler/Strings.lean, with the bits of
`Fmt.oStr` at the number 164 and the numbers of the position's own tree. start: 32 bytes; fsalt: a
file's salt of the length `salt`; the typed salt is the bits of the one and then of the other.
Asked: no tree is deeper than 63; the body passes the code's test. -/
theorem leaf_query3 (ok : List Bool → Bool) (hs : G.Shallow) (p : OPos G.sh) (a : OSym G.sh p)
    (hok : ok (G.embS salt p a) = true)
    (start fsalt : ByteArray) (h32 : start.size = 32) (hf : fsalt.size = salt) :
    (Strings.pLeafS (L3 G dec) (8 * salt) ok).put
        ⟨G.embS salt p a, _root_.Run.bytesToBits start ++ _root_.Run.bytesToBits fsalt⟩ =
      some (_root_.Run.bytesToBits (_root_.Fmt.oStr 0 164 (G.leafS salt p a).1
        (G.leafS salt p a).2.1 start ((G.leafS salt p a).2.2 ++ fsalt))) := by
  have hl : (_root_.Run.bytesToBits start ++ _root_.Run.bytesToBits fsalt).length =
      256 + 8 * salt := by
    rw [List.length_append, _root_.Run.length_bytesToBits, _root_.Run.length_bytesToBits, h32, hf]
  have h256 : (_root_.Run.bytesToBits start).length = 256 := by
    rw [_root_.Run.length_bytesToBits, h32]
  show (if (_root_.Run.bytesToBits start ++ _root_.Run.bytesToBits fsalt).length =
        256 + 8 * salt then
      (if ok (G.embS salt p a) then some (G.embS salt p a) else none).map fun m =>
        _root_.Run.pre33 ++
          ((_root_.Run.bytesToBits start ++ _root_.Run.bytesToBits fsalt).take 256 ++
          (m ++ (_root_.Run.bytesToBits start ++ _root_.Run.bytesToBits fsalt).drop 256))
      else none) = _
  rw [if_pos hl, if_pos hok, G.embS_fit salt hs p a, List.take_left' h256,
    List.drop_left' h256, _root_.Run.oStr32_bits 164 _ _ start _ (by decide) h32,
    _root_.Run.bytesToBits_append]
  simp only [Option.map_some, List.append_assoc]

/-- It meets what is asked of a written protocol, if the maker's wiring is lawful and no tree is
deeper than 63. -/
theorem Z3_ok (hs : G.Shallow) (hw : (wq3 G K chal o dec).OKG) :
    (Z3 salt G dec K chal o embE prjE).OK :=
  ⟨G.back salt hs, fun _ => rfl, hw, rfl, fun p => ⟨we1_which G.a p, we1_leaf G.a p⟩⟩

/-- The clause for the protocol in three stretches, with a round of several roots as it is: IF
it is round-by-round sound for a language with every error at most e, the maker's wiring is lawful
(at sampled values it is not, wherever a field element is drawn: see the head) and no tree is deeper
than 63, THEN the compiler's conclusion for that language and any reading. -/
theorem plainAt3 (R : Reading (Strings.strung (L3 G dec)) embE)
    (Lg : Unit → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (εs : ℝ≥0∞) (ε : Err G.sh)
    (hb : Err.Below ε εs) (hS : (Plain3 G dec).Sound Lg ε) (hs : G.Shallow)
    (hw : (wq3 G K chal o dec).OKG) :
    PlainAt (Z3 salt G dec K chal o embE prjE) R Lg εs :=
  plainAt (Z3 salt G dec K chal o embE prjE) R Lg εs ε hb hS (plain3_local G dec)
    (Z3_ok salt G dec K chal o embE prjE hs hw)

/-- With the strict format its compiled verifier is the sibling's `vTS` at that wire. -/
theorem Z3_verifierS (sMT sFS : ℕ) (cm : Dig 256)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (Plain3 G dec))) :
    (Z3 salt G dec K chal o embE prjE).verifierS sMT sFS cm π =
      vTS (W3 salt G dec K chal o embE prjE) sMT sFS cm π :=
  rfl

/-- The third clause for the verifier with the strict format, for the named set: IF the protocol
is round-by-round sound for the language at the errors ε, the maker's wiring is lawful and no tree
is deeper than 63, THEN outside the set a string that the sibling's `vTS` accepts at that wire
within the trace, and whose external openings R keeps, means that the language holds of the string
that R reads off the trace under the root. -/
theorem lang3S (R : Reading (Strings.strung (L3 G dec)) embE)
    (Lg : Unit → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (ε : Err G.sh)
    (hS : (Plain3 G dec).Sound Lg ε) (hs : G.Shallow) (hw : (wq3 G K chal o dec).OKG)
    (sMT sFS : ℕ) (tr : Tc (W3 salt G dec K chal o embE prjE)) (cm : Dig 256)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (Plain3 G dec)))
    (hB : ¬ plainBad (Z3 salt G dec K chal o embE prjE) R ε tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (vTS (W3 salt G dec K chal o embE prjE) sMT sFS cm π) true) :
    Lg () (R.at (W3 salt G dec K chal o embE prjE) tr cm) :=
  plainBad_langS (Z3 salt G dec K chal o embE prjE) R ε Lg hS (plain3_local G dec)
    (Z3_ok salt G dec K chal o embE prjE hs hw) sMT sFS tr cm π hB hk hrun

/-- The same with verifier's messages as hash blocks (the library's `ckP f`, `chalP f K`): there
the maker's wiring is lawful if every round takes at most K blocks and has at most 64 bits of work
(the sibling's `wq3_okg_pull`). The soundness asked is that of the protocol at blocks. -/
theorem plainAt3_pull (f : Fmt.Fld) (o : (G.atP f).Ones)
    (R : Reading (Strings.strung (L3 (G.atP f) dec)) embE)
    (Lg : Unit → (oneExternalString (2 ^ (G.atP f).a) PQ.SgX).Str → Prop) (εs : ℝ≥0∞) (ε : Err (G.atP f).sh)
    (hb : Err.Below ε εs) (hS : (Plain3 (G.atP f) dec).Sound Lg ε) (hs : (G.atP f).Shallow)
    (hK : ∀ d ∈ G.ds₁ ++ (G.ds₂ ++ G.ds₃), (_root_.Run.bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ G.ds₁ ++ (G.ds₂ ++ G.ds₃), d.entry.work ≤ 64) :
    PlainAt (Z3 salt (G.atP f) dec K (_root_.Run.chalP f K) o embE prjE) R Lg εs :=
  plainAt3 salt (G.atP f) dec K (_root_.Run.chalP f K) o embE prjE R Lg εs ε hb hS hs
    (wq3_okg_pull G f K o dec hK hw)

end TypedOracleCompiler.Slice
