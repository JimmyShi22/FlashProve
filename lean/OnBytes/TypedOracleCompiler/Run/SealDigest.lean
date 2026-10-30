-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SealDigest.lean: A SEALED ROUND's DRAWN DIGEST IS THE ROW's BLOCK 1: SO THE TWO
SEALS OF Run/ChainF.lean ARE THE DIGESTS THAT THE READER's SEALED ROUNDS DRAW. A piece of "the tie
at H_b" for a proof file (LinkF).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY ("a sealed round's drawn digest is the row's block 1" was said by text; no lemma named; that
seal₁ | sealOf … are the port's seals is no lemma in ChainF.lean). In chain_whole the slot value is
seal₁ as a digest, and (F3) holds sealOf … in ρ₀'s place: both are BLOCKS OF A ROW (Fmt.blockW … 1).
The port's seal of a chain is the digest that its sealed round DRAWS; Run/ReqClimb.lean's "closing"
is the first chain's.
  cat_words          32 bytes are their four words, each spelled again (Fmt.u64_wordAt, four times)
  sealed_digest a round of the kind "sealed" whose entry draws nothing else, without work, read as a
  reader reads (ro.drawn = Fmt.drawRound … on the row's message blocks): ro.drawn.digest = some
  (Fmt.blockW … 1): the row has two blocks; the message's first block is block 1; the seal is its
  four words
  msg_empty          a message that is read as no item is empty
  sealG_digest   SEAL 1: such a round WITHOUT ITEMS, read behind the chain c (TraceL … [r] [ro] c
                 …): ro.drawn.digest = some (sealG O c): what GAt makes g answer: chain_whole's
                 seal₁
  sealOf_digest SEAL 2: under SealLast ds, FitL ds rs, TraceL … rs ros c …: the LAST round read
  draws sealOf (Fmt.HO O) rs ros c: the typed chain value behind the shared stretch
WHAT IS NOT SAID. That the port's ChainRead.seal IS the last round's drawn digest (the port's text:
Chain/Session.lean). That chain 1's last round is such a round at cfg₀ (SealRound's six clauses and
"no items": an evaluation of the description). Nothing on a sealed round WITH work.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ChainF

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)

/-- 32 bytes are their four words, each spelled again -/
theorem cat_words (b : ByteArray) (h : b.size = 32) :
    _root_.Fmt.cat ([_root_.Fmt.wordAt b 0, _root_.Fmt.wordAt b 8, _root_.Fmt.wordAt b 16,
        _root_.Fmt.wordAt b 24].map
      _root_.Fmt.u64) = b := by
  simp only [List.map_cons, List.map_nil, _root_.Fmt.cat_cons, _root_.Fmt.cat_nil]
  rw [_root_.Fmt.u64_wordAt b 0 (by omega), _root_.Fmt.u64_wordAt b 8 (by omega), _root_.Fmt.u64_wordAt b 16 (by omega),
    _root_.Fmt.u64_wordAt b 24 (by omega)]
  have hs : b.data.size = 32 := by rw [ByteArray.size_data]; exact h
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_extract, ByteArray.data_empty]
  simp [Array.extract_append_extract, ← hs]

/-- A SEALED ROUND's DRAWN DIGEST IS THE ROW's BLOCK 1. -/
theorem sealed_digest (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (f : _root_.Fmt.Fld)
    (r : _root_.Fmt.Round) (ro : RoundOut) (c : Chain) (hk : r.kind = .sealed)
        (h1 : r.entry.poss = 0)
    (h2 : r.entry.trits = 0) (h3 : r.entry.drawE = 0) (h4 : r.entry.drawNZ = 0)
        (hw : r.entry.work = 0)
    (hdrawn : ro.drawn = _root_.Fmt.drawRound f r.entry r.kind
      (_root_.Fmt.rowOf (_root_.Fmt.msgA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro)))) :
    ro.drawn.digest =
      some (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ro.msg r.kind
          r.entry.work ro.nonce 1) := by
  have hB : (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ro.msg r.kind
      r.entry.work ro.nonce 1).size
      = 32 := size_blockW_HO O hO _ _ _ _ _ _ _ _
  have hbs : rowBs (_root_.Fmt.HO O) c r ro =
      _root_.Fmt.fetchW (m := Id) (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
        ro.msg r.kind r.entry.work ro.nonce
        (_root_.Fmt.firstBlock r.entry.work +
          _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind)) := rfl
  have hsz2 : (rowBs (_root_.Fmt.HO O) c r ro).size = 2 := by
    rw [hbs, _root_.Fmt.size_fetchW, hw, hk]
    unfold _root_.Fmt.wordsAtMost
    rw [h1, h2, h3, h4]
    rfl
  have hget : (rowBs (_root_.Fmt.HO O) c r ro).getD 1 ByteArray.empty =
      _root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work
          ro.nonce 1 := by
    have h2' := hsz2
    rw [hbs, _root_.Fmt.size_fetchW] at h2'
    rw [hbs]
    exact _root_.Fmt.fetchW_getD _ _ _ _ _ _ _ _ _ 1 (by omega)
  have hv0 : (_root_.Fmt.msgA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro)).getD 0
      ByteArray.empty =
      _root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work
          ro.nonce 1 := by
    rw [← hget]
    unfold _root_.Fmt.msgA
    rw [hw]
    show ((rowBs (_root_.Fmt.HO O) c r ro).extract 1 (rowBs (_root_.Fmt.HO O) c r ro).size).getD 0
        ByteArray.empty = _
    simp [Array.getD_eq_getD_getElem?, hsz2]
  generalize _root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ro.msg r.kind
      r.entry.work ro.nonce 1 = B
    at hB hv0 ⊢
  generalize _root_.Fmt.msgA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) = vb at hdrawn hv0
  rw [hdrawn]
  unfold _root_.Fmt.drawRound _root_.Fmt.drawRoundD _root_.Fmt.drawElems _root_.Fmt.drawDigest
  rw [hk, h1, h2, h3, h4, if_neg (by decide), if_pos rfl]
  simp [_root_.Fmt.Dr.bind, _root_.Fmt.Dr.pure, _root_.Fmt.drawPoss, _root_.Fmt.Dr.times,
      _root_.Fmt.drawPlainNZ,
    _root_.Fmt.drawTrits, _root_.Fmt.drawWords, _root_.Fmt.drawSeal, _root_.Fmt.Dr.word,
        _root_.Fmt.rowOf, hv0]
  exact cat_words B hB

/-- a message that is read as no item is empty -/
theorem msg_empty (f : _root_.Fmt.Fld) (msg : ByteArray) (l : List ItemValue)
    (h : _root_.Fmt.whole (_root_.Fmt.readItems f []) msg = some l) : msg = ByteArray.empty := by
  have hp : PlainOf.ofGots [] l = some () := by
    unfold _root_.Fmt.whole at h
    have e : _root_.Fmt.readItems f [] msg 0 = some ([], 0) := rfl
    rw [e] at h
    simp only at h
    split at h
    · cases Option.some.inj h
      rfl
    · cases h
  exact ((msg_bytes f [] msg l () h hp).1).symm

/-- SEAL 1: a sealed round without items, read behind the chain c, draws sealG O c: (G)'s answer by
GAt. -/
theorem sealG_digest (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
    (r : _root_.Fmt.Round) (ro : RoundOut) (c : Chain) (roots : Array ByteArray)
        (hk : r.kind = .sealed)
    (hi : r.items = []) (h1 : r.entry.poss = 0) (h2 : r.entry.trits = 0) (h3 : r.entry.drawE = 0)
    (h4 : r.entry.drawNZ = 0) (hw : r.entry.work = 0)
        (ht : TraceL (_root_.Fmt.HO O) P [r] [ro] c roots) :
    ro.drawn.digest = some (sealG O c) := by
  obtain ⟨hask, hwhole, hdrawn, -, -, -⟩ := ht
  simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff, Bool.or_eq_true,
    bne_iff_ne, beq_iff_eq] at hask
  obtain ⟨-, -, -, -, -, -, hw0, -⟩ := hask
  have hn : ro.nonce = 0 := hw0.resolve_left fun h => h hw
  have hm : ro.msg = ByteArray.empty := msg_empty P.field ro.msg ro.vals
      (by rw [← hi]; exact hwhole)
  rw [sealed_digest O hO P.field r ro c hk h1 h2 h3 h4 hw hdrawn, hm, hn, hk, hw]
  rfl

/-- SEAL 2: the last round of a stretch that ends in a sealed round draws sealOf: the typed chain
value behind the stretch (chain_from_shS_ind). -/
theorem sealOf_digest (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (P : _root_.Fmt.Plan) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain)
        (roots : Array ByteArray),
      SealLast ds → FitL ds rs → TraceL (_root_.Fmt.HO O) P rs ros c roots →
      ∃ ro, ros.getLast? = some ro ∧ ro.drawn.digest = some (sealOf (_root_.Fmt.HO O) rs ros c)
  | [], _, _, _, _, hs, _, _ => hs.elim
  | [_], [], _, _, _, _, hf, _ => hf.elim
  | [_], _ :: _, [], _, _, _, _, ht => ht.elim
  | _ :: _ :: _, [], _, _, _, _, hf, _ => hf.elim
  | _ :: _ :: _, [_], _, _, _, _, hf, _ => hf.2.2.2.2.2.2.elim
  | _ :: _ :: _, _ :: _ :: _, [], _, _, _, _, ht => ht.elim
  | _ :: _ :: _, _ :: _ :: _, [_], _, _, _, _, ht => ht.2.2.2.2.2.elim
  | [d], r :: rs, ro :: ros, c, roots, hs, hf, ht => by
      obtain ⟨he, hk, -, -, -, -, hf'⟩ := hf
      obtain ⟨-, -, hdrawn, -, -, ht'⟩ := ht
      cases rs with
      | cons _ _ => exact hf'.elim
      | nil =>
      cases ros with
      | cons _ _ => exact ht'.elim
      | nil =>
      exact ⟨ro, rfl, sealed_digest O hO P.field r ro c (hk ▸ hs.kind) (he ▸ hs.poss)
          (he ▸ hs.trits) (he ▸ hs.drawE)
        (he ▸ hs.drawNZ) (he ▸ hs.work) hdrawn⟩
  | _ :: d' :: ds, r :: r' :: rs, ro :: ro' :: ros, c, roots, hs, hf, ht => by
      obtain ⟨x, hx, hd⟩ := sealOf_digest O hO P (d' :: ds) (r' :: rs) (ro' :: ros) _ _ hs
          hf.2.2.2.2.2.2 ht.2.2.2.2.2
      exact ⟨x, hx, hd⟩


end TypedOracleCompiler.Run.PQ
