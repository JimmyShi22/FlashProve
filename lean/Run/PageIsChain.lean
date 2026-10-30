-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsChain.lean: the proof of the statement on the hash chain from which the verifier's
challenges are drawn (`Spec.pi_chain`) in the comparison of the two verifiers of Run/PageIs.lean.

Run/PageIs.lean compares two verifiers of a proof file: this library's rendering in Lean
(Fmt/Rules8.lean) of the verifier of the format page (docs/format/FORMAT.md, which comes with the
programs, that is, with the C++ implementation that accompanies this Lean code; here in an edition
of the page that is not in this repository), and the compiled verifier behind a lenient reader that
only cuts the file into its parts. To cut the file, the lenient reader recomputes the hash chain,
and it refuses some files (what it still asks the hash, what it refuses and what it does not test:
part 1 of the head of Run/ParseLax.lean).

What the statement says. Let O be any function on byte strings with answers of 32 bytes. Let S be a
description within the limits of the generic construction (`Run.PQ.ok`). Let C be the choice of
challenge types (the parameter `C : CK`, called a kit in the code), and let chal make a message from
a round's K blocks. Let what C reads off that message be the format's draw on the first of these
blocks, as many as the round's draws can need (`KitFits`); and let K have room for every round's
blocks. Let o be what the lenient reader hands out, of which only `LaxFacts` of Run/PageIs.lean is
used, with its rounds typed (`plainsSL`). Then, at the typed oracle functions that O induces and on
the reader's argument string, the chain of the evaluable form of the compiled verifier (`chainP`,
Run/ThinDefs.lean) does not refuse, ends in a local phase, and yields each round's root as o has it.
Moreover, what it draws is what o says was drawn, and its test bits pass exactly if every round's
proof-of-work test of the format page passes (`passL`). (That the evaluable form computes the
compiled verifier's verdict is `thin_verify`, stated in Run/ThinTie.lean and proved in
Run/ThinTieProofs.lean.)

1. What the file contains. Theorems with their proofs, each under the hypotheses of its statement,
and two definitions with which they are stated. The parts are lettered as in the text below the
head.
   C. `msgA_eq`, `drawn_eq`, `pass_bits`. On a round's blocks: the blocks of the verifier's message,
       as the format cuts them off the row, are the bytes of the typed message blocks. So the view
       of the verifier's message is the format's draw.
   B. `FitL`, `roundsOk_count`, `shape_some` (of a tree with exactly one opening), `fit_from`,
       `fit_rds`. What the limits of the generic construction say: a round's entry, kind and items
       are the description's; a round has a tree exactly if it sends a root; at most one; as many as
       its items say.
   Under "The rounds, by induction", `chain_ind`: for a suffix of the rounds, any chain value, and
       any embedding of plain parts that the spellings read rightly.

2. What is checked when the file compiles. No tests (#guard) in this file.

3. Theorems. Other files use `pi_chain` (Run/PageIsProofs.lean, Run/PageIsFullTop.lean [not in this library]), and `FitL`
and `fit_rds` (Run/OneIsTypedTop.lean).

4. What is not claimed.
   That `LaxFacts` holds of the lenient reader's output (Run/PageIsReaders.lean), what follows the
   chain (Run/PageIsAfter.lean), and the comparison of the two verifiers as a whole
   (Run/PageIsProofs.lean, Run/PageIsCoreProofs.lean) are other files of the same comparison.
   No statement on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageIs
import Fmt.Rules8Ok
import Run.ChainRow

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)

/-! ## A. A message's bytes -/

/-- The spelling of an item that was read: its bytes. -/
def gotBytes : ItemValue → ByteArray
  | .f x => _root_.Fmt.u64 x
  | .e x => _root_.Fmt.ext x
  | .word x => _root_.Fmt.u64 x
  | .root d => d
  | .answer x => _root_.Fmt.ext x

theorem only_item (f : _root_.Fmt.Fld) (t : Item) :
    _root_.Fmt.Only (_root_.Fmt.readItem f t) gotBytes fun g => ∀ d, g = .root d → d.size = 32 := by
  intro b i x j h
  cases t with
  | f =>
      rcases h1 : _root_.Fmt.rdElt f b i with _ | ⟨u, k⟩
      · simp [_root_.Fmt.readItem, h1] at h
      · simp only [_root_.Fmt.readItem, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, a2, a3, a4⟩ := _root_.Fmt.only_elt f b i u k h1
        exact ⟨fun d hd => (by cases hd), a2, a3, a4⟩
  | e =>
      rcases h1 : _root_.Fmt.rdExt f b i with _ | ⟨u, k⟩
      · simp [_root_.Fmt.readItem, h1] at h
      · simp only [_root_.Fmt.readItem, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, a2, a3, a4⟩ := _root_.Fmt.only_ext f b i u k h1
        exact ⟨fun d hd => (by cases hd), a2, a3, a4⟩
  | word =>
      rcases h1 : _root_.Fmt.rdWord b i with _ | ⟨u, k⟩
      · simp [_root_.Fmt.readItem, h1] at h
      · simp only [_root_.Fmt.readItem, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, a2, a3, a4⟩ := _root_.Fmt.only_word b i u k h1
        exact ⟨fun d hd => (by cases hd), a2, a3, a4⟩
  | root =>
      rcases h1 : _root_.Fmt.rdDigest b i with _ | ⟨u, k⟩
      · simp [_root_.Fmt.readItem, h1] at h
      · simp only [_root_.Fmt.readItem, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨a1, a2, a3, a4⟩ := _root_.Fmt.only_digest b i u k h1
        exact ⟨fun d hd => (by cases hd; exact a1), a2, a3, a4⟩
  | answer =>
      rcases h1 : _root_.Fmt.rdExt f b i with _ | ⟨u, k⟩
      · simp [_root_.Fmt.readItem, h1] at h
      · simp only [_root_.Fmt.readItem, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, a2, a3, a4⟩ := _root_.Fmt.only_ext f b i u k h1
        exact ⟨fun d hd => (by cases hd), a2, a3, a4⟩

theorem extract_self (b : ByteArray) (i : ℕ) : b.extract i i = ByteArray.empty := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  simp

/-- What the reader of a message's items accepts is the spelling of what it returns: if
`Fmt.readItems` reads the list l from place i ≤ b.size to place j of b, these bytes of b are the
spellings of l in order, and every root in l has 32 bytes. -/
theorem items_only (f : _root_.Fmt.Fld) :
    ∀ (ts : List Item) (b : ByteArray) (i : ℕ) (l : List ItemValue) (j : ℕ), i ≤ b.size →
      _root_.Fmt.readItems f ts b i = some (l, j) →
      (∀ d ∈ _root_.Fmt.rootsOf l, d.size = 32) ∧
      j = i + (_root_.Fmt.cat (l.map gotBytes)).size ∧
      j ≤ b.size ∧
      b.extract i j = _root_.Fmt.cat (l.map gotBytes)
  | [], b, i, l, j, hi, h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨fun d hd => (by cases hd), rfl, hi, extract_self b i⟩
  | t :: ts, b, i, l, j, hi, h => by
      rcases h1 : _root_.Fmt.readItem f t b i with _ | ⟨x, k⟩
      · simp [_root_.Fmt.readItems, h1] at h
      · rcases h2 : _root_.Fmt.readItems f ts b k with _ | ⟨l', k'⟩
        · simp [_root_.Fmt.readItems, h1, h2] at h
        · simp only [_root_.Fmt.readItems, h1, h2, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨a1, a2, a3, a4⟩ := only_item f t b i x k h1
          obtain ⟨c1, c2, c3, c4⟩ := items_only f ts b k l' k' a3 h2
          refine ⟨?_, ?_, c3, ?_⟩
          · intro d hd
            cases x with
            | root r =>
                rcases List.mem_cons.1 hd with rfl | hd'
                · exact a1 _ rfl
                · exact c1 d hd'
            | f _ => exact c1 d hd
            | e _ => exact c1 d hd
            | word _ => exact c1 d hd
            | answer _ => exact c1 d hd
          · rw [List.map_cons, _root_.Fmt.cat_cons, ByteArray.size_append]
            omega
          · rw [List.map_cons, _root_.Fmt.cat_cons,
              ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4]

/-- The typed plain part spells the items that were read, if every root among them is rt. -/
theorem bytes_ofGots (rt : ByteArray) :
    ∀ (ts : List Item) (l : List ItemValue) (p : PlainOf ts), PlainOf.ofGots ts l = some p →
      (∀ d ∈ _root_.Fmt.rootsOf l, d = rt) → PlainOf.bytes rt ts p = _root_.Fmt.cat (l.map gotBytes)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by cases h
  | .root :: ts, .root d :: l, p, h, hr => by
      have ih := bytes_ofGots rt ts l p h fun d' hd' => hr d' (List.mem_cons_of_mem _ hd')
      show rt ++ PlainOf.bytes rt ts p = _
      rw [List.map_cons, _root_.Fmt.cat_cons, ih, hr d (List.mem_cons_self)]
      rfl
  | .f :: ts, .f x :: l, p, h, hr => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.u64 x ++ PlainOf.bytes rt ts y = _
        rw [List.map_cons, _root_.Fmt.cat_cons, bytes_ofGots rt ts l y h1 hr]
        rfl
  | .word :: ts, .word x :: l, p, h, hr => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.u64 x ++ PlainOf.bytes rt ts y = _
        rw [List.map_cons, _root_.Fmt.cat_cons, bytes_ofGots rt ts l y h1 hr]
        rfl
  | .e :: ts, .e x :: l, p, h, hr => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.ext x ++ PlainOf.bytes rt ts y = _
        rw [List.map_cons, _root_.Fmt.cat_cons, bytes_ofGots rt ts l y h1 hr]
        rfl
  | .answer :: ts, .answer x :: l, p, h, hr => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.ext x ++ PlainOf.bytes rt ts y = _
        rw [List.map_cons, _root_.Fmt.cat_cons, bytes_ofGots rt ts l y h1 hr]
        rfl
  | _ :: _, [], _, h, _ => by simp [PlainOf.ofGots] at h
  | .root :: _, .f _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .root :: _, .e _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .root :: _, .word _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .root :: _, .answer _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .f :: _, .e _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .f :: _, .word _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .f :: _, .root _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .f :: _, .answer _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .word :: _, .f _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .word :: _, .e _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .word :: _, .root _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .word :: _, .answer _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .e :: _, .f _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .e :: _, .word _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .e :: _, .root _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .e :: _, .answer _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .answer :: _, .f _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .answer :: _, .e _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .answer :: _, .word _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h
  | .answer :: _, .root _ :: _, _, h, _ => by simp [PlainOf.ofGots] at h

/-- If the items read can be typed (`PlainOf.ofGots`), as many roots are read as the items have. -/
theorem roots_ofGots :
    ∀ (ts : List Item) (l : List ItemValue) (p : PlainOf ts),
      PlainOf.ofGots ts l = some p → (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root ts
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by simp [PlainOf.ofGots] at h
  | .root :: ts, .root d :: l, p, h => by
      have ih := roots_ofGots ts l p h
      show (_root_.Fmt.rootsOf l).length + 1 = _root_.Fmt.countItem .root (.root :: ts)
      rw [ih]
      simp [_root_.Fmt.countItem]
  | .f :: ts, .f x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · have ih := roots_ofGots ts l y h1
        show (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root (.f :: ts)
        rw [ih]
        simp [_root_.Fmt.countItem]
  | .e :: ts, .e x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · have ih := roots_ofGots ts l y h1
        show (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root (.e :: ts)
        rw [ih]
        simp [_root_.Fmt.countItem]
  | .word :: ts, .word x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · have ih := roots_ofGots ts l y h1
        show (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root (.word :: ts)
        rw [ih]
        simp [_root_.Fmt.countItem]
  | .answer :: ts, .answer x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · have ih := roots_ofGots ts l y h1
        show (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root (.answer :: ts)
        rw [ih]
        simp [_root_.Fmt.countItem]
  | .f :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h

/-- Under `h`, `hp` and `hr` (every root read is rt): the message that was read is the spelling of
the typed plain part, and every root read has 32 bytes. -/
theorem msg_bytes (f : _root_.Fmt.Fld) (ts : List Item) (msg : ByteArray) (l : List ItemValue)
    (p : PlainOf ts) (rt : ByteArray)
    (h : _root_.Fmt.whole (_root_.Fmt.readItems f ts) msg = some l)
    (hp : PlainOf.ofGots ts l = some p) (hr : ∀ d ∈ _root_.Fmt.rootsOf l, d = rt) :
    PlainOf.bytes rt ts p = msg ∧ ∀ d ∈ _root_.Fmt.rootsOf l, d.size = 32 := by
  unfold _root_.Fmt.whole at h
  rcases h1 : _root_.Fmt.readItems f ts msg 0 with _ | ⟨y, j⟩
  · simp [h1] at h
  · simp only [h1] at h
    by_cases hj : j = msg.size
    · rw [if_pos hj] at h
      obtain rfl := Option.some.inj h
      obtain ⟨a1, -, -, a4⟩ := items_only f ts msg 0 y j (Nat.zero_le _) h1
      refine ⟨?_, a1⟩
      rw [bytes_ofGots rt ts y p hp hr, ← a4, hj]
      apply ByteArray.ext
      rw [ByteArray.data_extract, ← ByteArray.size_data]
      simp
    · rw [if_neg hj] at h
      cases h


/-! ## C. One round, on its blocks -/

section Blocks
variable (B : ℕ → ByteArray) (hB : ∀ b, (B b).size = 32) (w nb : ℕ) (bs : Array ByteArray)
  (hs : bs.size = _root_.Fmt.firstBlock w + nb)
  (hg : ∀ b, b < bs.size → bs.getD b ByteArray.empty = B b)

include hB hs hg in
/-- Under `hB`, `hs`, `hg`, `hK` and `hm`: the blocks of the verifier's message, as the format cuts
them off the row, are the bytes of the typed message blocks. -/
theorem msgA_eq (K : ℕ) (hK : nb ≤ K) (mb : Fin K → Dig 256)
    (hm : ∀ i : Fin K, mb i = bytesToDig (B (_root_.Fmt.firstBlock w + i.val))) :
    (Array.ofFn fun i : Fin nb => digToBytes (firstBlocks 256 K nb mb i)) =
      _root_.Fmt.msgA w bs := by
  unfold _root_.Fmt.msgA
  apply Array.ext
  · rw [Array.size_ofFn, Array.size_extract, hs]
    omega
  · intro i h1 h2
    rw [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_extract]
    have hi : i < K := by omega
    have e1 : firstBlocks 256 K nb mb ⟨i, h1⟩ = mb ⟨i, hi⟩ := by
      unfold firstBlocks
      exact dif_pos hi
    have hb : _root_.Fmt.firstBlock w + i < bs.size := by rw [hs]; omega
    have e2 := hg (_root_.Fmt.firstBlock w + i) hb
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb] at e2
    rw [e1, hm, TieTree.dig_bytes _ (hB _)]
    exact e2.symm

include hB hs hg in
/-- Under `KitFits` and the hypotheses below (with `hB`, `hs`, `hg`): what the kit sees in the
wire's message is the format's draw on the row. -/
theorem drawn_eq (f : _root_.Fmt.Fld) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (hkit : KitFits f C K chal) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind)
    (hnb : nb = _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost e k)) (hK : nb ≤ K)
    (mb : Fin K → Dig 256)
    (hm : ∀ i : Fin K, mb i = bytesToDig (B (_root_.Fmt.firstBlock w + i.val))) :
    C.dr e k (chal e k mb) =
      _root_.Fmt.drawRound f e k (_root_.Fmt.rowOf (_root_.Fmt.msgA w bs)) := by
  rw [hkit e k mb, ← hnb]
  congr 1
  unfold rowOfDigs
  rw [msgA_eq B hB w nb bs hs hg K hK mb hm]
  rfl

end Blocks

/-- The test bits of a block that is given by its bytes, against the format's proof-of-work test in
bits: for w ≤ 64 all w test bits are 0 exactly if `Fmt.bitAt b0 k` is 0 for every k < w. -/
theorem pass_bits (b0 : ByteArray) (w : ℕ) (hw : w ≤ 64) :
    decide (∀ i : Fin w, testBits 256 w (bytesToDig b0) i = false) =
      (List.range w).all fun k => _root_.Fmt.bitAt b0 k == false := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  constructor
  · intro h k hk
    have hk' : k < w := List.mem_range.1 hk
    have := h ⟨k, hk'⟩
    unfold testBits at this
    rw [dif_pos (by show k < 256; omega)] at this
    rw [beq_iff_eq]
    exact this
  · intro h i
    have := h i.val (List.mem_range.2 i.isLt)
    rw [beq_iff_eq] at this
    unfold testBits
    rw [dif_pos (by have := i.isLt; omega)]
    exact this

/-! ## B. What the limits of the generic construction say of the rounds -/

/-- The rounds' data against the description's rounds; the head tells the clauses, under B. -/
def FitL : List RD → List _root_.Fmt.Round → Prop
  | [], [] => True
  | d :: ds, r :: rs =>
    d.entry = r.entry ∧ d.kind = r.kind ∧ d.items = r.items ∧
    (d.tree.isSome = true ↔ r.entry.roots ≠ 0) ∧
    _root_.Fmt.countItem .root r.items = r.entry.roots ∧ r.entry.roots ≤ 1 ∧ FitL ds rs
  | _, _ => False

theorem roundsOk_count (P : _root_.Fmt.Plan) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List _root_.Fmt.Round) (after : Bool) (sent : ℕ),
      _root_.Fmt.roundsOk P nr ft after sent rs = true →
      ∀ r ∈ rs, _root_.Fmt.countItem .root r.items = r.entry.roots
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, r', hr => by
      simp only [_root_.Fmt.roundsOk, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hr with rfl | hr'
      · have h1 := h.1
        simp only [_root_.Fmt.Round.ok, Bool.and_eq_true, and_assoc, beq_iff_eq] at h1
        exact h1.2.1
      · exact roundsOk_count P nr ft rs _ _ h.2 r' hr'

theorem shape_some (S : _root_.Fmt.Spec) (n : ℕ)
    (h : ((allOpens S).filter fun o => ownNo o == some n).length = 1) :
    (shapeOfOwn S n).isSome = true := by
  unfold shapeOfOwn
  rw [Option.isSome_map]
  rcases hf : (allOpens S).find? (fun o => ownNo o == some n) with _ | x
  · rw [List.find?_eq_none] at hf
    have : (allOpens S).filter (fun o => ownNo o == some n) = [] :=
      List.filter_eq_nil_iff.2 fun a ha => hf a ha
    rw [this] at h
    cases h
  · rfl

theorem fit_from (S : _root_.Fmt.Spec) :
    ∀ (rs : List _root_.Fmt.Round) (sent : ℕ), sent + (rs.map (·.entry.roots)).sum = nRoots S →
      (∀ r ∈ rs, _root_.Fmt.countItem .root r.items = r.entry.roots) →
      (∀ r ∈ rs, r.entry.roots ≤ 1) → FitL (rdsFrom S sent rs) rs
  | [], _, _, _, _ => trivial
  | r :: rs, sent, hsum, hc, h1 => by
      rw [List.map_cons, List.sum_cons] at hsum
      refine ⟨rfl, rfl, rfl, ?_,
        hc r List.mem_cons_self,
        h1 r List.mem_cons_self,
        fit_from S rs (sent + r.entry.roots) (by omega)
          (fun r' hr' => hc r' (List.mem_cons_of_mem _ hr'))
          fun r' hr' => h1 r' (List.mem_cons_of_mem _ hr')⟩
      show ((if r.entry.roots = 0 then none
            else some ((shapeOfOwn S sent).getD (bareShape S.firstTree sent))).isSome = true) ↔
        _
      by_cases h0 : r.entry.roots = 0
      · rw [if_pos h0]
        simp [h0]
      · rw [if_neg h0]
        exact ⟨fun _ => h0, fun _ => rfl⟩

/-- Within the limits of the generic construction (`ok S`), `FitL` holds of `rds S` and the rounds
of S. -/
theorem fit_rds (S : _root_.Fmt.Spec) (h : ok S = true) : FitL (rds S) S.rounds := by
  simp only [ok, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hS, h1, -, -, -⟩ := h
  refine fit_from S S.rounds 0 (by rw [Nat.zero_add]; rfl) ?_ ?_
  · exact roundsOk_count _ _ _ S.rounds _ _ (_root_.Fmt.ok_rounds hS)
  · intro r hr
    exact of_decide_eq_true (List.all_eq_true.1 h1 r hr)

/-! ## D. The typed answer to a round's chain query; the wire's message -/

/-- Under `hO` and `hk`: the typed answer, block by block, is the page's block, read as a typed
digest (`bytesToDig`). -/
theorem famOf_row {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray)
    (hO : ∀ x, (O x).size = 32) (D : PageD L .onl) (K : ℕ) (i : ℕ) (ρ : List Bool)
    (rt : Option (Dig 256)) (pl : PlainPart (Compile.Batch.shapeOf L .onl) (annOf L .onl))
    (kind : _root_.Fmt.Kind) (hk : kind.num = D.kind (i + 1)) :
    (∀ k : Fin K,
      (famOf O D K (.fb .onl)
          (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl) : (Fin K → Dig 256) × Dig 256).1 k =
        bytesToDig
          (_root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
            (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl)
            (blockNo (D.work (i + 1)) K k.castSucc))) ∧
    (famOf O D K (.fb .onl)
        (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl) : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig
        (_root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
          (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl)
          (_root_.Fmt.firstBlock (D.work (i + 1)) - 1)) := by
  rw [← famP_eq]
  refine ⟨fun k => ?_, ?_⟩
  · show digS ((famB (fun _ => L) O D K (.fb .onl)
            (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl)).getD
          k.castSucc.val ByteArray.empty) = _
    rw [famB_row (fun _ => L) O hO D K i ρ rt pl kind hk k.castSucc, digS_eq]
  · show digS ((famB (fun _ => L) O D K (.fb .onl)
            (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl)).getD
          (Fin.last K).val ByteArray.empty) = _
    rw [famB_row (fun _ => L) O hO D K i ρ rt pl kind hk (Fin.last K), blockNo_last, digS_eq]

/-- Under the hypothesis below: the wire's message without its test bits is made of the blocks of
the verifier's message. -/
theorem old_grind {Cc : Type} {K : ℕ} (ch : (Fin K → Dig 256) → Cc) (B : ℕ → ByteArray) :
    ∀ (w : ℕ) (u : Fin (K + 1) → Dig 256),
      (∀ k : Fin (K + 1), u k = bytesToDig (B (blockNo w (K + 1) k.castSucc))) →
      ∃ mb : Fin K → Dig 256,
        GChal.old (chalGrind ch w u) = ch mb ∧
        ∀ i : Fin K, mb i = bytesToDig (B (_root_.Fmt.firstBlock w + i.val))
  | 0, u, hu => by
      refine ⟨firstBlocks 256 (K + 1) K u, rfl, fun i => ?_⟩
      have hi : i.val < K + 1 := by have := i.isLt; omega
      have e : firstBlocks 256 (K + 1) K u i = u ⟨i.val, hi⟩ := by
        unfold firstBlocks
        exact dif_pos hi
      rw [e, hu, blockNo_msg0 (K + 1) ⟨i.val, hi⟩]
  | b + 1, u, hu => by
      refine ⟨fun i => u i.succ, rfl, fun i => ?_⟩
      show u i.succ = _
      rw [hu]
      have e : blockNo (b + 1) (K + 1) (i.succ.castSucc) = _root_.Fmt.firstBlock (b + 1) + i.val :=
        blockNo_msgW (b + 1) (K + 1) i.val (Nat.succ_ne_zero b) (by have := i.isLt; omega)
      rw [e]

/-- For w ≤ 64, under the hypotheses below: the wire's test is the format's proof-of-work test. -/
theorem pass_grind {Cc : Type} {K : ℕ} (ch : (Fin K → Dig 256) → Cc)
    (B : ℕ → ByteArray) (bs : Array ByteArray) :
    ∀ (w : ℕ) (u : Fin (K + 1) → Dig 256), w ≤ 64 →
      (∀ k : Fin (K + 1), u k = bytesToDig (B (blockNo w (K + 1) k.castSucc))) →
      bs.getD 0 ByteArray.empty = B 0 → GChal.pass (chalGrind ch w u) = _root_.Fmt.passesA w bs
  | 0, _, _, _, _ => by
      show decide (∀ i : Fin 0, _) = _
      simp [_root_.Fmt.passesA]
  | b + 1, u, hw, hu, h0 => by
      rw [_root_.Fmt.passes_bits (b + 1) hw]
      unfold _root_.Fmt.passesBits
      rw [h0, ← pass_bits (B 0) (b + 1) hw]
      have e : u 0 = bytesToDig (B 0) := by
        rw [hu 0]
        have e0 : blockNo (b + 1) (K + 1) ((0 : Fin (K + 1)).castSucc) = 0 :=
          blockNo_test (b + 1) (K + 1) (Nat.succ_ne_zero b) (Nat.succ_pos K)
        rw [e0]
      show decide (∀ i : Fin (b + 1), testBits 256 (b + 1) (u 0) i = false) = _
      rw [e]

theorem old_mk {P : Type} (p : P) (ν : ℕ) : ∀ w : ℕ, GPlain.old (GPlain.mk (W := ℕ) w p ν) = p
  | 0 => rfl
  | _ + 1 => rfl

theorem nonce_mk {P : Type} (p : P) (ν : ℕ) :
    ∀ w : ℕ, (w ≠ 0 ∨ ν = 0) → GPlain.nonce (GPlain.mk (W := ℕ) w p ν) = ν
  | 0, h => (h.resolve_left fun h' => h' rfl).symm
  | _ + 1, _ => rfl

/-- The root of a round's component, off the list of roots. -/
theorem takeRt_fit (has : Bool) (R rest : List ByteArray)
    (h : has = true ↔ R.length ≠ 0) (h1 : R.length ≤ 1) :
    takeRt has ((R ++ rest).map bytesToDig) =
      some (R.head?.map bytesToDig, rest.map bytesToDig) := by
  cases R with
  | nil =>
      have : has = false := by
        cases has
        · rfl
        · exact absurd rfl (h.1 rfl)
      subst this
      rfl
  | cons x R' =>
      have hR : R' = [] := by
        cases R' with
        | nil => rfl
        | cons _ _ => simp at h1
      subst hR
      have : has = true := h.2 (by simp)
      subst this
      rfl

theorem roots_size (f : _root_.Fmt.Fld) (ts : List Item) (msg : ByteArray) (l : List ItemValue)
    (h : _root_.Fmt.whole (_root_.Fmt.readItems f ts) msg = some l) :
    ∀ d ∈ _root_.Fmt.rootsOf l, d.size = 32 := by
  unfold _root_.Fmt.whole at h
  rcases h1 : _root_.Fmt.readItems f ts msg 0 with _ | ⟨y, j⟩
  · simp [h1] at h
  · simp only [h1] at h
    by_cases hj : j = msg.size
    · rw [if_pos hj] at h
      obtain rfl := Option.some.inj h
      exact (items_only f ts msg 0 y j (Nat.zero_le _) h1).1
    · rw [if_neg hj] at h
      cases h

/-- A local round after the first: the chain's step. -/
theorem chainP_lo {I X : Type} {lam K : ℕ} {y : X} (Lf : Unit → BatchProtocol I X)
    (g : Fam (spec lam K (Lf ()))) (t : Tag) (cms : List (Dig lam)) (salt : Bits) (rtreq : Dig lam)
    (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts rts' : List (Dig lam)) (rt : Option (Dig lam)) (pl : r.Plain)
    (pls : Plains (up Ss)) (ht : takeRt w.hasJ rts = some (rt, rts')) :
    chainP Lf g id none t cms (some y : Option X) salt rtreq (r :: Ss) (r.lo, A) (w, W) embP i
        (.loc v) rts (pl, pls) =
      (chainP Lf g id none t cms (some y : Option X) salt rtreq Ss A W
        (fun z => embP (.inr z)) (i + 1)
        (.loc (List.ofFn
            (g (OracleName.fb t)
              (⟨i, .f2 none v, rt,
                embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
        rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f2 none v, rt,
                    embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some rt), z.2.1),
            z.2.2) := by
  show (match takeRt w.hasJ rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [ht]
  rfl

/-! ## The rounds, by induction -/

section Rounds
variable (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (S : _root_.Fmt.Spec) (C : CK)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)
  (hkit : KitFits S.plan.field C K chal) (cms : List (Dig 256)) (salt : Bits) (rtreq : Dig 256)

include hO hkit in
theorem chain_ind :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (uL C ds) (allLo (SL C ds)) →
          PlainPart (Compile.Batch.shapeOf (LbS C (rds S) dec) .onl) (annOf (LbS C (rds S) dec) .onl))
        (pl : Plains (uL C ds)),
      FitL ds rs → (∀ k, S.rounds[i + k]? = rs[k]?) →
      (∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      (∀ n rt z,
        (PDS S C dec).msg n rt (embP z) = msgSL C (rt.getD ByteArray.empty) ds (embPL C ds z)) →
      (∀ n z, (PDS S C dec).nonce n (embP z) = nonceSL C ds (embPL C ds z)) →
      c.label = S.label → c.round = i → bitsToBytes v = c.rho →
      TraceL (_root_.Fmt.HO O) S.plan rs ros c roots → plainsSL C ds ros = some pl →
      ∃ (ρ : Rho (uL C ds)) (v' : Bits),
        chainP (fun _ => LbS C (rds S) dec) (famOf O (PDS S C dec) (K + 1)) id none .onl cms
            (some () : Option Unit) salt rtreq (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
            embP (i + 1) (.loc v)
            ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig) pl =
          some (ρ, rtSL C ds ros, .loc v') ∧
        drawnSL C ds ρ = ros.map (·.drawn) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c
  | [], [], [], i, c, roots, v, embP, pl, _, _, _, _, _, _, _, _, _, _ => ⟨(), v, rfl, rfl, rfl⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | [], _ :: _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, [], _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | d :: ds, r :: rs, ro :: ros, i, c, roots, v, embP, pl, hf, hsuf, hroom, hmsg, hnon, hlab, hrnd, hv, ht, hp => by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      -- the typed plain parts
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      rcases hp1 : plainsSL C ds ros with _ | pls
      · simp [plainsSL, hp0, hp1] at hp
      simp only [plainsSL, hp0, hp1, Option.some.injEq] at hp
      subst hp
      -- the round's data in the spellings
      have hr0 : S.rounds[i]? = some r := by simpa using hsuf 0
      have hkind : r.kind.num = (PDS S C dec).kind (i + 1) := by
        show _ = if i + 1 = 0 then 7 else ((S.rounds[i + 1 - 1]?).map (·.kind.num)).getD 7
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, hr0]
        rfl
      have hwork : (PDS S C dec).work (i + 1) = r.entry.work := by
        show (if i + 1 = 0 then 0 else ((S.rounds[i + 1 - 1]?).map (·.entry.work)).getD 0) = _
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, hr0]
        rfl
      simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff, Bool.or_eq_true,
        bne_iff_ne, beq_iff_eq] at hask
      obtain ⟨-, hrho, -, -, hw64, -, hw0, -⟩ := hask
      -- the root
      have hlen : (_root_.Fmt.rootsOf ro.vals).length = r.entry.roots := by
        rw [roots_ofGots d.items ro.vals p0 hp0, hit, hcount]
      have htake := takeRt_fit d.tree.isSome (_root_.Fmt.rootsOf ro.vals)
        (ros.flatMap fun r => _root_.Fmt.rootsOf r.vals)
        (by rw [hlen]; exact htree) (by rw [hlen]; exact h1)
      have hsz := roots_size S.plan.field r.items ro.msg ro.vals hwhole
      have hrt : ∀ x ∈ _root_.Fmt.rootsOf ro.vals, x =
          ((((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig).map digToBytes).getD
            ByteArray.empty) := by
        intro x hx
        rcases hR : _root_.Fmt.rootsOf ro.vals with _ | ⟨y, R'⟩
        · rw [hR] at hx; cases hx
        · have hR' : R' = [] := by
            cases R' with
            | nil => rfl
            | cons _ _ => rw [hR] at hlen; simp at hlen; omega
          subst hR'
          rw [hR] at hx hsz
          obtain rfl := List.mem_singleton.1 hx
          show x = digToBytes (bytesToDig x)
          rw [TieTree.dig_bytes x (hsz x (List.mem_singleton.2 rfl))]
      -- message and nonce as the spellings give them
      have hM : (PDS S C dec).msg (i + 1)
            (((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig).map digToBytes)
            (embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))) = ro.msg := by
        rw [hmsg]
        show PlainOf.bytes _ d.items
            (GPlain.old (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce)) = _
        rw [old_mk]
        exact (msg_bytes S.plan.field d.items ro.msg ro.vals p0 _
          (by rw [hit]; exact hwhole) hp0 hrt).1
      have hN : (PDS S C dec).nonce (i + 1)
            (embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))) = ro.nonce := by
        rw [hnon]
        show GPlain.nonce (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce) = _
        exact nonce_mk p0 ro.nonce d.entry.work (by rw [he]; exact hw0)
      -- the typed answer
      have hrow := famOf_row O hO (PDS S C dec) (K + 1) i v
        ((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig)
        (embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))) r.kind hkind
      rw [hM, hN, hwork, hv] at hrow
      obtain ⟨hu, hnext⟩ := hrow
      have hwE : d.entry.work = r.entry.work := congrArg (·.work) he
      have hu' : ∀ k : Fin (K + 1),
          (famOf O (PDS S C dec) (K + 1) (.fb .onl)
                (⟨i + 1, .f2 none v,
                  (_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig,
                  embP (.inl (.inr
                        (GPlain.mk d.entry.work p0
                          ro.nonce)))⟩ : FbIn 256 (LbS C (rds S) dec) .onl) : (Fin (K + 1) → Dig 256) × Dig 256).1
              k =
            bytesToDig
              (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS S C dec).label c.rho (i + 1) ro.msg r.kind
                r.entry.work ro.nonce (blockNo d.entry.work (K + 1) k.castSucc)) :=
        fun k => (hu k).trans (by rw [hwE])
      -- the page's row
      have hbs : rowBs (_root_.Fmt.HO O) c r ro =
          _root_.Fmt.fetchW (m := Id) (_root_.Fmt.HO O) S.label c.rho (i + 1)
            ro.msg r.kind r.entry.work ro.nonce
            (_root_.Fmt.firstBlock r.entry.work +
              _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind)) := by
        unfold rowBs
        rw [hlab, hrnd]
        rfl
      have hsize : (rowBs (_root_.Fmt.HO O) c r ro).size =
          _root_.Fmt.firstBlock r.entry.work +
            _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) := by
        rw [hbs, _root_.Fmt.size_fetchW]
      have hget : ∀ b, b < (rowBs (_root_.Fmt.HO O) c r ro).size →
          (rowBs (_root_.Fmt.HO O) c r ro).getD b ByteArray.empty =
            _root_.Fmt.blockW (_root_.Fmt.HO O) (PDS S C dec).label c.rho (i + 1)
              ro.msg r.kind r.entry.work ro.nonce b := by
        intro b hb
        rw [hsize] at hb
        rw [hbs]
        exact _root_.Fmt.fetchW_getD _ _ _ _ _ _ _ _ _ b hb
      have hfb : 1 ≤ _root_.Fmt.firstBlock r.entry.work := by
        unfold _root_.Fmt.firstBlock; split <;> omega
      have hB32 : ∀ b,
          (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS S C dec).label c.rho (i + 1)
              ro.msg r.kind r.entry.work ro.nonce b).size = 32 :=
        fun b => size_blockW_HO O hO _ _ _ _ _ _ _ _
      -- the next round
      have hv' : bitsToBytes
            (List.ofFn
              (famOf O (PDS S C dec) (K + 1) (.fb .onl)
                (⟨i + 1, .f2 none v,
                  (_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig,
                  embP (.inl (.inr
                        (GPlain.mk d.entry.work p0
                          ro.nonce)))⟩ : FbIn 256 (LbS C (rds S) dec) .onl) : (Fin (K + 1) → Dig 256) × Dig 256).2) =
          (nextOf (_root_.Fmt.HO O) c r ro).rho := by
        rw [hnext]
        show digToBytes (bytesToDig _) =
          _root_.Fmt.nextA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro)
        rw [TieTree.dig_bytes _ (hB32 _)]
        unfold _root_.Fmt.nextA
        rw [hget _ (by rw [hsize]; omega)]
      obtain ⟨ρ', v'', hch, hdr, hps⟩ :=
        chain_ind ds rs ros (i + 1) (nextOf (_root_.Fmt.HO O) c r ro) _ _
          (fun z => embP (.inr z)) pls hf' (fun k => by
            have := hsuf (k + 1); rw [List.getElem?_cons_succ] at this; rw [← this]; congr 1; omega)
        (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr')) (fun n rt z => hmsg n rt (.inr z))
          (fun n z => hnon n (.inr z)) hlab (by show c.round + 1 = i + 1; rw [hrnd]) hv' ht' hp1
      refine ⟨((wireS C K chal d).chal
            (famOf O (PDS S C dec) (K + 1) (.fb .onl)
              (⟨i + 1, .f2 none v,
                (_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig,
                embP (.inl (.inr
                      (GPlain.mk d.entry.work p0
                        ro.nonce)))⟩ : FbIn 256 (LbS C (rds S) dec) .onl) : (Fin (K + 1) → Dig 256) × Dig 256).1,
          ρ'),
        v'', ?_, ?_, ?_⟩
      · have hstep := chainP_lo (y := ()) (fun _ => LbS C (rds S) dec)
          (famOf O (PDS S C dec) (K + 1)) .onl cms salt rtreq (roundS C d) (SL C ds)
          (allLo (SL C ds)) (wireS C K chal d) (wiresSL C K chal ds) embP (i + 1) v
          (((ro :: ros).flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig)
            _ _ (GPlain.mk d.entry.work p0 ro.nonce) pls (by rw [List.flatMap_cons]; exact htake)
        refine hstep.trans ?_
        rw [hch]
        rfl
      · show C.dr d.entry d.kind
              (GChal.old (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work _)) ::
            drawnSL C ds ρ' =
          ro.drawn :: ros.map (·.drawn)
        obtain ⟨mb, hmb, hmbB⟩ := old_grind (chal d.entry d.kind)
          (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS S C dec).label c.rho (i + 1)
            ro.msg r.kind r.entry.work ro.nonce)
          d.entry.work _ hu'
        rw [hmb, hdr, hdrawn]
        congr 1
        rw [hwE] at hmbB
        have := drawn_eq _ hB32 r.entry.work _ (rowBs (_root_.Fmt.HO O) c r ro)
          hsize hget S.plan.field C K chal hkit d.entry d.kind (by rw [he, hk])
          (hroom r List.mem_cons_self) mb hmbB
        rw [this, he, hk]
      · show (GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work _) &&
            passSL C ds ρ') =
          (_root_.Fmt.passesA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) &&
            passL (_root_.Fmt.HO O) rs ros (nextOf (_root_.Fmt.HO O) c r ro))
        rw [hps,
          pass_grind (chal d.entry d.kind)
            (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS S C dec).label c.rho (i + 1)
              ro.msg r.kind r.entry.work ro.nonce)
            (rowBs (_root_.Fmt.HO O) c r ro) d.entry.work _ (by rw [hwE]; exact hw64)
            hu' (hget 0 (by rw [hsize]; omega)), hwE]

end Rounds

/-! ## E. The first query, and the whole -/

theorem first_bytes (pd st run : ByteArray) (h : run.size = 32) :
    Run.firstBytes pd st (bytesToBits run) =
      _root_.Fmt.firstBytes pd st ByteArray.empty (some run) := by
  have hne : (bytesToBits run).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff]
    intro e
    have := length_bytesToBits run
    rw [e, h] at this
    simp at this
  unfold Run.firstBytes _root_.Fmt.firstBytes
  rw [hne, bitsToBytes_bytesToBits, ByteArray.append_empty]
  rfl

theorem size_HO32 (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (n t i : ℕ)
    (s b : ByteArray) (hn : n ≠ 162) :
    (_root_.Fmt.HO O n t i s b).size = 32 := by
  unfold _root_.Fmt.HO
  rw [if_neg hn]
  exact hO _

/-- The typed answer to the first query: its chain value. -/
theorem famOf_first {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) (D : PageD L .onl)
    (K : ℕ) (pd : Dig 256) (x : Option X) (salt : Bits) (rt : Option (Dig 256))
    (pl : PlainPart (Compile.Batch.shapeOf L .onl) (annOf L .onl)) :
    (famOf O D K (.fb .onl)
        (⟨0, .f1 [pd] x salt, rt, pl⟩ : FbIn 256 L .onl) : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig
        (O (_root_.Fmt.oStr 0 160 0 D.label _root_.Fmt.zero32
            (Run.firstBytes (digToBytes pd) (D.stm x) salt))) := by
  show ansOf O
      (if (Fin.last K).val = K then
          some
            ⟨0, 160, 0, D.label, _root_.Fmt.zero32, Run.firstBytes (digToBytes pd) (D.stm x) salt⟩
        else none) = _
  rw [if_pos (Fin.val_last K)]
  rfl

theorem firstValue_HO (O : ByteArray → ByteArray) (lab : ℕ)
    (pd st rec : ByteArray) (run : Option ByteArray) :
    _root_.Fmt.firstValueW (m := Id) (_root_.Fmt.HO O) lab pd st rec run =
      O (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32 (_root_.Fmt.firstBytes pd st rec run)) := rfl

/-- The first round: the chain's step. -/
theorem chainP_first {I X : Type} {lam K : ℕ} {y : X} (Lf : Unit → BatchProtocol I X)
    (g : Fam (spec lam K (Lf ()))) (t : Tag) (cms : List (Dig lam)) (salt : Bits) (rtreq : Dig lam)
    (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (rts : List (Dig lam)) (pl : r.Plain) (pls : Plains (up Ss)) (hw : w.hasJ = false) :
    chainP Lf g id none t cms (some y : Option X) salt rtreq (r :: Ss) (r.lo, A) (w, W)
        embP 0 .first rts (pl, pls) =
      (chainP Lf g id none t cms (some y : Option X) salt rtreq Ss A W (fun z => embP (.inr z)) 1
        (.loc (List.ofFn
            (g (OracleName.fb t)
              (⟨0, .f1 cms (some y) salt, none,
                embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
        rts pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨0, .f1 cms (some y) salt, none,
                    embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some none), z.2.1),
            z.2.2) := by
  show (match takeRt w.hasJ rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [hw]
  rfl

/-- The head says in words what it states. -/
theorem pi_chain : Spec.pi_chain := by
  intro O hO S C K chal dec hok hkit hroom o run pl hL hrun hpl
  obtain ⟨rnd, -, hr⟩ := hL.run
  have hrun32 : run.size = 32 := by
    rw [hrun] at hr
    rw [Option.some.inj hr]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  have hpd32 : o.pd.size = 32 := by
    rw [hL.pd]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  have hv : bitsToBytes
    (List.ofFn
      (famOf O (PDS S C dec) (K + 1) (.fb .onl)
        (⟨0, .f1 [bytesToDig o.pd] (some ()) (bytesToBits run),
          none,
          embPS C (rds S) dec
            (.inl (.inr
                ()))⟩ : FbIn 256 (LbS C (rds S) dec) .onl) : (Fin (K + 1) → Dig 256) × Dig 256).2) =
      o.rho0 := by
    rw [hL.rho0 run hrun, famOf_first, firstValue_HO]
    show digToBytes
        (bytesToDig
          (O (_root_.Fmt.oStr 0 160 0 S.label _root_.Fmt.zero32
              (Run.firstBytes (digToBytes (bytesToDig o.pd)) S.statement (bytesToBits run))))) = _
    rw [TieTree.dig_bytes _ (hO _), TieTree.dig_bytes _ hpd32, first_bytes _ _ _ hrun32]
  obtain ⟨ρ, v, hch, hdr, hps⟩ :=
    chain_ind O hO S C K chal dec hkit [bytesToDig o.pd] (bytesToBits run) (fun _ => false)
      (rds S) S.rounds o.rounds.toList 0 ⟨S.label, o.rho0, 0⟩ #[] _
      (fun z => embPS C (rds S) dec (.inr z)) pl (fit_rds S hok) (fun k => by rw [Nat.zero_add])
      hroom (fun _ _ _ => rfl) (fun _ _ => rfl) rfl rfl hv hL.trace hpl
  refine ⟨ρ, v, ?_, hdr, hps⟩
  refine (chainP_first (y := ()) (fun _ => LbS C (rds S) dec) (famOf O (PDS S C dec) (K + 1)) .onl
    [bytesToDig o.pd] (bytesToBits run) (fun _ => false) (s0 C) (SL C (rds S))
    (allLo (SL C (rds S))) (wire0S C K chal) (wiresSL C K chal (rds S)) (embPS C (rds S) dec)
    ((rootsB o).map bytesToDig) () pl rfl).trans ?_
  have hch' := hch
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hch'
  show Option.map _
      (chainP _ _ id none .onl _ _ _ _ (SL C (rds S)) _ _ _ 1 _
        ((o.rounds.toList.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig) pl) = _
  rw [hch']
  show some ((_, ρ), _) = some ((default, ρ), _)
  rw [Subsingleton.elim ((wire0S C K chal).chal _) default]

end Run.PQ
