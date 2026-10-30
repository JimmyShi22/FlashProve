-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3StoredThree.lean: THE SEVEN LETTERS FOR THE STORED TABLE IN THE LOOKUP's LAW AT A LAYERS' LINK AND AT THE HEAD (oW · wOf · nr · nc · smpW · strW · msgW), FILLED AS A CONDUIT FOR THE TABLE OF JOINTS' OWN ITEM pinW; AND THE SENTENCES THAT THE LAW's CALLERS ASK AT THEM. Definitions, statements and proofs.
WHAT A FOE WILL SAY, SAID FIRST: "oW IS NOT THE STORED TABLE's CODE." RIGHT: IT IS NOT MEANT TO BE.
 (a) What binds w.cells to the committed table is the table's own item pinW: pinWOf decT: decT y.cell a = some w.cells, decT THE ONE DECODER. It stands in the row's context at the layers and the head: part of the relation in front AND behind: the lookup's row neither makes nor closes it: other kinds' rows do, at the real decoder.
 (b) The three fields that the law's callers ask (tabIn · pinWIn · pinWOut) say: pinW ⟺ "oW.dec (strW y) σW = some (msgW w)", both ways, and "decodes" ⟹ "a sample is there and no clash". So the second half of the law's pin (LayPin, in LayFront and in LayBehind) is pinW in the library's dress. HERE THE DRESS IS CUT TO FIT: conduit_pin IS AN "IFF": just the w that pinW lets through pass.
 (c) The law reads the table's CONTENT through wOf (msgW w) alone: here wOf (msgW w) y c = w.cells y c inside the ranges (wOf_msgW): the very cells that pinW pins.
 (d) The law is general in oW: no premise on its code, list or sample; its error reads the caller's numbers, layout and side oracles, not the signature in which alone oW stands: no number hangs on oW, as long as nr and nc are the true numbers.
WHAT oW.dec IS SPENT FOR BEYOND CARRYING (a foe's reading of the library's own step from "for every tuple of messages" to "over the signature", sigLift_know, Cb/Ld/LdSigLiftProofs.lean): ONE THING: THAT THE DECODED TUPLE IS A FUNCTION OF THE STATEMENT: the bad challenges are counted at one tuple, fixed by samples and words before the draw. Every oracle message has that by type. Here (dec_word) its value is decT's own value at the strings' cells and z: what the one decoder gives.
WHAT WOULD BE HOLLOW, AND IS NOT DONE: a msgW that does not read w.cells; a strW that does not read decT's value.
WHAT THE CONDUIT DROPS: "no collision at the stored table's word" is true outright here (no_clash). The real "no collision" lives inside decT (a guarded decoder gives nothing at a collision): the table's "decodes" holds it.
THE TERMS. codeW: the identity code on the cells' entries, with one more coordinate, a flag that is 1 at every code word · oWc: that code at radius 0, one seed, no answer · wordOf: of a decoded matrix: its code word; of "nothing": the zero word (flag 0: off every code word) · strWc decT z s₀ y := wordOf (decT's value at y's cells) · smpWc: the one sample · msgWc w := w.cells' entries · wOfC.
z (the public part) STANDS IN strWc ALONE: so the callers' form is the one in which strW is a function of z (Johnson/Desc/First/Look/K3SeatLawsZ.lean). ONE PREMISE ON decT (NoRec): it does not read the first chain's record. THE RECORD's TYPE IS A LETTER S₁ HERE (meant: the first chain's record): nothing of it is read.

Limits. A filling of letters. codeW's encoder is AFFINE (the flag), not linear: the lookup's law asks no law of the code; whoever wants "decoding undoes encoding" at this oracle message has dec_word, not the library's lemma on codes. Nothing on what decT is. NO MEMBER IS SHOWN. Nothing on soundness by itself.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.Look.Stored
open Cb Cb.Ood Prob OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.Sound (Frame MsgT strsOf behind cellStays pinWOf decodesOf)

variable (rows cols : ℕ)

/-- The cells' entries. -/
abbrev JW : Type := Fin rows × Fin cols

/-- The matrices. -/
abbrev CellsW : Type := Fin rows → Fin cols → GE

/-- **The identity code on the cells' entries, with a flag.** -/
@[reducible] def codeW : LdCode GE Unit where
  NP := Unit
  NS := fun _ => Option (JW rows cols)
  J := JW rows cols
  Q := Empty
  enc := fun m _ _ s => match s with
    | some j => m j
    | none => 1
  Aa := Option (JW rows cols)
  T := fun f _ α => f () α
  src := fun _ => {()}

/-- **The conduit**: that code at radius 0; one seed, no answer. -/
@[reducible] def oWc : OMsg GE := OMsg.plain (codeW rows cols) (Sample.nil GE (JW rows cols)) 0 fun _ => 0

variable {rows cols}

/-- A matrix's entries, as a message. -/
def entries (c : CellsW rows cols) : (oWc rows cols).Msg := fun j => c j.1 j.2

theorem entries_inj {c c' : CellsW rows cols} (h : entries c = entries c') : c = c' := by
  funext i j
  exact congrFun h (i, j)

/-- The word of a decoder's value. -/
def wordOf : Option (CellsW rows cols) → (oWc rows cols).Str
  | some c => (codeW rows cols).enc (entries c) Empty.elim
  | none => fun _ _ => 0

/-- A count over one position. -/
theorem cnt_unit (Q : Unit → Prop) : cnt Q = 0 ↔ ¬ Q () := by
  constructor
  · intro h hq
    haveI : Nonempty {a : Unit // Q a} := ⟨⟨(), hq⟩⟩
    have h1 : 0 < Nat.card {a : Unit // Q a} := Nat.card_pos
    have h2 : Nat.card {a : Unit // Q a} = 0 := h
    omega
  · intro h
    exact cnt_false fun a ha => h ha

/-- The distance of a code word's own word from a pair: 0 just at its own message. -/
theorem dist_some (c : CellsW rows cols) (t : (oWc rows cols).Wit) :
    (oWc rows cols).dist (wordOf (some c)) t = 0 ↔ t.1 = entries c := by
  unfold OMsg.dist
  rw [cnt_unit]
  constructor
  · intro h
    have h1 := Classical.not_not.1 h
    funext j
    exact (congrFun h1 (some j)).symm
  · intro h
    refine Classical.not_not.2 ?_
    funext α
    cases α with
    | none => rfl
    | some j => exact (congrFun h j).symm

/-- The zero word is off every code word. -/
theorem dist_none (t : (oWc rows cols).Wit) : (oWc rows cols).dist (wordOf none) t ≠ 0 := by
  unfold OMsg.dist
  rw [Ne, cnt_unit]
  intro h
  have h1 := Classical.not_not.1 h
  have h2 : (0 : GE) = 1 := congrFun h1 none
  exact zero_ne_one h2

/-- **The conduit's decoder gives back the value of which the word was made.** -/
theorem dec_word (v : Option (CellsW rows cols)) (σ : (oWc rows cols).Smp) :
    (oWc rows cols).dec (wordOf v) σ = v.map entries := by
  unfold OMsg.dec decMin
  cases v with
  | none =>
    rw [dif_neg]
    · rfl
    · rintro ⟨t, -, ht⟩
      exact dist_none t (Nat.le_zero.1 ht)
  | some c =>
    have hex : ∃ t : (oWc rows cols).Wit,
        First ((oWc rows cols).dist (wordOf (some c))) (oWc rows cols).rank Prod.fst
          (oWc rows cols).Z.val σ.1 σ.2 t ∧ (oWc rows cols).dist (wordOf (some c)) t ≤ (oWc rows cols).e := by
      have h0 : (oWc rows cols).dist (wordOf (some c)) (entries c, fun q => q.elim) = 0 :=
        (dist_some c _).2 rfl
      refine ⟨(entries c, fun q => q.elim), ⟨funext fun s => s.elim, fun t' _ => ?_⟩, Nat.le_of_eq h0⟩
      rw [h0]
      rcases Nat.eq_zero_or_pos ((oWc rows cols).dist (wordOf (some c)) t') with h | h
      · exact Or.inr ⟨h.symm, Nat.le_refl _⟩
      · exact Or.inl h
    rw [dif_pos hex]
    exact congrArg some ((dist_some c _).1 (Nat.le_zero.1 hex.choose_spec.2))

/-- **No collision, ever**: at radius 0 a word's list has at most one message. -/
theorem no_clash (f : (oWc rows cols).Str) (ρ : (oWc rows cols).Z.D) : ¬ (oWc rows cols).Clash f ρ := by
  rintro ⟨u, u', ⟨r, hu⟩, ⟨r', hu'⟩, hne, -⟩
  have e1 := Classical.not_not.1 ((cnt_unit _).1 (Nat.le_zero.1 hu))
  have e2 := Classical.not_not.1 ((cnt_unit _).1 (Nat.le_zero.1 hu'))
  refine hne (funext fun j => ?_)
  exact (congrFun e1 (some j)).symm.trans (congrFun e2 (some j))

/-! ## The seven terms -/

section
variable {P S₁ Tok : Type} {Fr : Frame}
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S₁ → Option (CellsW rows cols))

/-- decT does not read the first chain's record. -/
def NoRec : Prop := ∀ c z s s', decT c (z, s) = decT c (z, s')

/-- The stored table's word: the word of decT's own value. s₀: any record. -/
def strWc (s₀ : S₁) (z : P) (y : Fr.E.Str) : (oWc rows cols).Str :=
  wordOf (decT (strsOf Fr y).cell (z, s₀))

/-- The one sample. -/
def smpWc (_ : S₁) : Option (oWc rows cols).Smp := some ((), fun s => s.elim)

/-- The witness's message: its cells' entries. -/
def msgWc (w : Wit (CellsW rows cols) Tok MsgT) : (oWc rows cols).Msg := entries w.cells

/-- The matrix, by numbers; 0 outside. -/
def wOfC (m : (oWc rows cols).Msg) (y c : ℕ) : GE :=
  if h : y < rows ∧ c < cols then m (⟨y, h.1⟩, ⟨c, h.2⟩) else 0

variable {decT}

/-- **THE HEART: THE SECOND HALF OF THE LAW's PIN IS pinW, BOTH WAYS.** -/
theorem conduit_pin (hS : NoRec decT) (s₀ : S₁) (z : P) (a : S₁ × Fr.E.Str)
    (w : Wit (CellsW rows cols) Tok MsgT) :
    (∃ σW, smpWc a.1 = some σW ∧
        (oWc rows cols).dec (strWc decT s₀ z a.2) σW = some (msgWc w)) ↔
      pinWOf decT (z, a.1) (strsOf Fr a.2) w := by
  unfold pinWOf strWc msgWc
  rw [hS _ z a.1 s₀]
  constructor
  · rintro ⟨σW, -, h⟩
    rw [dec_word] at h
    cases hv : decT (strsOf Fr a.2).cell (z, s₀) with
    | none => rw [hv] at h; cases h
    | some c =>
      rw [hv] at h
      exact congrArg some (entries_inj (Option.some.inj h))
  · intro h
    refine ⟨((), fun s => s.elim), rfl, ?_⟩
    rw [dec_word, h]
    rfl

/-- (1) -/
theorem tabIn_c (s₀ : S₁) (z : P) (a : S₁ × Fr.E.Str)
    (_ : decodesOf decT (z, a.1) (strsOf Fr a.2)) :
    ∃ σW, smpWc a.1 = some σW ∧ ¬ (oWc rows cols).Clash (strWc decT s₀ z a.2) σW.1 :=
  ⟨((), fun s => s.elim), rfl, no_clash _ _⟩

/-- (2) -/
theorem pinWIn_c (hS : NoRec decT) (s₀ : S₁) (z : P) (a : S₁ × Fr.E.Str)
    (w : Wit (CellsW rows cols) Tok MsgT) (h : pinWOf decT (z, a.1) (strsOf Fr a.2) w) :
    ∃ σW, smpWc a.1 = some σW ∧
      (oWc rows cols).dec (strWc decT s₀ z a.2) σW = some (msgWc w) :=
  (conduit_pin hS s₀ z a w).2 h

/-- (3) -/
theorem pinWOut_c (hS : NoRec decT) (s₀ : S₁) (z : P) (a : S₁ × Fr.E.Str)
    (w : Wit (CellsW rows cols) Tok MsgT)
    (h : ∃ σW, smpWc a.1 = some σW ∧
      (oWc rows cols).dec (strWc decT s₀ z a.2) σW = some (msgWc w)) :
    pinWOf decT (z, a.1) (strsOf Fr a.2) w :=
  (conduit_pin hS s₀ z a w).1 h

/-- (4) A later sending leaves the stored table's word. -/
theorem hstrW_c (C : _root_.Run.PQ.CK) (s₀ : S₁) (z : P) (base : ℕ) (ds : List RDT) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) :
    strWc decT s₀ z (behind C Fr base ds y τ) = strWc decT s₀ z y := by
  unfold strWc
  have e : (strsOf Fr (behind C Fr base ds y τ)).cell = (strsOf Fr y).cell :=
    funext fun x => cellStays C Fr base ds y τ x
  rw [e]

/-- (5) The sample reads nothing of the record. -/
theorem hsmpW_c (s s' : S₁) : smpWc (rows := rows) (cols := cols) s' = smpWc (rows := rows) (cols := cols) s := rfl

/-- (6) The message reads the witness's cells alone. -/
theorem msgW_cells (w w' : Wit (CellsW rows cols) Tok MsgT) (h : w.cells = w'.cells) :
    msgWc w = msgWc w' := by
  unfold msgWc
  rw [h]

/-- (7) What the law reads of the message IS the cells. -/
theorem wOf_msgW (w : Wit (CellsW rows cols) Tok MsgT) (y c : ℕ) (hy : y < rows) (hc : c < cols) :
    wOfC (msgWc w) y c = w.cells ⟨y, hy⟩ ⟨c, hc⟩ := by
  unfold wOfC
  rw [dif_pos ⟨hy, hc⟩]
  rfl

end

end VerifiableInference.Desc.First.Look.Stored

#print axioms VerifiableInference.Desc.First.Look.Stored.dec_word
#print axioms VerifiableInference.Desc.First.Look.Stored.no_clash
#print axioms VerifiableInference.Desc.First.Look.Stored.conduit_pin
#print axioms VerifiableInference.Desc.First.Look.Stored.tabIn_c
#print axioms VerifiableInference.Desc.First.Look.Stored.pinWIn_c
#print axioms VerifiableInference.Desc.First.Look.Stored.pinWOut_c
#print axioms VerifiableInference.Desc.First.Look.Stored.hstrW_c
#print axioms VerifiableInference.Desc.First.Look.Stored.msgW_cells
#print axioms VerifiableInference.Desc.First.Look.Stored.wOf_msgW
