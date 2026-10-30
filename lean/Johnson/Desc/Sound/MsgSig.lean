-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MsgSig.lean: THE ORACLES' STRINGS READ AS THE LIBRARY's OWN WORDS: the three
readings under which a boundary's relation is the library's joint over a signature. Definitions, and
small lemmas.

THE NOTIONS ARE THE LIBRARY's, CALLED, NOT REWRITTEN: `Cb.Sig`, `Sig.decs` (the decoder with the
sample: the nearest code word among those whose message has the sample's answers; nothing beyond the
radius), `Sig.CF` (no oracle message has two members of its list with one answer at its sample's
seed), `Sig.over` (Cb/Ld/LdSig.lean); `Johnson.Pack.sigOf cs l` (Johnson/Pack/PortF.lean): the
signature of a sending, a function of the programs' codes and of the list of the sampled messages'
shapes, each with its radius.

  `rowAt`: a row's symbol out of a tenant's words at a leaf: one word over the base field, three
    over the extension field (`toF`, `toE`: OnBytes/Slice/Field.lean).
  `wordsOf G cs l seat y`: THE FIRST READING: the words, OFF PLAIN STRINGS (`Strs`,
    Johnson/Desc/Msg.lean; from the rule's own oracles: `strsOf`, MsgAt.lean): so all notions here
    have the types of the table of joints' letters. seat: for each member of the signature the tree
    (its number through the file) and the tenant that holds it. Leaf by leaf the tenant's main and
    mask words (`wordOf`, Johnson/Desc/Msg.lean), row by row.
  `SeatFits`: a test on the plan alone: each member's tree is told, has as many leaves as the
    member's code has long positions, and its tenant's words are the shape's rows.
  `ShownAt`: every leaf of a member shows its symbol. WHY IT STANDS BESIDE: where a tree is not
    sent, or a column has not its words, `wordsOf` falls to 0, AND THE ZERO WORD IS A CODE WORD.
  `MsgT`, `Wit.tab`, `msgsOf`: THE THIRD READING: the witness's messages. M := mask row or main row,
    row, place ↦ an element of the extension field, total. Which message a member is: `Reading.arr`
    at its seat. AT THE PAD's PLACES (`padB`, Johnson/Desc/SeatAt.lean; it is the library's `padP`:
    `padB_inl`, `padB_inr`, proved) THE TABLE IS READ OFF THE SEAT's OWN COMPONENT (`Wit.pad`): a
    message that is kept and sent again is sent with another pad, so one component for all copies
    could be pinned at none but one of them. The pin compares ALL entries, the pad's too.
  THE SECOND READING, the samples off the chain's record, is a letter (`smp`), member by member:
  nothing
    where the record does not hold the member's sample.
  `PinAt`, `CfAt`: ONE MEMBER: the library's `OMsg.dec` gives the witness's message; no `OMsg.Clash`
    at the seed.
  `PinSig keep`, `CfSig keep`: the members in `keep` (a boundary may hold fewer than a sending's:
    those that are kept).
  `pinSig_over`, `cfSig_over` (proved): AT ALL MEMBERS THEY ARE, TO THE LETTER, THE FIRST HALVES OF
    `Sig.over`'s RELAXED RELATION (`∀ i, decs σ words i = some …`) AND OF ITS CONDITION (`CF σ
    words`), at the samples that the record holds. `pinSig_of_over`, `cfSig_of_over` (proved): and
    back, where the seats fit and every leaf is shown.
  `wordsStay`, `pinStays` (proved): past a block in front of which a member's tree was sent, its
    word is the same, and so are `PinAt` and `CfAt`, AT ONE RECORD: that the record behind the block
    still holds the sample is the block's duty.
Limits. `SeatFits` is a fact on the plan's letters alone: it is meant as one premise of whoever uses
the table, not as something that a block hands on. THAT EVERY LEAF OF A TREE IS SHOWN BEHIND THE
BLOCK THAT SENDS IT (a column of a tree that the stretch itself sends has its words by type) IS
OWED: the sending's row's duty. One signature is one sending's: a boundary's relation takes one
`PinSig` for each sending that is open there. A raw word that is not below the field's prime is read
as its residue (`toF`): the description's decision refuses a view in which an opened column holds
such a word (`viewWordsBelowPrime`, Johnson/Desc/Block.lean); of a leaf that is not opened nothing is asked. A
message without a sample is no member (PortF.lean's Limits). Nothing on soundness: that a sending's
block gives `PinSig` and `CfSig` behind it, but for the priced seeds, is the library's lemma on a
sending (`sigOf_send`), to be carried by that kind's own law.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StringsStay
import Johnson.Desc.SeatAt
import Johnson.Pack.PortF

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)

/-- The plain test on a pad's place is the library's, at a main row's entry. -/
theorem padB_inl (cs : OnBytes.Codes) (s : OnBytes.OracleShape)
    (x : Fin s.mainRows × Fin (pMain cs s).ell) :
    padB cs s false x.1.val x.2.val = true ↔ padP cs s (.inl x) := by
  unfold padB padP eachZ
  simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- And at a mask row's entry. -/
theorem padB_inr (cs : OnBytes.Codes) (s : OnBytes.OracleShape)
    (x : Fin s.maskRows × Fin (pMask cs s).ell) :
    padB cs s true x.1.val x.2.val = true ↔ padP cs s (.inr x) := by
  unfold padB padP
  simp only [if_true, Bool.and_eq_true, beq_iff_eq]
  exact Iff.rfl

/-- A row's symbol out of a tenant's words at a leaf: row number k. -/
def rowAt : (b : Bool) → List UInt64 → ℕ → RowTy b
  | true, ws, k => toF (ws.getD k 0)
  | false, ws, k => toE (ws.getD (3 * k) 0, ws.getD (3 * k + 1) 0, ws.getD (3 * k + 2) 0)

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat : Fin l.length → ℕ × ℕ)

/-- One member's word, off plain strings. -/
def wordAt (y : Strs) (i : Fin l.length) : ((sigOf cs l).om i).Str
  | .inl x => fun r =>
      rowAt _ (((wordOf G y (seat i).1 (seat i).2 x.val).map (·.main)).getD []) r.1.val
  | .inr x => fun r =>
      rowAt _ (((wordOf G y (seat i).1 (seat i).2 x.val).map (·.mask)).getD []) r.1.val

/-- **The first reading: the words.** -/
def wordsOf (y : Strs) : (sigOf cs l).ext.Str := fun i => wordAt G cs l seat y i

/-- **The seats fit**: a test on the plan alone. For each member: its tree is told; the tree has as
many leaves as the member's code has long positions; its tenant's main words are the shape's main
rows, each of its degree, and its mask words the shape's mask rows, three words each. WITHOUT IT: a
shorter code would leave the rest of the committed string unread; a longer one, or more rows than
words, would be filled with zeros. THE FIFTH CLAUSE: the library's word of main rows stands on the
main code's own positions: were the mask's code the longer, the later copies of a main row in the
tree would be read by nobody. THE SIXTH: THE TENANTS' WORDS ADD UP TO THE TREE's: else a description
could tell 0 words of a tree: an unsent tree's empty column would then "have its words", every leaf
would be shown, and the rows would read zeros: the zero word, a code word. THE SEVENTH: the degree
is 1 or 3: a main row is read one word or three a place. -/
def SeatFits : Prop :=
  ∀ i : Fin l.length, ∃ o n, G.oracleAt (seat i).1 = some o ∧ o.tenants[(seat i).2]? = some n ∧
    o.logLength = aOf cs (l.get i).1 ∧ n.main = (l.get i).1.mainRows * (l.get i).1.mainDeg ∧
    n.mask = (l.get i).1.maskRows * 3 ∧
    ((l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) ∧
    (o.tenants.map fun t => t.main + t.mask).sum = o.words ∧
    ((l.get i).1.mainDeg = 1 ∨ (l.get i).1.mainDeg = 3)

/-- Every leaf of member i shows its symbol. -/
def ShownAt (y : Strs) (i : Fin l.length) : Prop :=
  ∀ x : ℕ, x < 2 ^ aOf cs (l.get i).1 → (wordOf G y (seat i).1 (seat i).2 x).isSome = true

/-- The witness's messages: mask row or main row (true: mask), row, place. TO BE READ INSIDE A
MEMBER's RANGES ALONE (rows below its rows, places below its length): a pin fixes nothing outside
them. -/
abbrev MsgT : Type := Bool → ℕ → ℕ → GE

/-- **THE ONE ACCESSOR: the witness's table of a message of the shape s that has the number n and
sits at tenant t of tree j**: at the pad's places the seat's own component, elsewhere the message's,
which all copies share. WHOEVER READS A MESSAGE OFF A WITNESS READS IT THROUGH THIS: `w.msg n` at a
pad's place and `w.pad j t` outside the pad's places are pinned by nothing. -/
def _root_.VerifiableInference.Desc.Wit.tab {Cells Tok : Type} (w : Wit Cells Tok MsgT)
    (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (n j t : ℕ) : MsgT := fun mask row place =>
  if padB cs s mask row place = true then w.pad j t mask row place else w.msg n mask row place

/-- **The third reading: the witness's messages.** arr: which message a tenant of a tree holds
(`Reading.arr`, Johnson/Desc/Msg.lean): one number for all copies. -/
def msgsOf {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) : (sigOf cs l).Msg :=
  fun i j => match j with
    | .inl q => w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 false
        q.1.val q.2.val
    | .inr q => w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 true
        q.1.val q.2.val

variable {A Cells Tok : Type} (smp : A → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp)
  (arr : ℕ → ℕ → ℕ)

/-- **Member i is pinned**: the record holds its sample, every leaf is shown, and its word decodes,
with the sample, to the witness's message: the library's decoder with a sample (`OMsg.dec`). -/
def PinAt (i : Fin l.length) (a : A) (y : Strs) (w : Wit Cells Tok MsgT) : Prop :=
  ∃ z, smp a i = some z ∧ ShownAt G cs l seat y i ∧
    ((sigOf cs l).om i).dec (wordsOf G cs l seat y i) z = some (msgsOf cs l seat arr w i)

/-- **Member i has no collision**: the record holds its sample, EVERY LEAF IS SHOWN (it stands in
the promise too: a block that closes a pin is owed it in front, and could not deliver it), and no
two members of its word's list have one answer at the sample's seed: the library's `OMsg.Clash`. -/
def CfAt (i : Fin l.length) (a : A) (y : Strs) : Prop :=
  ∃ z, smp a i = some z ∧ ShownAt G cs l seat y i ∧
    ¬ ((sigOf cs l).om i).Clash (wordsOf G cs l seat y i) z.1

/-- **The members in `keep` are pinned**, and the seats fit. -/
def PinSig (keep : Fin l.length → Prop) (a : A) (y : Strs) (w : Wit Cells Tok MsgT) : Prop :=
  SeatFits G cs l seat ∧ ∀ i, keep i → PinAt G cs l seat smp arr i a y w

/-- **The members in `keep` have no collision.** -/
def CfSig (keep : Fin l.length → Prop) (a : A) (y : Strs) : Prop :=
  ∀ i, keep i → CfAt G cs l seat smp i a y

/-- AT ALL MEMBERS IT IS `Sig.over`'s OWN, TO THE LETTER: there are samples σ, those that the record
holds, at which the first half of the relaxed relation holds. -/
theorem pinSig_over (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : PinSig G cs l seat smp arr (fun _ => True) a y w) :
    ∃ σ : (sigOf cs l).Smp, (∀ i, smp a i = some (σ i)) ∧
      ∀ i, (sigOf cs l).decs σ (wordsOf G cs l seat y) i = some (msgsOf cs l seat arr w i) := by
  choose z hz using fun i => h.2 i trivial
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2.2⟩

/-- And so is the condition: `Sig.CF`. -/
theorem cfSig_over (a : A) (y : Strs) (h : CfSig G cs l seat smp (fun _ => True) a y) :
    ∃ σ : (sigOf cs l).Smp, (∀ i, smp a i = some (σ i)) ∧
      (sigOf cs l).CF σ (wordsOf G cs l seat y) := by
  choose z hz using fun i => h i trivial
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2.2⟩

/-- AND BACK: from the library's relaxed relation, at samples that the record holds, where the seats
fit and every leaf is shown. -/
theorem pinSig_of_over (a : A) (y : Strs) (w : Wit Cells Tok MsgT) (hS : SeatFits G cs l seat)
    (σ : (sigOf cs l).Smp) (hσ : ∀ i, smp a i = some (σ i)) (hsh : ∀ i, ShownAt G cs l seat y i)
    (h : ∀ i, (sigOf cs l).decs σ (wordsOf G cs l seat y) i = some (msgsOf cs l seat arr w i)) :
    PinSig G cs l seat smp arr (fun _ => True) a y w :=
  ⟨hS, fun i _ => ⟨σ i, hσ i, hsh i, h i⟩⟩

/-- And from the library's condition. -/
theorem cfSig_of_over (a : A) (y : Strs) (σ : (sigOf cs l).Smp) (hσ : ∀ i, smp a i = some (σ i))
    (hsh : ∀ i, ShownAt G cs l seat y i) (h : (sigOf cs l).CF σ (wordsOf G cs l seat y)) :
    CfSig G cs l seat smp (fun _ => True) a y :=
  fun i _ => ⟨σ i, hσ i, hsh i, h i⟩

/-- Past a block in front of which a member's tree was sent its word is the same. -/
theorem wordsStay (C : CK) (Fr : Frame) (b : ℕ) (ds : List RDT) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) (i : Fin l.length) (h : (seat i).1 < b) :
    wordsOf G cs l seat (strsOf Fr (behind C Fr b ds y τ)) i =
      wordsOf G cs l seat (strsOf Fr y) i := by
  unfold wordsOf wordAt
  rw [wordStays Xi G C Fr b ds y τ (seat i).1 (seat i).2 h]

/-- And so are its pin and its condition, at one record. -/
theorem pinStays (C : CK) (Fr : Frame) (b : ℕ) (ds : List RDT) (s : A) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) (w : Wit Cells Tok MsgT) (i : Fin l.length) (h : (seat i).1 < b) :
    (PinAt G cs l seat smp arr i s (strsOf Fr (behind C Fr b ds y τ)) w ↔
        PinAt G cs l seat smp arr i s (strsOf Fr y) w) ∧
      (CfAt G cs l seat smp i s (strsOf Fr (behind C Fr b ds y τ)) ↔
        CfAt G cs l seat smp i s (strsOf Fr y)) := by
  have e := wordsStay G cs l seat C Fr b ds y τ i h
  have e' : ShownAt G cs l seat (strsOf Fr (behind C Fr b ds y τ)) i ↔
      ShownAt G cs l seat (strsOf Fr y) i := by
    unfold ShownAt
    rw [wordStays Xi G C Fr b ds y τ (seat i).1 (seat i).2 h]
  unfold PinAt CfAt
  simp only [e, e']
  exact ⟨trivial, trivial⟩

end

end VerifiableInference.Desc.Sound
