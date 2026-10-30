-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ExchangeAtHead.lean: THE SHARED "SENDING" (the kind K1): OUR
SHARE OF ExchangeS AT THE ITEM row m (sample t), AT ProofFile's LETTERS AT THE LIBRARY's HEAD
(lettersHead, Honest/Thread/FirstHead.lean): THE TWO PUBLIC PREMISES ON THE VERIFIER's BOOK THAT
exchange_rows TAKES (ExchangeAtPins.lean) ARE PAID THERE. Four theorems; no definition.

The letters. 𝓛 := lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w: h is the library's head: A
HYPOTHESIS; H, Q and the rest are bound letters, handed on to lettersHead as they come. R : K1Seated
𝓛 b blk wit J own₀ sort arr seats₀ ms rad. Said: any sentence on a run.

  - exchange_rows_head: UNDER R, hb : b < 353, hmark (a yes of blk's decision leaves no mark) and
    hcl : classOf sort = some (m₀, t₀): ExchangeAtS 𝓛.thread Said b (.row m₀ (.sample t₀)).
  - exchange_rows_two: UNDER R at b = 2 and the sort "opening": at row 0 (sample 0).
  - exchange_rows_fifty: UNDER hl : l < 25, R at b = K1.noL l d, and hcl: at row m₀ (sample t₀).
  - exchange_rows_fifty_tied: UNDER hl : l < 25 and R at b = K1.noL l d AT THE SORT THAT THE PLACE
    HAS ("reads l" at d = false, "digits l" at d = true): at row l (sample 1) or row l (sample 2):
    hcl falls.

Who pays what. BookFits behind the step: ProofFile's head_bookFits_next_front
(Honest/Thread/BookFitsAt.lean): in front of number 353; it asks nothing of the mark. "A tree's
number is its place": ProofFile's head_treeNumber_next (Honest/Thread/BookFacts.lean), which asks that no
mark stands behind the step: the real member's own seat gives that: k1_two_noMark, k1_fifty_noMark
(MemberInScope.lean), at the scope, the files and the opened description that the head holds
(h.scope, h.reads, h.laid.opened). That blk stands at number b of the chain's flat list is R's field
member: 𝓛's list of blocks is cF.blocksInOrder.

The other three shares (exchange_pin, exchange_pinI, exchange_pinV, ExchangeAtPins.lean) take no
premise on the book: they need no twin here. So at these letters, at number 2 and at the fifty, no
premise on a state is left in our share of ExchangeS: it hangs on the head and on R (and, where the
sort is left free, on hcl, which says which class the sort has).

UNDER "Stepped": THE CUT IS THE FRAME's: IT HOLDS OF NOTHING AT A BOOK THAT DOES NOT COVER THE
PART's COUNT. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (THROUGH THE SEED's FACTOR: NOT AT A FACTOR
0, NOR AT A LIST OF SEEDS SHORTER THAN THE ANSWERS).

THE BOOK. The sentence, to the letter, with
its first arm, in marks: "At a book whose count at the part's address does not cover the part's due
this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is a premise
here." OUR OWN WORDS: it stands among the premises as the field hasCoins of the record K1Seated (the
binder R), at exchange_rows_head, exchange_rows_two, exchange_rows_fifty, exchange_rows_fifty_tied.

Limits. IT STANDS OVER FILES OF ProofFile's THAT ARE ON NO SEAL (BookFitsAt.lean, BookFacts.lean,
FirstHead.lean and what lies beneath them). R AT THESE LETTERS IS MET BY NOBODY: THE TIE (msgs,
pads) IS A PREMISE ON THE LETTER Q. W's sending (number 356) is not here: its sort has no class of
sample rows. These shares are not "the exchange". It is no completeness. Nothing on soundness or on
any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberInScope
import Johnson.Desc.ProofFile.Honest.Thread.BookFitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {b : Nat} {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
  {J : SendJob (PlaceIn ProofFile.Inst) X} {own₀ : X} {sort : K1Sort} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **AT lettersHead THE TWO PREMISES ON THE BOOK ARE PAID**, at a member in front of number 353
whose yes leaves no mark. UNDER "Stepped": THE CUT IS THE FRAME's: IT HOLDS OF NOTHING AT A BOOK
THAT DOES NOT COVER THE PART's COUNT. -/
theorem exchange_rows_head
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) b blk wit J own₀
      sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (hb : b < 353)
    (hmark : ∀ s rs gs t, blk.decide s rs gs = .ok t → t.failed = none) (m₀ t₀ : ℕ)
    (hcl : classOf sort = some (m₀, t₀)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b
      (.row m₀ (.sample t₀)) := by
  have hblk : cF.blocksInOrder[b]? = some blk := R.member
  refine exchange_rows R Said m₀ t₀ hcl
    (fun k s m E ds y cols s' hA hd hS =>
      head_bookFits_next_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hblk hA.1 hd hS)
    (fun k s m E ds y cols s' hA hd hS => ?_)
  obtain ⟨-, gs, hdec⟩ := K1.step_ok _ blk s s' _ _ _ hS.2
  exact head_treeNumber_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hA.1 hd hS
    (hmark _ _ _ _ hdec)

/-- **AT NUMBER 2**: the opening: its class of sample rows is row 0 (sample 0). -/
theorem exchange_rows_two
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 2 blk wit J own₀
      .opening arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 2
      (.row 0 (.sample 0)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact exchange_rows_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w R Said (by decide)
    (k1_two_noMark h.scope h.reads O R.member) 0 0 rfl

/-- **AT THE FIFTY.** -/
theorem exchange_rows_fifty {l : ℕ} (hl : l < 25) (d : Bool)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l d) blk
      wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (m₀ t₀ : ℕ)
    (hcl : classOf sort = some (m₀, t₀)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l d) (.row m₀ (.sample t₀)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have h6 : IM.k1Ix l d ≤ 6 := by unfold IM.k1Ix; split <;> split <;> omega
  exact exchange_rows_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w R Said
    (by show 14 * l + IM.k1Ix l d + 2 < 353; omega)
    (k1_fifty_noMark h.scope h.reads O hl d R.member) m₀ t₀ hcl

/-- **AT THE FIFTY, AT THE SORT THAT THE PLACE HAS**: "reads l" (d = false), "digits l" (d = true):
the class of sample rows is row l (sample 1) or row l (sample 2). -/
theorem exchange_rows_fifty_tied {l : ℕ} (hl : l < 25) (d : Bool)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l d) blk
      wit J own₀ (cond d (.digits l) (.reads l)) arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l d) (.row l (.sample (K1.momL d))) :=
  exchange_rows_fifty h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl d R Said l (K1.momL d)
    (by cases d <;> rfl)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchange_rows_head
#print axioms ProofFile.Honest.K1.exchange_rows_two
#print axioms ProofFile.Honest.K1.exchange_rows_fifty
#print axioms ProofFile.Honest.K1.exchange_rows_fifty_tied
