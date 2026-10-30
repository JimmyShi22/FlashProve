-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeParts.lean: THE FRAME'S SENTENCE "THE EXCHANGE"
(`Exchange`, Honest/Thread/Pays.lean) CUT INTO ITS PARTS: a form into which a kind's theorems on
the items of its own row are laid. The first part is general in the thread: no kind is named. The
second says what a row of the first chain's table owes at a place inside a segment.

  `ExchangeParts`       the parts, by name
  `exchange_of_parts`   the parts give `Exchange T b`
  `owes_at_link`        at the first chain's thread, at a place inside a segment: the row owes what
                          the table's row opens, then what it reads and leaves

THE PARTS. row: the row owes the items "outs", then the items "ctx". asked: each of "ctx" is open in
front. input: the member's step leaves the prover's input. outs: FROM THE THREAD IN FRONT AND THE
MEMBER'S STEP EACH OF "outs" HOLDS BEHIND: the kind's own debt. carried: each of "ctx" says behind,
of any witness, what it says in front: the frame's sentence on what is carried past a member leaves
out the items that the row owes, so these are owed here.

WHY "asked" AND "carried" DO FOR "ctx". The thread holds an open item at EVERY continuation of the
challenges heard; behind the member the challenges heard are those in front and the member's own: so
a continuation behind is a continuation in front, and the witness is the same term.

FOR THE LOOKUP ON A LINK'S CALLS "outs" are: the forms of the run "objects"; what the planes, the
keys and the rider are worth. For the lookup on the digits: the forms of "objects"; planes; keys.
Honest/K3/Law/Thread/ExchangeSite.lean and ExchangeObjects.lean conclude the library's sentences
beneath these items. Typed since this head was first written, all conditional: the step to the item
on the forms of "objects", at a meaning's field (`formsT_field`, `forms_field`, ExchangeField.lean)
and at the composed meaning (`formsT_at_mgAll`, ExchangeAtMgAll.lean; `formsText_mgAll`,
FormsAtMgAll.lean); all of "outs" as `L.thread.Items` (`allOpenings_digitsLookup`, `all_attention`, `all_layers`,
ExchangeAll.lean; `all_head`, ExchangeHeadAll.lean). `exchange_row` (ExchangeRow.lean) builds
`ExchangeParts` under hOuts and hCar; the theorems `exchange_digits…` end in `Exchange L.thread b`.
No instance of `ExchangeParts` without hypotheses is exhibited in this file.

Limits. `Exchange` is a premise's form of the frame's. Nothing is shown of any item here. Nothing on
soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (rowOf)
open ProofFile.Honest.FirstThread (Letters)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **The exchange at the member number b, in parts.** outs: what the row opens. ctx: what it reads
and leaves. -/
structure ExchangeParts (b : Nat) (outs ctx : List T.ι) : Prop where
  row : (T.row b).owes = outs ++ ctx
  asked : ∀ i ∈ ctx, i ∈ T.opened b
  input : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    y.2.st.input = m.st.input
  outs : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items outs k s' y.2 (E.add y.1)
  carried : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ i ∈ ctx, ∀ v,
    T.means m.st.input i (T.seat k m s) (T.strs E) v →
    T.means m.st.input i (T.seat k y.2 s') (T.strs (E.add y.1)) v

variable {T}

/-- **The parts give the exchange.** CONDITIONAL ON `ExchangeParts`. No instance of these hypotheses
is exhibited in this file. -/
theorem exchange_of_parts {b : Nat} {outs ctx : List T.ι} (P : ExchangeParts T b outs ctx) :
    Exchange T b := by
  intro blk hb k s m E ds y cols s' hA hd hSt ds' i hi
  rw [P.row] at hi
  rcases List.mem_append.1 hi with h | h
  · exact P.outs blk hb k s m E ds y cols s' hA hd hSt ds' i h
  · have hin := P.input blk hb k s m E ds y cols s' hA hd hSt
    obtain ⟨⟨⟨l, _, hy⟩, _⟩, _⟩ := hSt
    have hh := play_heard l ds [] m y hy
    have hfront := hA.2.2.2.1 (ds ++ ds') i (P.asked i h)
    rw [hin, hh, List.append_assoc]
    exact P.carried blk hb k s m E ds y cols s' hA hd ⟨⟨⟨l, by assumption, hy⟩, by assumption⟩,
      by assumption⟩ i h _ hfront

end

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok M)

/-- **At a place inside a segment the first chain's row owes what the table's row opens, then what
it reads and leaves.** -/
theorem owes_at_link {b i : Nat} {a : Place} (hk : L.ps[b]? = some a) (hl : a.link = some i) :
    (L.thread.row b).owes = (rowOf L.links a).outs ++ (rowOf L.links a).ctx := by
  show (FirstRows.rows L.links L.ps b).owes = _
  unfold FirstRows.rows
  rw [hk]
  show (FirstRows.turn a _).owes = _
  unfold FirstRows.turn
  rw [hl]
  rfl

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.exchange_of_parts
#print axioms ProofFile.Honest.K3.Law.AtThr.owes_at_link
