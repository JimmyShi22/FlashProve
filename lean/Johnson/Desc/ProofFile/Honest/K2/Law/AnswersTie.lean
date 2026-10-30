-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AnswersTie.lean: the kind "the code switch" (K2): WHAT THE
PART's SECOND MOVE SAYS, OF `switchRowsLaid`'s ROWS (Honest/K2/ScriptLots.lean): the shared
sending's `answers` (Johnson/Prover/Send/Core.lean) at the held words of these rows, AT ANY NUMBER f
OF THE SENDING's FIRST MESSAGE. The other half of Honest/K2/Law/RowsTie.lean, which ties the first
move. Five statements with their proofs; no definition.

  `value_sample_moves`  a sample row's value is the same at two statements and two numbers where
                        the codes are one, the message there is one and the words there are one
  `stAt_at`             the message number f + k of `stAt P f`
  `answers_moves`       THE SHIFT: the shared sending's answers at the number f are those at 0
  `answers_are`         the core's sender's answers in the shared sending's terms, at any f
  `says_two_of_rows`    THE END

By: `coefAt_sampleRow` (Johnson/Desc/K1/Law/Means.lean): a sample row's coefficients in closed form:
the two numbers enter by one comparison alone · `tableSize_eq` (Johnson/Desc/K1/Law/SaysTie.lean) ·
`switchRowsAt_again` (Honest/K2/Exact.lean): the second move's data are the first's. The first proof
goes as `says_iff`'s (SaysTie.lean), which has two premises more and a closed form for its end.
Twins, not imported: `stAt_core`, `answers_core` (Honest/K2/Law/CoreSenderLaw.lean): `answers_are` at f =
0; that file stands over other matter. Kin, not called: `answers_any`
(Honest/K1/Law/SendAtBlock.lean, of other authors): the same answers at any words beneath, at one
number. `value_sample_same` (Honest/K2/Law/ClearAtCore.lean): one statement and one number, two
families of words that are alike at that number; it asks for no message there, so it does not follow
from `value_sample_moves`, nor that from it. `answers_at_chain` (Honest/K1/AnswersChain.lean, of
other authors): the statement and the words may turn; the number stays.

Limits. `says_two_of_rows` ASKS `serves` AND `roomy`: the second move does not test them,
`switchRowsLaid` does. AT `coreSender freshTable` ALONE. It is an equation of two values that may
both be refusals: that the rows are laid is not said here. THE 0 BENEATH THE HELD WORDS is a
constant. Where the list of seeds is too short `answers` reads a default, on both sides alike:
nothing refuses. It says which function of the rows and the challenge the answers are: nothing on
what they show. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsTie
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchMoves
import Johnson.Desc.ProofFile.Honest.K2.Exact
import Johnson.Desc.K1.Law.SaysTie
import Johnson.Desc.K1.Law.Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc.K1 (sampleRow Msg coefAt_sampleRow tableSize_eq)
open VerifiableInference.Desc.K2.Honest (zeroG)
open Johnson.Prover.Send (answers shapeAt)

variable {W₀ Rc Xi Tr : Type}

/-- **A sample row's value moves with its message.** x: the message, at the number o₁ of the one
statement and o₂ of the other. -/
theorem value_sample_moves (S₁ S₂ : Statement) (o₁ o₂ : Nat) (x : OnBytes.Oracle)
    (h₁ : S₁.oracles[o₁]? = some x) (h₂ : S₂.oracles[o₂]? = some x) (hc : S₁.codes = S₂.codes)
    (m : Msg) (z : List E) (β : E) (i : Nat) (y : E) (w₁ w₂ : Words Cb.Gl.E)
    (hw : w₁ o₁ = w₂ o₂) :
    value rdE S₁ (sampleRow m o₁ z β i y) w₁ = value rdE S₂ (sampleRow m o₂ z β i y) w₂ := by
  have one : ∀ (S : Statement) (o : Nat), S.oracles[o]? = some x → ∀ w : Words Cb.Gl.E,
      value rdE S (sampleRow m o z β i y) w =
        onTable rdE S (sampleRow m o z β i y) w o .main +
          onTable rdE S (sampleRow m o z β i y) w o .mask := by
    intro S o hx w
    have ho : o < S.oracles.size := by
      by_contra h
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hx
      cases hx
    unfold value
    rw [Finset.sum_eq_single o]
    · intro o' _ hne
      have hz0 : ∀ part, onTable rdE S (sampleRow m o z β i y) w o' part = 0 := fun part => by
        unfold onTable
        refine Finset.sum_eq_zero fun j _ => ?_
        have e := coefAt_sampleRow m o z β i y o' part j
        have hb : (o == o') = false := beq_eq_false_iff_ne.2 (Ne.symm hne)
        rw [hb] at e
        simp at e
        unfold coefAt at e
        rw [rdE_val, e, zero_mul]
      rw [hz0, hz0, add_zero]
    · intro h
      exact absurd (Finset.mem_range.2 ho) h
  have tb : ∀ part, onTable rdE S₁ (sampleRow m o₁ z β i y) w₁ o₁ part =
      onTable rdE S₂ (sampleRow m o₂ z β i y) w₂ o₂ part := fun part => by
    unfold onTable
    rw [tableSize_eq S₁ o₁ x h₁ part, tableSize_eq S₂ o₂ x h₂ part, hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e₁ := coefAt_sampleRow m o₁ z β i y o₁ part j
    have e₂ := coefAt_sampleRow m o₂ z β i y o₂ part j
    simp only [beq_self_eq_true, Bool.true_and] at e₁ e₂
    have e := e₁.trans e₂.symm
    unfold coefAt at e
    rw [rdE_val, rdE_val, e, hw]
  rw [one S₁ o₁ h₁ w₁, one S₂ o₂ h₂ w₂, tb, tb]

/-- The message number f + k of the statement that holds the place's messages from f on. -/
theorem stAt_at (P : VerifiableInference.Desc.K1.Par) (f k : Nat) (hk : k < P.sent.size) :
    (K1.stAt P f).oracles[f + k]? = some { shape := shapeAt P k } := by
  unfold K1.stAt stSent
  show ((Array.replicate f _) ++ P.sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[f +
    k]? = _
  rw [Array.getElem?_append_right (by simp), Array.size_replicate, Nat.add_sub_cancel_left]
  simp [shapeAt, hk]

/-- **THE SHIFT.** w, w': any words beneath. -/
theorem answers_moves (P : VerifiableInference.Desc.K1.Par) (f : Nat)
    (V : Nat → Johnson.Prover.Send.Rows) (seeds : List (List E × E)) (w w' : Words Cb.Gl.E) :
    answers P (K1.stAt P f) f (Johnson.Prover.Send.held w f P V) seeds =
      answers P (K1.stAt P 0) 0 (Johnson.Prover.Send.held w' 0 P V) seeds := by
  unfold answers
  refine List.flatMap_congr fun k hk => ?_
  have hk' : k < P.sent.size := List.mem_range.1 (List.mem_filter.1 hk).1
  refine List.map_congr_left fun i _ => ?_
  refine congrArg ofE (value_sample_moves _ _ _ _ _ (stAt_at P f k hk') (stAt_at P 0 k hk') rfl
    _ _ _ _ _ _ _ ?_)
  funext part j
  unfold Johnson.Prover.Send.held
  rw [if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk' _⟩,
    if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk' _⟩, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left]

/-- **The core's sender's answers, in the shared sending's terms, at any number f.** -/
theorem answers_are (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (data : Nat → Nat → Nat → Cb.Gl.E)
    (c : Cs (sendingDue codes sent fresh)) (drawn : List Fmt.Ext3) (f : Nat) :
    (coreSender freshTable).answers codes sent fresh data c drawn =
      (rowsAll freshTable codes sent fresh data c).map fun V =>
        (answers (sendingPar codes sent) (K1.stAt (sendingPar codes sent) f) f
          (Johnson.Prover.Send.held (fun _ _ _ => 0) f (sendingPar codes sent) V)
          (K1.seedsAt (sendingPar codes sent) [⟨drawn, [], [], none⟩])).map toE := by
  have e0 : K1.stAt (sendingPar codes sent) 0 =
      { codes := codes, oracles := sent.map fun n => { shape := n.shape } } := by
    unfold K1.stAt stSent
    rw [sendingPar_sent]
    simp only [Array.replicate_zero, Array.empty_append]
    rfl
  have hz : (zeroG : Cb.Gl.E) = 0 := readE_zero
  show (rowsAll freshTable codes sent fresh data c).map (fun V =>
    (answers (sendingPar codes sent)
      { codes := codes, oracles := sent.map fun n => { shape := n.shape } } 0
      (Johnson.Prover.Send.held (fun _ _ _ => zeroG) 0 (sendingPar codes sent) V)
      (VerifiableInference.Desc.K1.cutSeeds (sendingPar codes sent).coordinates
        (sendingPar codes sent).seeds (drawn.map OnBytes.E.ofTriple))).map toE) = _
  rw [← e0, hz]
  refine congrArg (fun g => (rowsAll freshTable codes sent fresh data c).map g)
    (funext fun V => ?_)
  rw [answers_moves (sendingPar codes sent) f V _ (fun _ _ _ => 0) (fun _ _ _ => 0)]
  rfl

/-- **WHAT THE SECOND MOVE SAYS, OF `switchRowsLaid`'s ROWS.** h: what was heard in front of the
part. x₁: the part's own first challenge. f: any number. -/
theorem says_two_of_rows (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) (x₁ : Fmt.Drawn) (s : Seen) (hs : p.sizes.serves = true)
    (hr : p.sizes.roomy = true) (f : Nat) :
    (moveTwo (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c s
        ⟨switchWit D readers closing p w, h ++ [x₁], ()⟩ =
      (switchRowsLaid D readers closing p c w h).map fun V =>
        ⟨((answers (sendingPar p.sizes.codes (switchSent p.sizes p.others))
            (K1.stAt (sendingPar p.sizes.codes (switchSent p.sizes p.others)) f) f
            (Johnson.Prover.Send.held (fun _ _ _ => 0) f
              (sendingPar p.sizes.codes (switchSent p.sizes p.others)) V)
            (K1.seedsAt (sendingPar p.sizes.codes (switchSent p.sizes p.others))
              [x₁])).map toE).map .answer, []⟩ := by
  have e := switchRowsAt_again p.sizes p.carries c.2.2
    ⟨switchWit D readers closing p w, h, ()⟩ ⟨switchWit D readers closing p w, h ++ [x₁], ()⟩ x₁
    rfl rfl
  have hl : ((⟨switchWit D readers closing p w, h ++ [x₁], ()⟩ :
      State SwitchAsk Unit).lately 1).flatMap (·.elems) = x₁.elems := by
    simp [State.lately]
  unfold moveTwo switchRowsLaid
  rw [hs, hr]
  show ((switchRowsAt p.sizes p.carries c.2.2
    ⟨switchWit D readers closing p w, h ++ [x₁], ()⟩ 1).bind _) = Except.map _ (Except.bind
      (switchRowsAt p.sizes p.carries c.2.2 ⟨switchWit D readers closing p w, h, ()⟩ 0) _)
  rw [e, hl]
  cases switchRowsAt p.sizes p.carries c.2.2 ⟨switchWit D readers closing p w, h, ()⟩ 0 with
  | error _ => rfl
  | ok M =>
    show Except.map _ ((coreSender freshTable).answers p.sizes.codes
      (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) M c.1 x₁.elems) =
      Except.map _ (rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) M c.1)
    rw [answers_are _ _ _ M c.1 x₁.elems f]
    cases rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) M c.1 <;> rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.value_sample_moves
#print axioms ProofFile.Honest.K2.Law.stAt_at
#print axioms ProofFile.Honest.K2.Law.answers_moves
#print axioms ProofFile.Honest.K2.Law.answers_are
#print axioms ProofFile.Honest.K2.Law.says_two_of_rows
