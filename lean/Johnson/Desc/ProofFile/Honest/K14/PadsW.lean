-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/PadsW.lean: the linear claim's second part ("K14, second part",
the first member of a proof file's last chain): WHERE THE PAD OF THE MESSAGE W LIES. The member's
last test, "no coefficient on a pad", needs that each place of W's pad in its main table lies inside
the table, at an entry numbered at least 2 ^ kCol (PadsBehind, Honest/K14/DotPads.lean). This file
shows it from what the verifier's own sub-protocol that receives W writes into the statement.

  PadOwn              the message number o, where it is there with a shape that has answers, bears
                      the pad's places that a sending lays for its own shape (Send.pad)
  padOwn_of_same      it passes to a statement with the same codes and, of each message, the same
                      shape, mark, sample rows and pad (SameAll, Johnson/Desc/K13/Law/PinDec.lean)
  decideSend_pad      behind a yes of a sending's decision the first message sent has it
  sendAtS_pad         the same at the first chain's state: the numbers that the state notes are the
                      sending's, and the first of them has it
  atM4_pad            **behind a yes of the joined sub-protocol "W's commitment, the own group and
                      (Eval)"**: the state names W's number, and the message there has it
  padsBehind_of_own   **PadOwn at W's number gives PadsBehind there**, where the message has the
                      plan's shape of W, is a member of some group, and the plan's test on the
                      linear part's shape passes at the statement's codes

A LIMIT. PadsBehind speaks of the pad's places in the MAIN table alone, and a sending lays every
place of a pad in the mask table as soon as the shape has a mask row (Send.pad,
OnBytes/Iop/Send.lean). At such a shape PadsBehind runs over nothing: it is true because the pad
lies in the mask table, and PadOwn is what shows that. At the full size W's shape has a mask row
(k13_wRow_at_head, AtFullSide/K13/WFillAtHead.lean). padsBehind_of_own says something of a place
where the shape has no mask row.

What is not claimed. That any sub-protocol says yes. That the message is there: PadOwn is an
implication. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.DotPads
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.K1.Law.Joined2
import Johnson.Desc.K1.Law.Sound
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K13.Law.PinDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open Desc.Plain (DState)
open VerifiableInference.Desc.K1 (Par sendAtS decideSend decideSend_iff behind outs wr shapesOf
  outs_spec kept_behind seedsOf answersIn)
open VerifiableInference.Desc.K13 (Where atM4 rowsB atS)
open VerifiableInference.Desc.K13.Law (ebind_ok rowsB_at rows_ok rows_same SameAll sampleOf linAt)

/-- The message number o, where it is there with a shape that has answers, bears the pad's places
that a sending lays for that shape at the statement's codes. -/
def PadOwn (T : Statement) (o : Nat) : Prop :=
  ∀ x, T.oracles[o]? = some x → x.shape.answers ≠ 0 →
    x.pad = ((Send.pad T.codes x.shape).getD []).map fun p => (p.part, p.index)

/-- It passes to a statement with the same codes and the same shapes and pads. -/
theorem padOwn_of_same {A B : Statement} (h : SameAll A B) {o : Nat} (hA : PadOwn A o) :
    PadOwn B o := by
  intro x hx ha
  have e := h.2 o
  unfold sampleOf at e
  rw [hx] at e
  have e2 : (A.oracles[o]?).map (fun y => (y.shape, y.sampled, y.sampleRows, y.pad)) =
      some (x.shape, x.sampled, x.sampleRows, x.pad) := e.symm
  obtain ⟨y, hy, e'⟩ := Option.map_eq_some_iff.1 e2
  have e1 : y.shape = x.shape := congrArg (·.1) e'
  have e4 : y.pad = x.pad := congrArg (·.2.2.2) e'
  rw [← e4, ← e1, h.1]
  exact hA y hy (by rw [e1]; exact ha)

/-- **Behind a yes of a sending's decision the first message sent has it.** -/
theorem decideSend_pad {L : Type} (P : Par) (owed : Option Nat) (d : DState L) (rs : List Fmt.RoundView)
    (x : Array Nat × DState L) (h : decideSend P owed d rs = .ok x) (w : Nat)
    (hw : x.1[0]? = some w) : PadOwn x.2.st w := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨⟨_, hc, _, _, hf⟩, hids, hd⟩ := (decideSend_iff P owed d x.2 r₁ r₂ x.1).1 h
    rw [hids, Array.getElem?_map] at hw
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨hlt, hi0⟩ := Array.getElem?_eq_some_iff.1 hi
    rw [Array.size_range] at hlt
    rw [Array.getElem_range] at hi0
    subst hi0
    have hk : 0 < (shapesOf P).length := by
      unfold shapesOf
      simpa using hlt
    obtain ⟨ys', _, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
      d.st.oracles.size (answersIn r₂) hf 0 hk
    intro y hy ha
    rw [hd] at hy ⊢
    have hy' : (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)).toArray[0 + d.st.oracles.size]? = some y := hy
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)] at hy'
    have hy2 : (outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[0]? =
        some y := by simpa using hy'
    obtain rfl : wr P.codes (seedsOf P r₁) (d.st.oracles.size + 0) (shapesOf P)[0] ys' = y :=
      Option.some.inj (hget.symm.trans hy2)
    have hcod : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes :=
      (kept_behind P d _ _).1.trans hc
    have hsh : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + 0) (shapesOf P)[0] ys').shape =
        (shapesOf P)[0] := by
      unfold wr
      split <;> rfl
    rw [hcod, hsh]
    rw [hsh] at ha
    simp [wr, ha]

variable {Cl : Type}

/-- The same at the first chain's state. -/
theorem sendAtS_pad (P : Par) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') :
    ∃ (a : VerifiableInference.Desc.First.MemOwn) (ids : Array Nat),
      s'.here = .mem { a with ids := ids } ∧ ∀ w, ids[0]? = some w → PadOwn s'.st w := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · rename_i a ha
    split at h
    · obtain ⟨y, hy, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 hy
      exact ⟨a, x.1, rfl, fun w hw => decideSend_pad P _ _ rs x hx w hw⟩
    · cases h
  · cases h

/-- **Behind a yes of "W's commitment, the own group and (Eval)"** the state names W's number, and
the message there, where it is there with a shape that has answers, bears its own shape's pad. -/
theorem atM4_pad {P : Where} {P' : Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (sendAtS P')).decide s rs gs = .ok s') :
    ∃ l, linAt s' = some l ∧ PadOwn s'.st l.w := by
  have h' : ((sendAtS P' : Block S Cl).decide s (rs.take (sendAtS P' : Block S Cl).rounds.length)
      (gs.take (sendAtS P' : Block S Cl).openings)).bind (fun m =>
        (rowsB (Cl := Cl) atS P).decide m (rs.drop (sendAtS P' : Block S Cl).rounds.length)
          (gs.drop (sendAtS P' : Block S Cl).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h'
  obtain ⟨a, ids, hh, hp⟩ := sendAtS_pad P' s s₁ _ _ h1
  obtain ⟨m₀, l, o, owed, hs, hl, hrows, rfl⟩ := rowsB_at h2
  rw [hh] at hs
  injection hs with hs
  subst hs
  obtain ⟨_, _, _, _, hw, _⟩ := rows_ok hrows
  exact ⟨o.1, rfl, padOwn_of_same (rows_same hrows) (hp _ hw)⟩

/-- **PadOwn at W's number gives PadsBehind there.** hx, hs: the message is there with the plan's
shape of W. hm: it is a member of a group G. hlin: the plan's test on the linear part's shape passes
at the statement's codes. -/
theorem padsBehind_of_own (T : Statement) (Sh : LinShape) (w : Nat) (x : Oracle) (G : Group)
    (hx : T.oracles[w]? = some x) (hs : x.shape = Sh.w) (hm : G.members.contains w = true)
    (hlin : linOk T.codes Sh = true) (hp : PadOwn T w) :
    PadsBehind T w (linLayW T.codes Sh) (2 ^ Sh.kCol) := by
  have hf : VerifiableInference.Desc.Own.linFits T.codes Sh = true := by
    rw [VerifiableInference.Desc.Own.linFits_eq]
    exact hlin
  obtain ⟨hsh, _, _, _, _, _, _, hroom⟩ :=
    (VerifiableInference.Desc.Own.linFits_iff T.codes Sh).1 hf
  have hv := hsh.2.2.2.2.2.2.2.1
  have ha : Sh.w.answers ≠ 0 := by
    have := hv.2.2.2
    omega
  exact (Desc.K14.Honest.sits_of_msg T G w x Sh.w Sh.wRowsHigh (2 ^ Sh.kCol) hx hs
    (by rw [← hs]; exact hp x hx (by rw [hs]; exact ha)) hm (Nat.pos_of_ne_zero hv.2.1) hv.2.2.1 ha
    (Nat.pow_pos (by decide)) hroom).pad

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.padOwn_of_same
#print axioms ProofFile.Honest.K14.decideSend_pad
#print axioms ProofFile.Honest.K14.sendAtS_pad
#print axioms ProofFile.Honest.K14.atM4_pad
#print axioms ProofFile.Honest.K14.padsBehind_of_own
