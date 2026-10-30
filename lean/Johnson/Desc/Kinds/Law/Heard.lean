-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Heard.lean: TWO SMALL LAWS ON THE SEAT OF THE HEARD NEXT TOKEN, for the
rows "reply_lays" and "reply_leaves". `Lays` and `Leaves` are the definitions `Block.Lays`
and `Block.Leaves` (Johnson/Desc/Sound/FoldHeard.lean), typed here once more to the letter, so that
this file needs none of that library: a term of the one is a term of the other.
GENERIC IN THE LENS: `k7_lays`: the next token's block lays, into whichever seat it is given, what
`replyOf` reads of the rounds that it was shown. `k6_leaves`: the output head's block leaves every
reading of the record that its three layings leave. `k6_runs_leave`: so does each of its runs of
claims, for a reading that `setKeyForms` leaves.
OVER Block.lean, State.lean and, in Johnson/Desc/Kinds/,
ReplyKind.lean · ReplyBlock.lean · HeadKind.lean · HeadFrame.lean:
the seat's setLedger and setHeard may refuse; the decision's last line is three.

-/
import Johnson.Desc.Kinds.HeadKind
import Johnson.Desc.Kinds.ReplyBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Desc.Reply (readReply isToken)

section
variable {S Cl α : Type}

/-- Where the block's decision goes on, the reading h of the record is as it was. -/
def Leaves (h : S → α) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → h s' = h s

/-- Where the block's decision goes on, the reading h of the record is rd of the rounds that the
decision was shown. -/
def Lays (h : S → α) (rd : List Fmt.RoundView → α) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → h s' = rd rs

end

/-- What the next token's block reads of its rounds: of just one round its one element. -/
def replyOf : List Fmt.RoundView → Option E
  | [r] => readReply r
  | _ => none

/-- What a return of the next token's decision is. -/
theorem k7_ok {S Cl : Type} {L : Reply.Seat S} {link piece V : Nat} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (Reply.kind (Cl := Cl) L link piece V).decide s rs gs = .ok s') :
    ∃ r0 x, rs = [r0] ∧ readReply r0 = some x ∧ isToken V x = true ∧ s' = L.setReply s x := by
  have h' : Reply.decideE V L s rs = .ok s' := h
  match rs, h' with
  | [], h' => simp [Reply.decideE] at h'
  | _ :: _ :: _, h' => simp [Reply.decideE] at h'
  | [r0], h' =>
    simp only [Reply.decideE] at h'
    split at h'
    · simp at h'
    · split at h'
      · simp at h'
      · rename_i x hx
        split at h'
        · rename_i ht
          simp only [Except.ok.injEq] at h'
          exact ⟨r0, x, rfl, hx, ht, h'.symm⟩
        · simp at h'

/-- (L1) at one record: the seat's law is asked at that record alone. -/
theorem k7_lays_at {S Cl : Type} (L : Reply.Seat S) (link piece V : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hL : ∀ x, L.reply (L.setReply s x) = some x)
    (h : (Reply.kind (Cl := Cl) L link piece V).decide s rs gs = .ok s') :
    L.reply s' = replyOf rs := by
  obtain ⟨r0, x, rfl, hx, _, rfl⟩ := k7_ok h
  rw [hL]
  exact hx.symm

/-- **(L1), generic in the lens**: for a seat that gives back what was laid, at every record. -/
theorem k7_lays {S Cl : Type} (L : Reply.Seat S) (hL : ∀ s x, L.reply (L.setReply s x) = some x)
    (link piece V : Nat) : Lays L.reply replyOf (Reply.kind (Cl := Cl) L link piece V) :=
  fun s rs gs s' h => k7_lays_at L link piece V s s' rs gs (hL s) h

/-- What a return of the head's decision is. -/
theorem decideBy_ok {S : Type} {rounds : Given → List Round} {hear : Given → Hear HeardAll}
    {weights : Given → Behind → SumOnMatrix} {p : Par} {L : Seat S} {s s' : S}
    {rs : List Fmt.RoundView} (h : decideBy rounds hear weights p L s rs = .ok s') :
    ∃ (F : OnBytes.Model.Fork) (H : HeardAll) (w : SumOnMatrix) (s1 s2 : S),
      L.setLedger s F = .ok s1 ∧ L.setHeard s1 H = .ok s2 ∧ s' = L.setWeightClaim s2 w := by
  unfold decideBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i s1 h1
            split at h
            · simp at h
            · rename_i s2 h2
              simp only [Except.ok.injEq] at h
              exact ⟨_, _, _, s1, s2, h1, h2, h.symm⟩

/-- **(L2), generic in the lens and in the reading.** -/
theorem k6_leaves {S Cl α : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (par : Par)
    (h : S → α) (h1 : ∀ s F s1, L.setLedger s F = .ok s1 → h s1 = h s)
    (h2 : ∀ s H s2, L.setHeard s H = .ok s2 → h s2 = h s)
    (h3 : ∀ s w, h (L.setWeightClaim s w) = h s) : Leaves h (kind cl L link piece par) := by
  intro s rs gs s' hd
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) par L s rs
      = .ok s' := hd
  obtain ⟨F, H, w, s1, s2, e1, e2, rfl⟩ := decideBy_ok hd'
  rw [h3, h2 _ _ _ e2, h1 _ _ _ e1]

/-- A block with the same decision leaves what the other leaves. (HeadCaller.lean's `kindWithJoin` is
`kind` with one more run: its decision is `kind`'s.) -/
theorem leaves_of_decide_eq {S Cl Cl' α : Type} {h : S → α} {b : Block S Cl} {b' : Block S Cl'}
    (he : b'.decide = b.decide) (hb : Leaves h b) : Leaves h b' := by
  intro s rs gs s' hd
  rw [he] at hd
  exact hb s rs gs s' hd

/-- Each of the head's named runs of claims leaves every reading that `setKeyForms` leaves. -/
theorem k6_runs_leave {S Cl α : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par)
    (h : S → α) (h4 : ∀ s k, h (L.setKeyForms s k) = h s) :
    ∀ c ∈ (kind cl L link piece p).claims, ∀ n s y, c.2 n s = .ok y → h y.2 = h s := by
  intro c hc n s y hy
  have hc' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl p L := hc
  unfold runsBy at hc'
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp hc'
  simp only [bind, Except.bind, pure, Except.pure] at hy
  split at hy
  · simp at hy
  · split at hy
    · simp at hy
    · simp only [Except.ok.injEq] at hy
      subst hy
      dsimp only
      split
      · exact h4 _ _
      · rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7_lays
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_leaves
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_runs_leave
