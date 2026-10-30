-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/SentKeeps.lean: the code switch: WHAT THE SENDING INSIDE A SWITCH
LEAVES AS IT WAS, AND WHICH NUMBERS IT RETURNS, at the sending that the kind K2 runs (sendByL8:
Send.sendOpen of Johnson/Desc/Sending/Send.lean over the plain ground).

BehindSame.lean says what the joins behind the sending leave as they were. Here the sending itself.
  SentOk S notices ids S'  the same codes and groups; the new messages' numbers are the next ones,
                       in the notices' order; every earlier message is as it was; message number
                       (old size + i) has notice i's shape; there are just notices.size messages
                       more
  loop_keeps           the loop that admits the sampled messages
  optBind, KeepsBelow, admit_keeps  tools: KeepsBelow n0: the second statement has the first's
                       codes, groups, number of messages and shapes, and its messages below n0;
                       admitting a message from n0 on keeps that
  sendP_keeps, sendOpen_keeps, sent_ok  SentOk of the plain ground's sendP, of Send.sendOpen, of the
                       sending that K2 runs (sendByL8)
KIN ON THE TREE, about the hand-written program's own sending and not about this text:
OnBytes/Slice/BlkSendRun.lean (receiveOracles_inv, verify_inv, sendVerify_inv).
By stSent_new, stSent_old, stSent_size, admitted_other, admitted_shape (OnBytes/Slice/). NOT HERE:
what the sending tests; the new messages' sample rows (SentRows.lean, SentTargets.lean) and pads;
the book. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.BehindSame
import Johnson.Top.H0.Tw.K2.SendL8
import OnBytes.Slice.BlkProxKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.Ground (recvP admitP)

theorem optBind {α β : Type} {x : Option α} {f : α → Option β} {b : β} (h : (x >>= f) = some b) :
    ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- Two statements of which the second has the first's codes, groups, number of messages and shapes,
and its messages below n0. -/
structure KeepsBelow (n0 : Nat) (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  groups : S'.groups = S.groups
  size : S'.oracles.size = S.oracles.size
  old : ∀ o : Nat, o < n0 → S'.oracles[o]? = S.oracles[o]?
  shape : ∀ i : Nat, (S'.oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape)

theorem KeepsBelow.refl (n0 : Nat) (S : Statement) : KeepsBelow n0 S S :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem KeepsBelow.trans {n0 : Nat} {A B C : Statement} (h : KeepsBelow n0 A B) (k : KeepsBelow n0 B
    C) :
    KeepsBelow n0 A C :=
  ⟨k.codes.trans h.codes, k.groups.trans h.groups, k.size.trans h.size,
    fun o ho => (k.old o ho).trans (h.old o ho), fun i => (k.shape i).trans (h.shape i)⟩

theorem admit_keeps {L : Type} {n0 o : Nat} {d d' : DState L} {rows : Array OnBytes.Row}
    (ho : n0 ≤ o) (h : admitP d o rows = some d') : KeepsBelow n0 d.st d'.st := by
  unfold admitP at h
  split at h
  · obtain ⟨x, -, h⟩ := optBind h
    obtain ⟨places, -, h⟩ := optBind h
    cases h
    exact ⟨rfl, rfl, by simp [OnBytes.Slice.admitted],
      fun o' ho' => OnBytes.Slice.admitted_other _ _ _ _ _ o' (by omega),
      OnBytes.Slice.admitted_shape _ _ _ _ _⟩
  · cases h

theorem loop_keeps {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) (n0 : Nat) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      (∀ x ∈ l, n0 ≤ x.1) → sampleLoop groundG p codes seeds l ys d = some (d', left) →
      KeepsBelow n0 d.st d'.st
  | [], ys, d, d', left, _, h => by
    cases h
    exact KeepsBelow.refl _ _
  | (o, s) :: l, ys, d, d', left, hl, h => by
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d1 h1
        exact (admit_keeps (hl (o, s) (List.mem_cons_self ..)) h1).trans
          (loop_keeps p codes seeds n0 l ys' d1 d' left
            (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h)

/-- What a sending leaves as it was, and which numbers it returns. -/
structure SentOk (S : Statement) (notices : Array OracleNotice) (ids : Array Nat) (S' : Statement) :
    Prop where
  codes : S'.codes = S.codes
  groups : S'.groups = S.groups
  ids : ids = (Array.range notices.size).map (· + S.oracles.size)
  size : S'.oracles.size = S.oracles.size + notices.size
  old : ∀ o : Nat, o < S.oracles.size → S'.oracles[o]? = S.oracles[o]?
  shape : ∀ i : Nat, (S'.oracles[S.oracles.size + i]?).map (·.shape) = (notices[i]?).map (·.shape)

theorem sendP_keeps {L : Type} {p : GPar} {own : Bool} {d : DState L} {sent : Array OracleNotice}
    {r₁ r₂ : Fmt.RoundView} {x : Array Nat × List E × List E × Nat × DState L}
    (h : sendP groundG p own d sent r₁ r₂ = some x) : SentOk d.st sent x.1 x.2.2.2.2.st := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := optBind h
  dsimp only at h
  obtain ⟨shapes, -, h⟩ := optBind h
  obtain ⟨seeds, -, h⟩ := optBind h
  obtain ⟨an, -, h⟩ := optBind h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBind h
    dsimp only at h
    split at h
    · cases h
      have hr : recvP p.firstTree d sent = some (ids, d₁) := h1
      unfold recvP at hr
      split at hr
      · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 hr
        cases e
        have hk := loop_keeps p _ seeds d.st.oracles.size _ an _ d₂ left (fun y hy => by
          have h3 := (List.of_mem_zip hy).1
          have h4 := (List.mem_filter.1 h3).1
          simp only [Array.toList_map, List.mem_map] at h4
          obtain ⟨a, -, e⟩ := h4
          omega) h2
        exact ⟨hk.codes, hk.groups, rfl,
          hk.size.trans (OnBytes.Slice.ProxRun.stSent_size _ _),
          fun o ho => (hk.old o ho).trans (OnBytes.Slice.stSent_old _ _ o ho),
          fun i => by
            rw [hk.shape, OnBytes.Slice.stSent_new, Option.map_map]
            rfl⟩
      · cases hr
    · cases h
  · cases h

theorem sendOpen_keeps {L : Type} {p : GPar} {owed : Option Nat} {sent : Array OracleNotice}
    {e₁ : Fmt.Entry} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array Nat} {took : Nat}
    (h : VerifiableInference.Desc.First.Send.sendOpen groundG p owed sent e₁ d r₁ r₂ =
      some (ids, took, d')) : SentOk d.st sent ids d'.st := by
  unfold VerifiableInference.Desc.First.Send.sendOpen at h
  split at h
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact sendP_keeps hx
  · cases h

/-- **The sending that K2 runs.** -/
theorem sent_ok {P : _root_.Tw.K2.Par9} {S : Statement} {B : TreeBook} {roots : Nat} {settled :
    Bool}
    {notices : Array OracleNotice} {rS rL : Fmt.RoundView} {y : _root_.Tw.K2.Sent}
    (h : _root_.Tw.K2.sendByL8 P S B roots settled notices rS rL = .ok y) :
    SentOk S notices y.ids y.st := by
  unfold _root_.Tw.K2.sendByL8 at h
  split at h
  · rename_i ids took d hd
    cases h
    exact sendOpen_keeps hd
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sendP_keeps
#print axioms VerifiableInference.Desc.First.K2.sent_ok
