-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyShape.lean: the table of joints of the key file: the book-keeping at the first chain's borders: a Bool on the state for each border (onAt's «shape»): where the chain stands: what is sent, which group is
open, whether a lookup's ledger is open and how far it is filled, how many lookups have laid their rows, whether the ranges' test has begun, whether the one claim and the row (Eval) lie. Over named readers alone (KReaders, and
KBook for the lookup's ledger). With code: an honest run evaluates it at every border. No Mathlib.
K3's files' rider: the ledger in front of K3 is a promise of the joint: open, its three arrays of its size, its count at the place's first slot, the lookup's slots inside its room and
free, nothing heard yet: lookupKind tests next and ns alone: here: border 2 + 6 l + 2.
Behind K3's hearing (border 2 + 6 l + 3) all slots are taken but not all are filled: the leaves' sumcheck is left open: the run «planes», which the layer calls, closes it and fills its slots: by a run (asked there, «filled» gets a no from the honest
file at both lookups): «filled» is asked behind the layer alone.
KBook has «handed»: what the last chain's first boundary's book-keeping wants of this chain's last statement beyond what that chain's start tests itself (Johnson/RunOne/KeyHanded.lean): one text for both sides of the two seams: asked behind
V's sending (borders 2 + 6 n + 4 | + 5). shape₁_handed: proved: the book-keeping's yes there gives it.
The ties between the plan, which the claims read, and the state's own copies, which the blocks read, are one reader, border by border: KBook.ties : Nat → S → Bool. The rule: for each block: what its decide reads against what the
claim in front reads; where the two name different fields a tie stands in the promise. So a tie more changes the filling alone, not this file. shape₁ := ties and core₁. The filling (Johnson/RunOne/KeyReaders1.lean: ties₁) asks,
among others, that the state's statement's codes are the plan's, at every border, and that the number under which the state holds the index-mask message (the caller lays the homes there; K13 reads the index masks there) is the
plan's number of the witness's message 0, from border 1 on. At the default (no) the book-keeping says no.
-/
import Johnson.Desc.Key.KeyMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

/-- A lookup's ledger, as far as the book-keeping reads it. -/
structure LedgerView where
  next : Nat
  ns : Nat
  /-- its three arrays have its size -/
  sized : Bool
  /-- the slots from next on are free -/
  free : Bool
  /-- the slots below next are filled -/
  filled : Bool

/-- **What more must be readable of the first chain's state.** -/
structure KBook (S : Type) where
  ledger : S → Option LedgerView
  heard : S → Bool
  homes : S → Nat
  /-- the number of the request's own group (V's, with the claim's masks' messages), once it is made -/
  own : S → Option Nat := fun _ => none
  /-- The Bool on the chain's last statement (Johnson/RunOne/KeyHanded.lean). (The two last fields have defaults, «nothing» and «no»: AT THE DEFAULTS THE BOOK-KEEPING SAYS NO BEHIND V's SENDING.) -/
  handed : S → Bool := fun _ => false
  /-- the ties between the plan and the state's own copies, at a border -/
  ties : Nat → S → Bool := fun _ _ => false

section
variable {S : Type} (K : KPlan) (X : KReaders S) (B : KBook S)

/-- Message k of the witness is in the statement, sampled, with a sample row. -/
def sentB (s : S) (k : Nat) : Bool :=
  match (K.orc k).bind fun o => (X.st s).oracles[o]? with
  | some x => x.sampled && x.sampleRows.size != 0
  | none => false

/-- Just the first d lookups have laid their rows and their claims on the keys; each has a claim a part. -/
def doneB (n d : Nat) (s : S) : Bool :=
  (List.range n).all fun l =>
    if l < d then
      (X.rowsAt s l).any (!·.isEmpty) && (match X.keysAt s l, K.lookups[l]? with | some ks, some L => ks.length == L.parts.length | _, _ => false)
    else (X.rowsAt s l).isNone && (X.keysAt s l).isNone

/-- B's group: there; its test has begun or not; its number of open rows. -/
def groupB (s : S) (inRun : Bool) (rows : Nat) : Bool :=
  match (X.grpB s).bind fun g => (X.st s).groups[g]? with
  | some G => G.inRun == inRun && G.rows.size == rows
  | none => false

/-- BEHIND V's SENDING (what the last chain's start leans on): V is the last message but one of the statement; the last is its fresh mask: unsampled, not yet spent; THE OWN GROUP IS THE LAST GROUP, ITS MEMBERS JUST I AND V, ONE OPEN ROW, ITS TEST NOT
BEGUN. -/
def ownB (s : S) : Bool :=
  let St := X.st s
  match K.orc 0, K.orc 2, B.own s with
  | some i, some v, some g =>
    St.oracles.size == v + 2 && ((St.oracles[v + 1]?).any fun x => !x.sampled && !x.spentAsMask) && g + 1 == St.groups.size &&
      ((St.groups[g]?).any fun G => G.members.toList == [i, v] && G.rows.size == 1 && !G.inRun)
  | _, _, _ => false

/-- All lookups' rows, counted. -/
def rowsCount (n : Nat) (s : S) : Nat := ((List.range n).map fun l => ((X.rowsAt s l).map (·.length)).getD 0).sum

/-- The book-keeping at border b of the first chain, but for the two ties to the plan. n: the number of lookups. slots l: the number of hidden values of lookup l (the face's). -/
def core₁ (n : Nat) (slots : Nat → Nat) (b : Nat) (s : S) : Bool :=
  if b == 0 then (X.st s).oracles.size == 0 && (X.st s).groups.size == 0
  else if b == 1 then sentB K X s 0 && !sentB K X s 1 && (X.st s).groups.size == 0
  else if b < 2 + 6 * n then
    let l := (b - 2) / 6
    let j := (b - 2) % 6
    sentB K X s 0 && sentB K X s 1 && !sentB K X s 2 && groupB X s false 0 && doneB K X n (if j ≥ 4 then l + 1 else l) s && (X.pile s).isNone &&
      (if j ≤ 1 then (B.ledger s).isNone && !B.heard s
       else if j == 2 then !B.heard s && B.homes s == slots l && (B.ledger s).any fun L => L.next == 0 && L.ns == slots l && L.sized && L.free
       else if j == 3 then B.heard s && B.homes s == slots l && (B.ledger s).any fun L => L.next == slots l && L.ns == slots l && L.sized
       else B.heard s && B.homes s == slots l && (B.ledger s).any fun L => L.next == slots l && L.ns == slots l && L.sized && L.filled)
  else
    let c := b - (2 + 6 * n)
    sentB K X s 0 && sentB K X s 1 && (B.ledger s).isNone && !B.heard s && doneB K X n n s &&
      (if c == 0 then groupB X s false 0 && (X.pile s).isNone && !sentB K X s 2
       else if c == 1 then groupB X s false (rowsCount X n s) && rowsCount X n s != 0 && (X.pile s).isNone && !sentB K X s 2
       else if c == 2 then groupB X s true 0 && (X.pile s).isNone && !sentB K X s 2
       else if c == 3 then groupB X s true 0 && (X.pile s).isSome && (X.eval s).isNone && !sentB K X s 2
       else groupB X s true 0 && (X.pile s).isSome && (X.eval s).isSome && (X.g s).isSome && sentB K X s 2 && ownB K X B s && B.handed s)

/-- **The book-keeping at border b of the first chain.** -/
def shape₁ (n : Nat) (slots : Nat → Nat) (b : Nat) (s : S) : Bool :=
  B.ties b s && core₁ K X B n slots b s

theorem shape₁_iff (n : Nat) (slots : Nat → Nat) (b : Nat) (s : S) :
    shape₁ K X B n slots b s = true ↔ (B.ties b s = true ∧ core₁ K X B n slots b s = true) := by
  unfold shape₁
  rw [Bool.and_eq_true_iff]

/-- **The step of the book-keeping across a block**, from the step of the ties and the step of core₁. -/
theorem shape₁_step (n : Nat) (slots : Nat → Nat) (b b' : Nat) (s s' : S) (ht : B.ties b s = true → B.ties b' s' = true)
    (hcore : core₁ K X B n slots b s = true → core₁ K X B n slots b' s' = true) (h : shape₁ K X B n slots b s = true) : shape₁ K X B n slots b' s' = true := by
  obtain ⟨h1, h3⟩ := (shape₁_iff K X B n slots b s).1 h
  exact (shape₁_iff K X B n slots b' s').2 ⟨ht h1, hcore h3⟩

/-- Behind V's sending core₁'s yes gives the Bool «handed». -/
theorem core₁_handed (n : Nat) (slots : Nat → Nat) (c : Nat) (s : S) (hc : 4 ≤ c) (h : core₁ K X B n slots (2 + 6 * n + c) s = true) : B.handed s = true := by
  have hb0 : (2 + 6 * n + c == 0) = false := by simp <;> omega
  have hb1 : (2 + 6 * n + c == 1) = false := by simp <;> omega
  have hlt : ¬ (2 + 6 * n + c < 2 + 6 * n) := by omega
  have e : 2 + 6 * n + c - (2 + 6 * n) = c := by omega
  have hc0 : (c == 0) = false := by simp <;> omega
  have hc1 : (c == 1) = false := by simp <;> omega
  have hc2 : (c == 2) = false := by simp <;> omega
  have hc3 : (c == 3) = false := by simp <;> omega
  simp only [core₁, hb0, hb1, hlt, e, hc0, hc1, hc2, hc3, Bool.false_eq_true, if_false, ↓reduceIte, Bool.and_eq_true] at h
  exact h.2.2

/-- **Behind V's sending the book-keeping's yes gives the Bool «handed».** -/
theorem shape₁_handed (n : Nat) (slots : Nat → Nat) (c : Nat) (s : S) (hc : 4 ≤ c) (h : shape₁ K X B n slots (2 + 6 * n + c) s = true) : B.handed s = true :=
  core₁_handed K X B n slots c s hc ((shape₁_iff K X B n slots _ s).1 h).2

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.shape₁_handed
