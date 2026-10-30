-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSeam.lean (each premise and conclusion of the form "∀ a …,
the promise at border 2 → …" stands besides under a letter E of the statement [a
lemma that takes the promise as a named premise, like `tidy_two`, does not]: what holds beside
the promise; at the ledger: the layer on the last chain's own state; the facts may
stand under a further condition Y on the statement, a letter: at the ledger it is the seated block's
yes with the game's own conclusion;
mem reads the outer state):
THE LEDGER's LAW `seam` OF THE LAST CHAIN's FIELD, CUT IN
TWO NAMED HALVES BY THE CORE OF THE SEAM (`core_at`, Johnson/Desc/Sound/SeamFacts.lean,
which stands at the kind's own record, at any frame, place and number of members): what the
proximity test's game concludes at W, the last chain's own test (`NTuple`: one tuple for all rows),
gives the table's own conclusion at the outer statement (`candN`: one tuple of candidates of mine,
of which ins holds however it is laid). A joining; general in the table's letters.
  `tidy_two`: inside the table's promise at border 2, at the book-keeping `fillAt …`, the
    record's statement is tidy (a clause of the book-keeping's test).
  `seam_of_core`: **the seam FROM: (facts) `CoreFacts` at what the seat's door returns, inside the
    promise: plain facts on the record and the strings: no chance, no count; (laid) THE ROWS' HALF:
    where all the rows that the test takes in hold, behind its beginning, of the words built of a
    tuple m, ins holds of every witness in which m is laid.**
Every "there is": candN's tuple: `core_at`'s m.
Limits. NOTHING OF THE TWO HALVES IS PAID HERE. `CoreFacts` is shown at no record; its clauses are
left to files of several kinds for the shared chain's two tests, in forms general in the seat. mem
and rdM are letters (which member an oracle message's number names; how a typed message is read
as words). Nothing on soundness.
-/
import Johnson.LLT25R.LastBehind
import Johnson.Desc.Sound.SeamFacts
import Johnson.Flat.Last.RowTwoCand

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open Cb Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Johnson.Pack
open OnBytes.Means H2K.ClaimSays H2K.Pin
open VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.K12.Seat (enterOwn)
open _root_.Desc.K14.Law.Fence (CoreFacts core_at)
open H2K.First (Plain)
open H2K.Pub (sgOf)
open _root_.Run

variable {P S₁ S₂ Cells Tok : Type} {Fr : Frame} (Nn : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (R : List Fmt.DeclaredRound)
  (hand : P × S₁ → Option Handed) (ended : S₂ → Option SharedOut)

/- what holds beside the promise at border 2: a letter -/
variable {E : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop}

/-- Inside the promise at border 2 the record's statement is tidy. -/
theorem tidy_two (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str)
    (h : onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a) : Means.Tidy a.1.2.st := by
  obtain ⟨f, o, -, -, hk⟩ := shapeAt_of_onL Nn Mg Pm Oc p R hand ended h
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  exact B.tidy

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (mine : List Mem) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (ins : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop)
  (mem : ((P × S₁ × S₂) × S₃) → ℕ → Option Mem)
  (rdM : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (Y : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop)

/-- **THE SEAM AT THE LAST CHAIN's OWN TEST, FROM THE CORE's FACTS AND THE ROWS' HALF.** -/
theorem seam_of_core
    (hrd : ∀ x m part i, rdM x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (facts : ∀ a t, onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t → Y a →
      CoreFacts cs G Fr π no rad smp (mem a.1) (· ∈ mine) t a.2 a.1 (strsOf Fr a.2))
    (laid : ∀ a t G0 m, onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      t.st.groups[t.g]? = some G0 →
      AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
        (_root_.Desc.K14.Law.wordsT cs (mem a.1) rdM m) →
      ∀ w w', LaidBy cs arr mine m w w' → ins a w') :
    ∀ a t st rest G0 Ly D', onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised cs G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      Fixes π t st rest G0 Ly D' → NTuple Fr π no rad rd (t, a.2) st rest G0 Ly D' → Y a →
      candN cs G arr smp Fr mine ins a := by
  intro a t st rest G0 Ly D' hon hE hP ht hf hN hY
  have hI : InOrder t.st := by
    obtain rfl : _ = t := Except.ok.inj ht
    exact (tidy_two Nn Mg Pm Oc p R hand ended a hon).inOrder
  obtain ⟨m, hall, hc⟩ := core_at cs G Fr π no rad rd smp (mem a.1) (· ∈ mine) rdM hrd t a.2 a.1
    (strsOf Fr a.2) (facts a t hon hE hP ht hY) hI ⟨st, rest, G0, Ly, D', hf, hN⟩ G0 hf.2.1
  exact ⟨m, fun x hx => hc x hx, laid a t G0 m hon hE hP ht hf.2.1 hall⟩

end LLT25

#print axioms LLT25.tidy_two
#print axioms LLT25.seam_of_core
