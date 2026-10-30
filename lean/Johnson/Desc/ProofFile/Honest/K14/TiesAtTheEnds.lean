-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/TiesAtTheEnds.lean: kind K14: how the two earlier chains' honest
threads (firstThread, sharedThread, Honest/Thread/TheFirstThread.lean) are tied to the list of
challenges that the second chain's witness is handed, as far as Omega's sample rows in front of the
second chain's proximity test need it. Statements with their proofs; no definition.

A stand of a thread at a border: its invariant Thr (Honest/Thread/Thr.lean), with its companion Said
(ThrS, Honest/Thread/Said.lean), holds there, at some state of the verifier, some state of the
prover's run and some available tables.

omega_samples_at_end (Honest/K14/OmegaSamplesAtEnd.lean) takes a premise hd: the first challenge
that the shared chain's run has heard is the first behind the first chain's in the list that the
second chain's witness is handed. Here hd is shown from ONE EQUATION ON LISTS: that list begins with
what the first chain's run has heard, followed by what the shared chain's run has heard. That is how
the frame lays the second chain's start (Ready.start₃, Honest/Frame.lean), and it is what the
library's term for the two earlier chains' last states (endsBy, Honest/Thread/OneState.lean) is
chosen by.

  endsBy_stands       where two stands of the two earlier threads make up the list, endsBy returns a
                      pair of states at which such stands are: with the inputs and the equation on
                      the lists. General in the threads
  firstRv_split       the first challenge of a list b that is not empty is the first behind a in
                      a ++ b ++ c
  rounds_pos          a list of sub-protocols whose second member (number 1, counted from 0)
                      declares a round has declared a round in front of every border from 2 on
  shared_heard_ne     **at the full size, where the shared chain's thread stands at its last border,
                      its run has heard a challenge**
  hd_of_split         **the premise hd from the equation on the lists**, the first thread at its
                      last border and the shared thread at its last border
  omega_samples_split **omega_samples_at_end with the equation in hd's place**

Limits.
  * h : HeadAtReturn is a hypothesis (Honest/K14/WordsAtLastWitness.lean says what it holds).
  * That the threads stand at any run, that the inputs are tied (hin) and the equation on the lists
    (hs) are premises. endsBy_stands gives the last two at endsBy's value WHERE SUCH STANDS EXIST:
    that they exist is its premise hE.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesAtEnd
import Johnson.Desc.ProofFile.Honest.Thread.OneState
import Johnson.Desc.K14.Law.RoundsMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Slice (rdE frS)
open OnBytes.Means (SampleSays)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Sound (wordsShared)
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifierAndGoals.AtTheName (dpZ)
open Desc.K14 (St p14Of beforePointOf)
open ProofFile.Honest.FirstThread

section ends
variable {Bk : ProverCoinCounts} {S₁ Cl₁ V₁ W₁ X₁ Pb₁ S₂ Cl₂ V₂ W₂ X₂ Pb₂ W₃ : Type}
  (T₁ : Thread Bk S₁ Cl₁ V₁ W₁ X₁ Pb₁) (Said₁ : Nat → Coins Bk → Mid W₁ X₁ → Prop) (n₁ : Nat)
  (T₂ : Thread Bk S₂ Cl₂ V₂ W₂ X₂ Pb₂) (Said₂ : Nat → Coins Bk → Mid W₂ X₂ → Prop) (n₂ : Nat)
  (in₁ : W₃ → W₁) (in₂ : W₃ → W₂)

/-- **Where two stands of the two earlier threads make up the list of challenges, the library's term
for their last states returns a pair at which such stands are.** -/
theorem endsBy_stands [Inhabited S₁] [Inhabited S₂] (k : Coins Bk) (w : W₃)
    (hl : List Fmt.Drawn)
    (hE : ∃ p : S₁ × S₂, ∃ m₁ E₁ m₂ E₂, ThrS T₁ Said₁ n₁ k p.1 m₁ E₁ ∧
      ThrS T₂ Said₂ n₂ k p.2 m₂ E₂ ∧ m₁.st.input = in₁ w ∧ m₂.st.input = in₂ w ∧
      m₁.st.heard ++ m₂.st.heard = hl) :
    ∃ m₁ E₁ m₂ E₂, ThrS T₁ Said₁ n₁ k (endsBy T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ k w hl).1 m₁ E₁ ∧
      ThrS T₂ Said₂ n₂ k (endsBy T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ k w hl).2 m₂ E₂ ∧
      m₁.st.input = in₁ w ∧ m₂.st.input = in₂ w ∧ m₁.st.heard ++ m₂.st.heard = hl := by
  unfold endsBy
  rw [dif_pos hE]
  exact hE.choose_spec

end ends

/-- The first challenge of a list b that is not empty is the first behind a in a ++ b ++ c. -/
theorem firstRv_split (a b c : List Fmt.Drawn) (hb : b ≠ []) :
    firstRv b = firstRv ((a ++ b ++ c).drop a.length) := by
  rw [List.append_assoc, List.drop_left]
  cases b with
  | nil => exact absurd rfl hb
  | cons x t => rfl

/-- A list of sub-protocols whose second member (number 1, counted from 0) declares a round has
declared a round in front of every border from 2 on. -/
theorem rounds_pos {S Cl : Type} {bs : List (Block S Cl)} {x : Block S Cl}
    (hx : bs[1]? = some x) (h1 : x.rounds ≠ []) (b : Nat) : 0 < roundsTo bs (b + 2) := by
  match bs, hx with
  | a :: y :: tl, hx =>
    obtain rfl : y = x := Option.some.inj hx
    unfold roundsTo declsTo
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
    have := List.length_pos_of_ne_nil h1
    omega

section letters
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X P₁ Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **At the full size, where the shared chain's thread stands at its last border, its run has heard
a challenge**, whatever the thread's letters are. -/
theorem shared_heard_ne (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E) :
    m.st.heard ≠ [] := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  rw [shared_has_twelve h] at hA
  have hlen := Thread.heard_length _ hA.2.1
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, l1, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  have h1 : x1.rounds ≠ [] := by
    rw [l1.rounds]
    intro c
    have q := (Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ B.made).1
    rw [c] at q
    cases q
  have hp : 0 < roundsTo (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order
      wit table fixed n₁ n₂ Vd Rd Kp w).thread.bs 12 :=
    rounds_pos (x := x1) (by rw [e]; rfl) h1 10
  intro c
  rw [c, List.length_nil] at hlen
  omega

end letters

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The premise hd of omega_samples_at_end from one equation on lists**: the list begins with what
the first chain's run has heard, then what the shared chain's run has heard. -/
theorem hd_of_split (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (w₂ : Common W₀ Rc OnBytes.TableKey) {k : Coins A.B} {e₁ : P5J.TS}
    {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : Thr (firstThread h first w₁) h.description.first.blocksInOrder.length k e₁ m₁ E₁) {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (sharedThread h reads sh w₂) h.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (heard rest : List Fmt.Drawn) (hs : heard = m₁.st.heard ++ m₂.st.heard ++ rest) :
    firstRv m₂.st.heard = firstRv (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) := by
  have e₁' : m₁.st.heard.length =
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length :=
    drawsFit_length _ _ u₁.2.1
  rw [hs, ← e₁']
  exact firstRv_split _ _ _ (shared_heard_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.head u₂)

/-- **omega_samples_at_end with the equation on the lists in hd's place.** -/
theorem omega_samples_split (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (w₂ : Common W₀ Rc OnBytes.TableKey) {k : Coins A.B} {e₁ : P5J.TS}
    {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : Thr (firstThread h first w₁) h.description.first.blocksInOrder.length k e₁ m₁ E₁) {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (sharedThread h reads sh w₂) h.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard rest : List Fmt.Drawn)
    (hin : m₂.st.input = ⟨w.w₀, w.rc, A.H.key w.x⟩)
    (hs : heard = m₁.st.heard ++ m₂.st.heard ++ rest) :
    ∀ e, Desc.K14.ended e₂ = some e →
      SampleSays rdE (sharedOfEnd e).st (sharedOfEnd e).omega
        (wordsShared (P5J.At.arr A.Z) ((dpZ files).at frS.P.T.a).t₁ (sharedOfEnd e).st
          (sharedOfEnd e).book (lastWitness h first reads k w heard)) :=
  omega_samples_at_end h first reads sh w₂ u₂ w heard hin
    (hd_of_split h first reads sh w₁ w₂ u₁ u₂ heard rest hs)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.endsBy_stands
#print axioms ProofFile.Honest.K14.firstRv_split
#print axioms ProofFile.Honest.K14.rounds_pos
#print axioms ProofFile.Honest.K14.shared_heard_ne
#print axioms ProofFile.Honest.K14.hd_of_split
#print axioms ProofFile.Honest.K14.omega_samples_split
