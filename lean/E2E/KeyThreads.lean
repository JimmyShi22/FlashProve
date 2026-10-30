--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyThreads.lean: THE KEY FILE's TESTS WITHOUT A PART OF A PROVER, IN THE FORMS THAT THE FILE's
RULE FOR ACCEPTANCE TAKES (Johnson/Desc/ProofFile/Honest/Thread/FileYes.lean, `file_accepts`). That
rule goes from premises at every sub-protocol of a file's three chains, and at the seams between the
chains, to "the IOP as written in Lean (below: the description) accepts the views of the run". Its
premises speak of three THREADS: for each chain a family of sentences, one at each border between
two sub-protocols. Here: adapters, general in the threads. Statements and proofs. NOTHING IS SHOWN
OF ANY PROVER: no completeness; every adapter has a premise on the threads that is shown of no
thread.

What is shown.
  **`accepted_quiet`**: GENERAL: a sub-protocol without a round is accepted (the rule's `Accepted`)
    where, at every state at which the thread stands in front of it, its decision accepts at no
    round and no column.
  **`accepted_sealed`**: GENERAL: the like for a sub-protocol whose one round is the sealing round,
    in which nothing is sent, and at whose place no part of a prover stands.
  **`doorYes_key`**: the rule's `DoorYes` at the key file's description: the third chain's start
    returns, where the two earlier threads' last sentences give `Start₃` (E2E/KeyStartThird.lean).
  **`finYes_key`**: the rule's `FinYes` there: the last test accepts, where the threads' last
    sentences give the library's book-keeping of the first chain at its border 19 and `fin₃` of the
    third chain's last state (E2E/KeyPasses.lean's `fin_of_shape`).
  AT THE KEY FILE's OWN SUB-PROTOCOLS, for threads whose lists are the description's flat lists:
    **`accepted_seal`** (the first chain's last; from `End₁` and `Listed`) · **`accepted_end₂`**
    (the shared chain's last; from the library's book-keeping at border 11 and `Listed`) ·
    **`accepted_k14Second`** (the third chain's number 0; from the premises of E2E/KeyDotRow.lean's
      `k14Second_passes'`) ·
    **`accepted_takenSources`** (number 1; from the library's `Third.Law.Tied`;
    `accepted_takenSources'`: in scope, from four trees' numbers in the book: E2E/KeySources.lean) ·
    **`accepted_end₃`** (number 3; from the library's book-keeping at border 3, `Older` and
    `Listed`). `flat_last`: a chain's flat list ends in its last sub-protocol.
The rule's premise on the instance (the description's test on it accepts) is E2E/KeyPasses.lean's
`okStart_named`, at the written key of every OOD sample.

THE VARIABLE fall. The rule excuses a sub-protocol's own step wherever a test "fall", a free
variable, says something; then it asks that no fall speaks along the run. At a sub-protocol without
a round a fall whose test is "this step rejects" would make `Accepted` hold for nothing, and move
the whole question into that premise. EVERY ADAPTER HERE HOLDS AT EVERY fall, SO ALSO AT THE ONE
THAT NEVER SPEAKS: at these sub-protocols no fall is needed: the book-keeping in front gives the
acceptance. Whoever spends the rule with these adapters takes a fall that says nothing at their
numbers b: `fall b = fun _ _ => none`.

Limits.
- No thread of the key file is laid here: the adapters' premises on the threads' sentences are met
  by nothing yet.
- `accepted_sealed` asks the decision's acceptance at all rounds and columns: a chain's end reads
  neither.
- The premises of the sentences that are called are theirs: see the heads of the files named.
- The rule itself is conditional and pointwise; see its own head.


-/
import E2E.KeyPasses
import E2E.KeyStartThird
import E2E.KeyEnds
import E2E.KeyEndFirst
import E2E.KeyDotRow
import E2E.KeyPublic
import E2E.KeySources
import Johnson.Desc.ProofFile.Honest.Thread.FileRowYes
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

section General
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **A sub-protocol without a round is accepted where its decision accepts.** -/
theorem accepted_quiet {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = [])
    (h : ∀ k s m E, Thr T b k s m E → ∃ s', blk.decide s [] [] = .ok s') : Accepted T fall b :=
  accepted_of_runs T hblk fun k s m E ds l hT hd hl => by
    have hl0 : l = [] := by
      have e := steps_decl hl
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
      exact List.map_eq_nil_iff.1 e
    have hd0 : ds = [] := by
      have e := drawsFit_length _ _ hd
      rw [hr] at e
      exact List.eq_nil_of_length_eq_zero e
    subst hl0
    subst hd0
    obtain ⟨s', hs⟩ := h k s m E hT
    refine ⟨([], m), [], s', rfl, ?_, ?_⟩
    · rw [hr]
      rfl
    · refine VerifiableInference.Desc.Block.step_ok.2 ⟨?_, ?_, ?_, ?_⟩
      · rw [hr]
        rfl
      · rw [hr]
        rfl
      · rw [hr]
        exact hs
      · rw [hr]
        rfl

/-- **The like for a sub-protocol whose one round is the sealing round**, at whose place no part of
a prover stands. -/
theorem accepted_sealed {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = [VerifiableInference.Desc.ChainEnd.sealRound]) (ho : blk.oracles = [[]])
    (hn : (T.hs.find? fun g => g.place == blk.place) = none)
    (h : ∀ k s m E rs gs, Thr T b k s m E → ∃ s', blk.decide s rs gs = .ok s') :
    Accepted T fall b :=
  accepted_of_runs T hblk fun k s m E ds l hT hd hl => by
    have el := steps_one_none hn hl
    subst el
    rw [hr] at hd
    obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd
    have eb : bareSteps (W := W) (Y := X) blk =
        [⟨blk.name, ⟨blk.place, 0⟩, VerifiableInference.Desc.ChainEnd.sealRound, [],
          fun _ _ => none, fun _ _ => none, 0, false, none⟩] := by
      simp [bareSteps, hr, ho]
    rw [eb]
    obtain ⟨s', hs⟩ := h k s m E _ _ hT
    refine ⟨_, [], s', rfl, ?_, ?_⟩
    · rw [hr]
      rfl
    · refine VerifiableInference.Desc.Block.step_ok.2 ⟨?_, ?_, hs, ?_⟩
      · rw [hr]
        exact (ProofFile.Honest.Toy.roundsFit_cons (by with_unfolding_all rfl) h₀).trans
          (by with_unfolding_all rfl)
      · rw [hr]
        rfl
      · rw [hr]
        rfl

end General

section Key
variable {W₀ Rc Ky Tr X₀ Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
  (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)
  (T₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (T₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)
  (x : KeyInst) (k : Coins Bk)

/-- **The third chain's start returns**, in the rule's form. -/
theorem doorYes_key
    (h : ∀ e₁ m₁ E₁ e₂ m₂ E₂, Thr T₁ (keyFileDescription X N P).first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ (keyFileDescription X N P).shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∃ l, Start₃ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape e₁ e₂ l) :
    DoorYes (keyFileDescription X N P) T₁ T₂ x k := fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ => by
  obtain ⟨l, hl⟩ := h e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
  exact ⟨_, start₃_passes X N P x e₁ e₂ l hl⟩

open Johnson.RunOne.KeyRows1 in
/-- **The last test accepts**, in the rule's form. -/
theorem finYes_key
    (h₁ : ∀ e₁ m₁ E₁, Thr T₁ (keyFileDescription X N P).first.blocksInOrder.length k e₁ m₁ E₁ →
      VerifiableInference.Desc.Key.shape₁ (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime)
        (book₁ X.Y.k.oneTime) 2 (slots₁ X.Y.k.oneTime) 19 e₁ = true)
    (h₃ : ∀ e₃ m₃ E₃, Thr T₃ (keyFileDescription X N P).second.blocksInOrder.length k e₃ m₃ E₃ →
      VerifiableInference.Desc.Third.fin₃ e₃ = true) :
    FinYes (keyFileDescription X N P) T₁ T₂ T₃ x k := fun e₁ m₁ E₁ e₂ _ _ e₃ m₃ E₃ u₁ _ u₃ =>
  fin_of_shape X N P x e₁ e₂ e₃ (h₁ e₁ m₁ E₁ u₁) (h₃ e₃ m₃ E₃ u₃)

/-! ## At the first two chains' ends -/

omit X N P T₁ T₂ T₃ x k in
/-- A chain's flat list ends in its last sub-protocol: with its rounds, oracle messages, place and
decision. -/
theorem flat_last {S Cl : Type} (c : VerifiableInference.Desc.Chain S Cl) :
    ∃ blk, c.blocksInOrder[c.blocksInOrder.length - 1]? = some blk ∧ blk.rounds = c.last.rounds ∧
      blk.oracles = c.last.oracles ∧ blk.place = c.last.place ∧ blk.decide = c.last.decide := by
  refine ⟨{ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }, ?_, rfl, rfl, rfl, rfl⟩
  show (_ ++ [_])[(_ ++ [_]).length - 1]? = _
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- **The first chain's seal** is accepted where the thread's sentence in front of it gives `End₁`
(E2E/KeyEndFirst.lean) and `Listed`, and no part of a prover stands at its place. -/
theorem accepted_seal {fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String}
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder) (n a : Nat)
    (hn : (T₁.hs.find? fun g => g.place == (keyFileDescription X N P).first.last.place) = none)
    (h : ∀ k s m E, Thr T₁ ((keyFileDescription X N P).first.blocksInOrder.length - 1) k s m E →
      End₁ n a (show VerifiableInference.Desc.Key.FirstState from s) ∧
        Listed (show VerifiableInference.Desc.Key.FirstState from s).d.st) :
    Accepted T₁ fall ((keyFileDescription X N P).first.blocksInOrder.length - 1) := by
  obtain ⟨blk, e, hr, ho, hp, hd⟩ := flat_last (keyFileDescription X N P).first
  exact accepted_sealed T₁ (by rw [hbs]; exact e) (hr.trans rfl) (ho.trans rfl)
    (by rw [hp]; exact hn) fun k s m E rs gs hT => by
      obtain ⟨h1, h2⟩ := h k s m E hT
      exact ⟨s, by
        rw [hd]
        exact seal_passes n a _ h1 (joined_of_listed _ h2) _ _ rs gs⟩

/-- **The shared chain's end** is accepted where the thread's sentence in front of it gives the
library's book-keeping at border 11 and `Listed`, and no part of a prover stands at its place. -/
theorem accepted_end₂ {fall : Nat → (keyFileDescription X N P).S₂ → List Fmt.Drawn → Option String}
    (hbs : T₂.bs = (keyFileDescription X N P).shared.blocksInOrder) (S : OnBytes.Params.LinShape) (a : Nat)
    (hn : (T₂.hs.find? fun g => g.place == (keyFileDescription X N P).shared.last.place) = none)
    (h : ∀ k s m E, Thr T₂ ((keyFileDescription X N P).shared.blocksInOrder.length - 1) k s m E →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 11 s) = true ∧
        Listed (show _root_.Desc.K14.St from s).st) :
    Accepted T₂ fall ((keyFileDescription X N P).shared.blocksInOrder.length - 1) := by
  obtain ⟨blk, e, hr, ho, hp, hd⟩ := flat_last (keyFileDescription X N P).shared
  exact accepted_sealed T₂ (by rw [hbs]; exact e) (hr.trans rfl) (ho.trans rfl)
    (by rw [hp]; exact hn) fun k s m E rs gs hT => by
      obtain ⟨h1, h2⟩ := h k s m E hT
      exact ⟨s, by
        rw [hd]
        exact end₂_passes S a s h1 (joined_of_listed _ h2) [] rs gs⟩

/-! ## At the third chain's own sub-protocols -/

section Third
variable {fall : Nat → (keyFileDescription X N P).S₃ → List Fmt.Drawn → Option String}
  (hbs : T₃.bs = (keyFileDescription X N P).second.blocksInOrder)
include hbs

/-- **"K14, second part"**, the third chain's sub-protocol number 0, is accepted where the thread's
first sentence gives the premises of E2E/KeyDotRow.lean's `k14Second_passes'`. -/
theorem accepted_k14Second
    (h : ∀ k s m E, Thr T₃ 0 k s m E → ∃ x q t y G lay dot, s.loc.border = some x ∧
      VerifiableInference.Desc.Third.firstStepB s.roots s.loc.firstTree s.book = true ∧
      Taken X.chains.made.sized.key.once.shape s x.shared q t y G lay ∧ Listed s.st ∧
      OnBytes.linDotRow X.chains.made.sized.key.once.shape x.g x.shared.psi s.st.oracles.size
        (OnBytes.linLayOmega (stTaken X.chains.made.sized.key.once.shape s y G).codes
          X.chains.made.sized.key.once.shape) s.loc.w
        (OnBytes.linLayW (stTaken X.chains.made.sized.key.once.shape s y G).codes
          X.chains.made.sized.key.once.shape) = some dot ∧
      PadsClear (stTaken X.chains.made.sized.key.once.shape s y G) (groupTaken s G) dot ∧
      TermsFit (stTaken X.chains.made.sized.key.once.shape s y G) (groupTaken s G) dot)
    (hp : (keyFileDescription X N P).planOk = true) : Accepted T₃ fall 0 :=
  accepted_quiet T₃ (b := 0) (by rw [hbs]; rfl) rfl fun k s m E hT => by
    obtain ⟨x, q, t, y, G, lay, dot, h1, h2, h3, h4, h5, h6, h7⟩ := h k s m E hT
    obtain ⟨s', e, -⟩ := k14Second_passes' (Cl := Unit)
      (VerifiableInference.Desc.Key.thirdPar X.chains) s x q t y G lay dot h1 (third_public hp).2
      h2 h3 h4 h5 h6 h7 [] []
    exact ⟨s', e⟩

/-- **"The taken trees' sources"**, number 1, is accepted where the thread's sentence in front of it
gives the library's `Third.Law.Tied`. -/
theorem accepted_takenSources
    (h : ∀ k s m E, Thr T₃ 1 k s m E →
      VerifiableInference.Desc.Third.Law.Tied (VerifiableInference.Desc.Key.ownTest P) s) :
    Accepted T₃ fall 1 := by
  have hb : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[1]? = some blk ∧ blk.rounds = [] ∧
      ∀ s, blk.decide s [] [] = (VerifiableInference.Desc.Third.takenSources
        (VerifiableInference.Desc.Key.ownTest P)).decide s [] [] := ⟨_, rfl, rfl, fun _ => rfl⟩
  obtain ⟨blk, e, hr, hd⟩ := hb
  exact accepted_quiet T₃ (b := 1) (by rw [hbs]; exact e) hr fun k s m E hT =>
    ⟨s, by rw [hd]; exact takenSources_passes _ s [] [] (h k s m E hT)⟩

/-- **The same in scope**, where the thread's sentence gives the four trees' numbers
(E2E/KeySources.lean). -/
theorem accepted_takenSources' {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (h : ∀ k s m E, Thr T₃ 1 k s m E →
      VerifiableInference.Desc.Third.takenOf s = some takenFull) : Accepted T₃ fall 1 :=
  accepted_takenSources X N P T₃ hbs fun k s m E hT => tied_in_scope hs scope s (h k s m E hT)

/-- **The third chain's end**, number 3, is accepted where the thread's sentence in front of it
gives the library's book-keeping at border 3, `Older` and `Listed`. -/
theorem accepted_end₃ (S : OnBytes.Params.LinShape) (a n g t : Nat) (idx : List Nat)
    (h : ∀ k s m E, Thr T₃ 3 k s m E →
      LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a n g t idx 3 s) = true ∧ Older n g s.st ∧
        Listed s.st) : Accepted T₃ fall 3 := by
  have hb : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[3]? = some blk ∧ blk.rounds = [] ∧
      ∀ s, blk.decide s [] [] = (VerifiableInference.Desc.Third.end₃ (Cl := Unit) []).decide s [] []
      := ⟨_, rfl, rfl, fun _ => rfl⟩
  obtain ⟨blk, e, hr, hd⟩ := hb
  exact accepted_quiet T₃ (b := 3) (by rw [hbs]; exact e) hr fun k s m E hT => by
    obtain ⟨h1, h2, h3⟩ := h k s m E hT
    exact ⟨s, by
      rw [hd]
      exact end₃_passes (Cl := Unit) S a n g t idx s h1 h2 (joined_of_listed _ h3) [] [] []⟩

end Third

end Key

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accepted_quiet
#print axioms AtPublicFiles.AtFiles.accepted_sealed
#print axioms AtPublicFiles.AtFiles.doorYes_key
#print axioms AtPublicFiles.AtFiles.finYes_key
#print axioms AtPublicFiles.AtFiles.flat_last
#print axioms AtPublicFiles.AtFiles.accepted_seal
#print axioms AtPublicFiles.AtFiles.accepted_end₂
#print axioms AtPublicFiles.AtFiles.accepted_k14Second
#print axioms AtPublicFiles.AtFiles.accepted_takenSources
#print axioms AtPublicFiles.AtFiles.accepted_takenSources'
#print axioms AtPublicFiles.AtFiles.accepted_end₃
