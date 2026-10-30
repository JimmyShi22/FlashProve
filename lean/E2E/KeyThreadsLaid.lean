--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyThreadsLaid.lean: THE KEY FILE's THREE THREADS, AS FAR AS THE SUB-PROTOCOLS WITHOUT A PART OF
A PROVER, THE THIRD CHAIN's START AND THE LAST TEST GO. To any three threads over the key file's
description (Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) clauses on the verifier's state are
added, border by border; then the adapters of E2E/KeyThreads.lean are paid by calls. NOTHING IS
SHOWN
OF ANY PROVER.

General.
  `withForm T Φ`: the thread T with one more clause in its sentence's part on the public
    book-keeping: Φ at the border's number and the verifier's state. All other letters are T's.
  `thr_withForm`: where that thread stands, Φ holds. `thr_of_withForm`: and T stands.
At the key file's description `keyFileDescription X N P`.
  `KeyNums`: the numbers that the clauses name: letters.
  `Last₁`, `Last₂`, `start₃_of_lasts`: what the third chain's start asks (`Start₃`,
    E2E/KeyStartThird.lean), split: five clauses on the first chain's last state, two on the shared
    chain's; its two clauses on public values come from the description's test on its own rounds.
  `Second₀`: the premises of the third chain's first sub-protocol's adapter, under one name.
  `Form₁`, `Form₂`, `Form₃`: THE CLAUSES, BORDER BY BORDER. At every border: every member of every
    group is listed (`Listed`). In front of a chain's end: what the end's adapter asks. At a chain's
    last border: what the third chain's start and the last test ask of that chain.
  **`seal_laid`, `end₂_laid`, `k14Second_laid`, `takenSources_laid`, `end₃_laid`**: the five
    sub-protocols are accepted (`Accepted`), at every fall, at the threads so laid.
  **`door_laid`, `fin_laid`**: the third chain's start returns (`DoorYes`); the last test accepts
    (`FinYes`).

Limits.
- THE CLAUSES ARE MOVED, NOT PAID. Whatever is added to a thread's sentence has to be shown in front
  of the first sub-protocol (`Enters₁`, `Enters₂`, `DoorBehind`) and kept by every sub-protocol
  (`Behind`): these debts get heavier by just these clauses. Nothing here pays them. That `Listed`
  is kept by every sub-protocol's own step is shown in E2E/KeyListed.lean, in another form.
- The base threads are free letters; so are the numbers.
- The shared chain's first sub-protocol, which has no round either, has no adapter here.
- Every adapter holds at every fall: at these sub-protocols none is needed.
- No sub-protocol with a part of a prover is treated.

-/
import E2E.KeyThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLink
open ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A thread with one more clause on the verifier's state.** -/
def withForm (T : Thread Bk S Cl V W X Pb) (Φ : Nat → S → Prop) : Thread Bk S Cl V W X Pb :=
  { T with formP := fun b q => T.formP b q ∧ Φ b q.2 }

/-- Where it stands, the clause holds. -/
theorem thr_withForm {T : Thread Bk S Cl V W X Pb} {Φ : Nat → S → Prop} {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid W X} {E : Env} (h : Thr (withForm T Φ) b k s m E) : Φ b s :=
  h.2.2.1.2.2

/-- And the thread without the clause stands. -/
theorem thr_of_withForm {T : Thread Bk S Cl V W X Pb} {Φ : Nat → S → Prop} {b : Nat}
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (h : Thr (withForm T Φ) b k s m E) :
    Thr T b k s m E :=
  ⟨h.1, h.2.1, ⟨h.2.2.1.1, h.2.2.1.2.1⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end AtPublicFiles.KeyLink

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink
open OnBytes
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.Third (numbersOk)
open Johnson.RunOne.KeyRows1

/-- The numbers that the clauses name. -/
structure KeyNums where
  /-- the first chain's end: the ranges' test's stages; the answers to a sample -/
  n₁ : Nat
  a₁ : Nat
  /-- the shared chain's end -/
  S₂ : LinShape
  a₂ : Nat
  /-- the third chain's end -/
  S₃ : LinShape
  a₃ : Nat
  n₃ : Nat
  g₃ : Nat
  t₃ : Nat
  idx₃ : List Nat

/-- What the third chain's start asks of the first chain's last state. -/
def Last₁ (codes : Codes) (S : LinShape) (s : FirstState) : Prop :=
  ∃ l, s.lin = some l ∧ l.mask.isSome = S.masksAhead ∧ numbersOk S (firstOutOf s l) = true ∧
    s.d.st.codes = codes ∧ s.d.roots = s.d.book.trees.size

/-- What it asks of the shared chain's last state. -/
def Last₂ (codes : Codes) (s : _root_.Desc.K14.St) : Prop :=
  _root_.Desc.K14.tested s = true ∧ s.st.codes = codes

section Key
variable {W₀ Rc Ky Tr X₀ Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- The two halves, with the two clauses on public values, give all that the start asks. -/
theorem start₃_of_lasts (hp : (keyFileDescription X N P).planOk = true) {s₁ : FirstState}
    {s₂ : _root_.Desc.K14.St}
    (h₁ : Last₁ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape s₁)
    (h₂ : Last₂ X.chains.made.sized.key.codes s₂) :
    ∃ l, Start₃ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape s₁ s₂ l := by
  obtain ⟨l, c1, c2, c3, c4, c5⟩ := h₁
  exact ⟨l, (third_public hp).1, (third_public hp).2, c1, c2, c3, c4, c5, h₂.1, h₂.2⟩

/-- The premises of the adapter of the third chain's first sub-protocol. -/
def Second₀ (s : (keyFileDescription X N P).S₃) : Prop :=
  ∃ x q t y G lay dot, s.loc.border = some x ∧
    VerifiableInference.Desc.Third.firstStepB s.roots s.loc.firstTree s.book = true ∧
    Taken X.chains.made.sized.key.once.shape s x.shared q t y G lay ∧ Listed s.st ∧
    OnBytes.linDotRow X.chains.made.sized.key.once.shape x.g x.shared.psi s.st.oracles.size
      (OnBytes.linLayOmega (stTaken X.chains.made.sized.key.once.shape s y G).codes
        X.chains.made.sized.key.once.shape) s.loc.w
      (OnBytes.linLayW (stTaken X.chains.made.sized.key.once.shape s y G).codes
        X.chains.made.sized.key.once.shape) = some dot ∧
    PadsClear (stTaken X.chains.made.sized.key.once.shape s y G) (groupTaken s G) dot ∧
    TermsFit (stTaken X.chains.made.sized.key.once.shape s y G) (groupTaken s G) dot

/-- **The first chain's clauses.** -/
def Form₁ (q : KeyNums) (b : Nat) (s : (keyFileDescription X N P).S₁) : Prop :=
  Listed (show FirstState from s).d.st ∧
    (b = (keyFileDescription X N P).first.blocksInOrder.length - 1 → End₁ q.n₁ q.a₁ (show FirstState from s)) ∧
    (b = (keyFileDescription X N P).first.blocksInOrder.length →
      Last₁ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape s ∧
        VerifiableInference.Desc.Key.shape₁ (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime)
          (book₁ X.Y.k.oneTime) 2 (slots₁ X.Y.k.oneTime) 19 s = true)

/-- **The shared chain's clauses.** -/
def Form₂ (q : KeyNums) (b : Nat) (s : (keyFileDescription X N P).S₂) : Prop :=
  Listed (show _root_.Desc.K14.St from s).st ∧
    (b = (keyFileDescription X N P).shared.blocksInOrder.length - 1 →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ q.S₂ q.a₂ 11 s) = true) ∧
    (b = (keyFileDescription X N P).shared.blocksInOrder.length → Last₂ X.chains.made.sized.key.codes s)

/-- **The third chain's clauses.** -/
def Form₃ (q : KeyNums) (b : Nat) (s : (keyFileDescription X N P).S₃) : Prop :=
  Listed s.st ∧ (b = 0 → Second₀ X N P s) ∧
    (b = 1 → VerifiableInference.Desc.Third.takenOf s = some takenFull) ∧
    (b = 3 → LKFU.Shape23.ok (LKFU.Shape23.shape₃ q.S₃ q.a₃ q.n₃ q.g₃ q.t₃ q.idx₃ 3 s) = true ∧
      Older q.n₃ q.g₃ s.st) ∧
    (b = (keyFileDescription X N P).second.blocksInOrder.length → VerifiableInference.Desc.Third.fin₃ s = true)

variable (q : KeyNums)
  (U₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)
  (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)

/-- **The first chain's seal is accepted.** -/
theorem seal_laid {fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String}
    (hbs : U₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hn : (U₁.hs.find? fun g => g.place == (keyFileDescription X N P).first.last.place) = none) :
    Accepted (withForm U₁ (Form₁ X N P q)) fall ((keyFileDescription X N P).first.blocksInOrder.length - 1) :=
  accepted_seal X N P (withForm U₁ (Form₁ X N P q)) hbs q.n₁ q.a₁ hn fun _ _ _ _ hT =>
    ⟨(thr_withForm hT).2.1 rfl, (thr_withForm hT).1⟩

/-- **The shared chain's end is accepted.** -/
theorem end₂_laid {fall : Nat → (keyFileDescription X N P).S₂ → List Fmt.Drawn → Option String}
    (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hn : (U₂.hs.find? fun g => g.place == (keyFileDescription X N P).shared.last.place) = none) :
    Accepted (withForm U₂ (Form₂ X N P q)) fall ((keyFileDescription X N P).shared.blocksInOrder.length - 1) :=
  accepted_end₂ X N P (withForm U₂ (Form₂ X N P q)) hbs q.S₂ q.a₂ hn fun _ _ _ _ hT =>
    ⟨(thr_withForm hT).2.1 rfl, (thr_withForm hT).1⟩

variable {fall : Nat → (keyFileDescription X N P).S₃ → List Fmt.Drawn → Option String}
  (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder)
include hbs

/-- **The third chain's first sub-protocol is accepted.** -/
theorem k14Second_laid (hp : (keyFileDescription X N P).planOk = true) :
    Accepted (withForm U₃ (Form₃ X N P q)) fall 0 :=
  accepted_k14Second X N P (withForm U₃ (Form₃ X N P q)) hbs
    (fun _ _ _ _ hT => (thr_withForm hT).2.1 rfl) hp

/-- **"The taken trees' sources" is accepted**, in scope. -/
theorem takenSources_laid {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) : Accepted (withForm U₃ (Form₃ X N P q)) fall 1 :=
  accepted_takenSources' X N P (withForm U₃ (Form₃ X N P q)) hbs hs scope fun _ _ _ _ hT =>
    (thr_withForm hT).2.2.1 rfl

/-- **The third chain's end is accepted.** -/
theorem end₃_laid : Accepted (withForm U₃ (Form₃ X N P q)) fall 3 :=
  accepted_end₃ X N P (withForm U₃ (Form₃ X N P q)) hbs q.S₃ q.a₃ q.n₃ q.g₃ q.t₃ q.idx₃
    fun _ _ _ _ hT =>
      ⟨((thr_withForm hT).2.2.2.1 rfl).1, ((thr_withForm hT).2.2.2.1 rfl).2, (thr_withForm hT).1⟩

omit hbs fall

/-- **The third chain's start returns.** -/
theorem door_laid (hp : (keyFileDescription X N P).planOk = true) (x : KeyInst) (k : Coins Bk) :
    DoorYes (keyFileDescription X N P) (withForm U₁ (Form₁ X N P q)) (withForm U₂ (Form₂ X N P q)) x k :=
  doorYes_key X N P (withForm U₁ (Form₁ X N P q)) (withForm U₂ (Form₂ X N P q)) x k
    fun _ _ _ _ _ _ u₁ u₂ =>
      start₃_of_lasts X N P hp ((thr_withForm u₁).2.2 rfl).1 ((thr_withForm u₂).2.2 rfl)

/-- **The last test accepts.** -/
theorem fin_laid (x : KeyInst) (k : Coins Bk) :
    FinYes (keyFileDescription X N P) (withForm U₁ (Form₁ X N P q)) (withForm U₂ (Form₂ X N P q))
      (withForm U₃ (Form₃ X N P q)) x k :=
  finYes_key X N P (withForm U₁ (Form₁ X N P q)) (withForm U₂ (Form₂ X N P q))
    (withForm U₃ (Form₃ X N P q)) x k (fun _ _ _ u₁ => ((thr_withForm u₁).2.2 rfl).2)
    fun _ _ _ u₃ => (thr_withForm u₃).2.2.2.2 rfl

end Key

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyLink.thr_withForm
#print axioms AtPublicFiles.KeyLink.thr_of_withForm
#print axioms AtPublicFiles.AtFiles.start₃_of_lasts
#print axioms AtPublicFiles.AtFiles.seal_laid
#print axioms AtPublicFiles.AtFiles.end₂_laid
#print axioms AtPublicFiles.AtFiles.k14Second_laid
#print axioms AtPublicFiles.AtFiles.takenSources_laid
#print axioms AtPublicFiles.AtFiles.end₃_laid
#print axioms AtPublicFiles.AtFiles.door_laid
#print axioms AtPublicFiles.AtFiles.fin_laid
