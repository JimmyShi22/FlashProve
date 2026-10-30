-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoined3.lean: CONDITIONAL: ALL THE DEBTS OF THE MEMBER AT AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5) IN ONE STATEMENT, AT THE FIRST CHAIN's LETTERS AS THEY ARE
LAID (`lettersHead`, Honest/Thread/FirstHead.lean): `k5_owes_all_joined_head₂`
(Honest/K5/Law/AllJoined2.lean) WITH ITS PREMISE hK, THE TEXT ON THE KEY POINTS, STRUCK FOR A
PREMISE ON THE VERIFIER's OWN STEP OF THE MEMBER RIGHT IN FRONT (`K3Back`,
Honest/K5/Law/KeyTextK3.lean). It proves nothing new: it joins.

  `k5_owes_all_joined_head₃`   CONDITIONAL: **`Plays`, `Behind`, `Exchange`, `RidesPast` and, for
                               every fall, `Accepted`**, Kp and b₀ letters
  `k5_owes_all_joined_kind₃`   CONDITIONAL: the same at Kp := `kpBy` f
                               (Honest/Thread/KeepsBy.lean) with `K5KeepsAt` at K5

THE PREMISES OF `k5_owes_all_joined_head₃`, ALL OF THEM. Those of `k5_owes_all_joined_head₂` but hK:
h · hg · hG · hL · hfit, hb · hKpM · hb₀ · hRdM · hr · hN · HQ · hH; and H3: at the member number 14
(2 g + 1) + 3 there are public parameters of a lookup, with the plan's shape, at which `K3Back`
holds. H3 NAMES NO STAND OF THE `Thread`, NO RUN AND NO WITNESS.

THE FORMS WITH hLent. Of hr (one return of the frame's `ready`, a routine over the whole prover, the
whole book and all three chains) the laws here spend one thing alone: hLent: the book's lending to
the kind's own row returns, at all coins: `Lends5` (Honest/K5/Law/CoinsFewOf.lean) at what the maker
of the place's public data yields. It names no input, no trace, no other kind's half and no other
chain; of the book it reads the first chain's rows and the entries. `k5_owes_all_joined_head₃_lent`
and `k5_owes_all_joined_kind₃_lent` take hLent in hr's stead. hr gives hLent by
`k5_lent_of_ready_K3` (Honest/K5/Law/AllJoined2.lean). The forms with hr keep their names and
statements and follow from these. hLent is shown nowhere either.

Limits. Conditional. The limits of Honest/K5/Law/AllJoined.lean stand here too. H3 is shown here of
nothing: its form is the conclusion of `att_back_head` (Honest/K3/Law/Thread/AttBackHead.lean) at
one number ft; that file is not imported here; Honest/K5/Law/AllJoined5.lean imports it. h is a
hypothesis of every statement that names it. No file in the kind K5's folders shows HQ, hH or hr. Kp
and b₀ are letters of `lettersHead`. One kind's twelve members of the chain. At the library's full
size and the format's second hash function alone. The other forms stand beside these.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoined2
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyTextK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (seatTab Mem MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt k5KeepsAt_iff)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, THE TEXT ON THE KEY POINTS STRUCK
FOR `K3Back`.** CONDITIONAL: every premise stands, by name, in the file's head.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_head₃_lent {n g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.fits n = true)
    (hb : borderOf g < n)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOfK3 Zp G cF g a)) {N : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        fall (borderOf g) := by
  refine k5_owes_all_joined_head₂_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg hG hL hfit hb
    hKpM hb₀ hRdM hLent hN HQ (fun a blk ha hblk => ?_) hH
  have hlt : 14 * (2 * g + 1) + 3 < cF.blocksInOrder.length :=
    Nat.lt_of_succ_lt (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨p, hp, hB⟩ := H3 a _ ha (List.getElem?_eq_getElem hlt)
  exact keyText_K3 h
    (k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg)
    hg hG ha rfl (List.getElem?_eq_getElem hlt) hp hB blk

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, THE TEXT ON THE KEY POINTS STRUCK
FOR `K3Back`.** CONDITIONAL: every premise stands, by name, in the file's head.
By `k5_owes_all_joined_head₃_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_head₃ {n g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.fits n = true)
    (hb : borderOf g < n)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀) {N : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_head₃_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg hG hL hfit hb hKpM
    hb₀ hRdM (k5_lent_of_ready_K3 h H Q test carryX item n₁ n₂ Vd RdL KpL w hg hG hL hr) hN HQ H3 hH

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE CLAUSE
BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head₃`, with hf in hKpM's stead.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_kind₃_lent {n g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits n = true)
    (hb : borderOf g < n)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOfK3 Zp G cF g a)) {N : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_head₃_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w hg hG hL hfit hb
    (fun a ha s s' => (kpBy_at f rfl s s').trans (by
      rw [hf]
      exact k5KeepsAt_iff ha s s'))
    hb₀ hRdM hLent hN HQ H3 hH

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE CLAUSE
BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head₃`, with hf in hKpM's stead.
By `k5_owes_all_joined_kind₃_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_kind₃ {n g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits n = true)
    (hb : borderOf g < n)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀) {N : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_kind₃_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL f w hg hG hL hfit hb hf hb₀
    hRdM (k5_lent_of_ready_K3 h H Q test carryX item n₁ n₂ Vd RdL (kpBy f) w hg hG hL hr) hN HQ H3
    hH

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head₃_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head₃
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind₃_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind₃
