-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoined2.lean: CONDITIONAL: ALL THE DEBTS OF THE MEMBER AT AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5) IN ONE STATEMENT, AT THE FIRST CHAIN's LETTERS AS THEY ARE
LAID (`lettersHead`, Honest/Thread/FirstHead.lean), WITH THREE PREMISES OF `k5_owes_all_joined_head`
(Honest/K5/Law/AllJoined.lean) STRUCK AND THE NUMBER b₀ A VARIABLE. It proves nothing new: it joins.

WHAT IS STRUCK, AND BY WHAT.
  hKs (`KeySizes`) and hKey (the maker's third test): the reader of the key points is laid at the
    text of the lookup's honest side: keyOf := `keyOfK3` (Honest/K5/Law/KeyOfK3.lean; `keySizes_K3`;
    `keysFit_K3`, Honest/K5/Law/KeysFitK3.lean)
  hL5 (`LedgerIs`): `ledgerIs_k5` (Honest/Law/Rule/LedgerCallers.lean), at the number that the
    filling has for the segment, which under h is `Forest.elems` a.fs (`first_at_head`,
    Johnson/Desc/K5/Honest/Law/FoAtHead.lean): so the number ν₅ is no letter any more
WHAT HAS COME. hb₀: the member that hears the reply is not this one (b₀ is not the border behind
  this member): in the stead of b₀ := `replyBorder`. At `replyBorder` it is `reply_behind`.

  `b0_ne_of_lt`                hb₀ at all twelve groups from 327 < b₀
  `k5_owes_all_joined_head₂`   CONDITIONAL: **`Plays`, `Behind`, `Exchange`, `RidesPast` and, for
                               every fall, `Accepted`**, Kp and b₀ letters
  `k5_owes_all_joined_kind₂`   CONDITIONAL: the same at Kp := `kpBy` f
                               (Honest/Thread/KeepsBy.lean) with `K5KeepsAt` at K5

THE PREMISES OF `k5_owes_all_joined_head₂`, ALL OF THEM. h · hg · hG: G is the ground that the
description's maker makes · hL: `LotLaid` at the maker with three tests, at `keyOfK3` · hfit, hb:
the test T.fits · hKpM: the letter Kp at the kind's place is `K5KeepsM` at the group's plan's
numbers · hb₀ · hRdM: the letter Rd's part goes on along the clause · hr: `ready` returns once · hN
· HQ: `K5ScriptQ`: two equations on the Script, at ν₅ := `Forest.elems` a.fs · hK: the text on the
key points, at `keyOfK3` · hH: where the run's own input meets Vd, the cells that the Script lays
for it hold an index.

THE FORMS WITH hLent. Of hr (one return of the frame's `ready`, a routine over the whole prover, the
whole book and all three chains) the laws here spend one thing alone: hLent: the book's lending to
the kind's own row returns, at all coins: `Lends5` (Honest/K5/Law/CoinsFewOf.lean) at what the maker
of the place's public data yields. It names no input, no trace, no other kind's half and no other
chain; of the book it reads the first chain's rows and the entries. `k5_owes_all_joined_head₂_lent`
and `k5_owes_all_joined_kind₂_lent` take hLent in hr's stead. `k5_lent_of_ready_K3`: hr, with hg, hG
and hL, gives hLent at `keyOfK3`. The forms with hr keep their names and statements and follow from
these. hLent is shown nowhere either.

Limits. Conditional. The limits of Honest/K5/Law/AllJoined.lean stand here too: on ans and on the
identities the weight has moved, not gone; the statement is met for nothing where the run's input
does not meet Vd, and would be if no member of the laid list sat at the tenant of a pin that is open
at the border. h is a hypothesis of every statement that names it. No file in the kind K5's folders
shows HQ, hK, hH or hr; Honest/K5/Law/AllJoined3.lean trades hK for a premise H3. Kp and b₀ are
letters of `lettersHead`. One member of the chain. At the library's full size and the format's
second hash function alone. The other forms stand beside these.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoined
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysFitK3
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerCallers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (K3Pts)
open VerifiableInference.Desc.Sound (seatTab Mem MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt k5KeepsAt_iff)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

/-- **A number above 327 is the border behind none of the kind's twelve members.** No premise but
these two bounds. 327 is the border behind the last of the twelve. -/
theorem b0_ne_of_lt {b₀ g : Nat} (h327 : 327 < b₀) (hg : g < 12) : b₀ ≠ borderOf g + 1 := by
  unfold borderOf
  omega

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

include h Q test carryX item n₁ n₂ Vd RdL KpL w in
/-- **ONE RETURN OF `ready` GIVES hLent, AT keyOfK3.** CONDITIONAL: g is below 12; hG; hL; hr. By
`k5_lent_of_ready` (Honest/K5/Law/AllJoined.lean), `keysFit_K3` and `keySizes_K3`. The letters Q
to w stand in the proof alone. -/
theorem k5_lent_of_ready_K3 {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOfK3 Zp G cF g a) :=
  k5_lent_of_ready h H Q test carryX item n₁ n₂ Vd RdL KpL w hg hG
    (fun _ ha => keysFit_K3 h hg hG ha)
    (fun _ _ => keySizes_K3 (Z := Zp) (G := G) (l := 2 * g + 1) rfl) hL hr

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, keyOf AT THE TEXT OF THE LOOKUP's
HONEST SIDE, THE LEDGER BY `ledgerIs_k5`, b₀ A VARIABLE.** CONDITIONAL: every premise stands, by
name, in the file's head.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_head₂_lent {n g : Nat} (hg : g < 12) {G : Ground}
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
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOfK3 Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
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
  obtain ⟨blk, a, ha, Hs⟩ := k5_seated_keys h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s')
    hg hG (fun a ha => keysFit_K3 h hg hG ha)
    (fun a _ => keySizes_K3 (Z := Zp) (G := G) (l := 2 * g + 1) rfl) hL
  obtain ⟨x₁, hx⟩ := (seated_decides h hg ha Hs.member).1.look
  have hν := H2K5.Honest.first_at_head h ha hx
  exact k5_owes_all_joined_T h
    (k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg)
    (k5RidersM_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg
      fun s s' k => (hKpM a ha s s').1
        ((keeps_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg s s').1 k))
    hg ha hx Hs hfit hb
    (fun s s' k => (keeps_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg s s').2
      ((hKpM a ha s s').2 k))
    (rides_head_M h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hb₀ (hRdM a ha))
    (fun _ _ _ => rfl) rfl (fun _ hv => hv.2) hN (HQ a x₁ ha hx)
    (fun k s m E hT p hp =>
      FirstThread.ledgerIs_k5 h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg hν k s m E hT p hp)
    (hLent a ha)
    (hK a blk ha Hs.member) rfl (holdsOwed_head Vd w hH)

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, keyOf AT THE TEXT OF THE LOOKUP's
HONEST SIDE, THE LEDGER BY `ledgerIs_k5`, b₀ A VARIABLE.** CONDITIONAL: every premise stands, by
name, in the file's head.
By `k5_owes_all_joined_head₂_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_head₂ {n g : Nat} (hg : g < 12) {G : Ground}
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
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOfK3 Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
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
  k5_owes_all_joined_head₂_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg hG hL hfit hb hKpM
    hb₀ hRdM (k5_lent_of_ready_K3 h H Q test carryX item n₁ n₂ Vd RdL KpL w hg hG hL hr) hN HQ hK hH

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
`k5_owes_all_joined_head₂`, with hf in hKpM's stead. hf asks more than is spent: an equation at all
places, where hKpM speaks of one.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_kind₂_lent {n g : Nat} (hg : g < 12) {G : Ground}
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
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOfK3 Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
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
  k5_owes_all_joined_head₂_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w hg hG hL hfit hb
    (fun a ha s s' => (kpBy_at f rfl s s').trans (by
      rw [hf]
      exact k5KeepsAt_iff ha s s'))
    hb₀ hRdM hLent hN HQ hK hH

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE CLAUSE
BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head₂`, with hf in hKpM's stead. hf asks more than is spent: an equation at all
places, where hKpM speaks of one.
By `k5_owes_all_joined_kind₂_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_kind₂ {n g : Nat} (hg : g < 12) {G : Ground}
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
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOfK3 Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
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
  k5_owes_all_joined_kind₂_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL f w hg hG hL hfit hb hf hb₀
    hRdM (k5_lent_of_ready_K3 h H Q test carryX item n₁ n₂ Vd RdL (kpBy f) w hg hG hL hr) hN HQ hK
    hH

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.b0_ne_of_lt
#print axioms ProofFile.Honest.K5.k5_lent_of_ready_K3
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head₂_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head₂
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind₂_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind₂
