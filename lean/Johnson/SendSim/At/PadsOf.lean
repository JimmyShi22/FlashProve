-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/PadsOf.lean: if the job fits its place and no seed's factor is 0, each answer of
the instance has a message coin of its own, which contributes its value to that answer and 0 to
every other answer. With it, the proof of Spec.padsOf.
Terms: Johnson/SendSim/At/Sim.lean; sender, wOf, put, slot, name, the instance's answers:
Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Algebra; no distribution is named.
  share_of  If the job fits its place (sendFits) and no seed's factor is 0, then for each name (k,
            i, s) of an answer there is a name n in CoinN, of oracle message k, such that the family
            with the value x at n and 0 elsewhere contributes x to the answer (k, i, s) and 0 to
            every other answer.
  padsOf    Spec.padsOf: under its four premises the instance has pads in the sense of Sender.Pads.
            The proof gives them all the factor 1.
  wt_eq     If the job fits its place, the contribution of message coins S to the answer (k, i, s)
            is coordinate s of bInv i, the inverse of the seed's factor, times K1's closed form of
            the answer (K1.Msg.form) on rowsR at no data and put S.
  rd_single   If the job fits its place and ride k' = none, then at no data and one value at one
            name n, each entry of a row's message in oracle message k' is 0, except where n's slot
            is located.
  rd_at_seat, rd_single_at   At the entry at which a slot is located, rowsR at no data has the
            slot's coin. If one value is put at a pad's name, that entry has the value at the
            answer's coordinate. The premises are in the doc comments.
  crd_theta, inMsg_of_place, form_one, ans_ext   Tools: the coordinates of a power of θ; a slot
            located in main or mask is not in a tail; K1's closed form on entries that are 0 but
            one; equality of names in AnsN.

Limits. The coin is obtained by choice: which coin it is, is not stated here. padSeat
(Johnson/SendSim/At/PadSeat.lean) gives it as an explicit term.

How it fits. mendsOf (Johnson/SendSim/At/MendsOf.lean) uses share_of, so the file serves rowsExact
(Johnson/SendSim/At/RowsExact.lean). Johnson/SendSim/At/PadSeat.lean and
Johnson/SendSim/At/Single.lean use wt_eq, rd_single, rd_single_at and form_one, on the way to
rowsFresh (Johnson/SendSim/At/RowsFresh.lean). Only pads_paid (Johnson/SendSim/At/Paid.lean), which
nothing uses, applies padsOf; it is here because it says in the model's own terms (Sender.Pads,
Johnson/SendSim/Pads.lean) what share_of proves. The proofs rest on pad_facts
(Johnson/SendSim/At/PadAt.lean), Johnson/SendSim/At/Cells.lean, Johnson/SendSim/At/FormOne.lean,
K1.Msg.weight_pad (Johnson/Desc/K1/Law/Catches.lean) and read_place
(Johnson/Desc/ProofFile/Honest/K1/NoOther.lean).

Notes. RidesZero and seedsFit are premises of Spec.padsOf. The proof uses neither.
-/
import Johnson.SendSim.At.PadAt
import Johnson.SendSim.At.FormOne

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- Coordinate s' of θ ^ s is 1 if s' = s, else 0. -/
theorem crd_theta (s' s : Fin 3) : crd s' (readE (thetaE s.val)) = if s' = s then 1 else 0 := by
  rw [readE_theta]
  fin_cases s' <;> fin_cases s <;> simp [crd]

variable (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn)

/-- If the job fits its place (sendFits), the contribution of the message coins S to the instance's
answer (k, i, s) is coordinate s of the inverse of the seed's factor times K1's closed form on the
sender's rows at no data and the coins put S. -/
theorem wt_eq (hf : sendFits P ride = true) (S : CoinN P ride → GF) (k : Fin P.sent.size)
    (i : Fin (shapeAt P k).answers) (s : Fin 3) :
    (sender P ride).wt (wOf P ds) S ⟨k, (i, s)⟩ =
      crd s (bInv P ds i * (K1.Msg.of P.codes (shapeAt P k)).form (readL (seedAt P ds i).1)
        (readE (seedAt P ds i).2) i
        ((rowsR P ride (fun _ _ _ => none) (put P ride S) k).word (shapeAt P k))) := by
  unfold Sender.wt
  show (sender P ride).form (wOf P ds ⟨k, (i, s)⟩)
    (entry P (rowsR P ride (fun _ _ _ => none) (put P ride S))) = _
  rw [form_at, Fintype.sum_sum_type, main_part P ride ds hf _ k i s,
    mask_part P ride ds hf _ k i s, form_rows, mul_add, crd_add]
  rfl

theorem inMsg_of_place (codes : Codes) (s : OracleShape) (R : Option Ride) (y : Seat) (tb : Rd)
    (r j : ℕ) (ht : tb = .main ∨ tb = .mask) (h : y.place codes s R = (tb, r, j)) :
    inMsg y = true := by
  cases y <;> first
    | rfl
    | (exfalso
       have h1 := congrArg Prod.fst h
       rcases ht with rfl | rfl <;> cases h1)

/-- If every entry of the arrays main and mask of V is 0 but the entry j0 of row r0 of the array tb,
with r0 and j0 within the sizes, K1's closed form on V is K1's weight at that entry's index times
the entry. -/
theorem form_one (codes : Codes) (s : OracleShape) (V : Rows) (z : ℕ → GE) (β : GE) (i : ℕ)
    (tb : Rd) (ht : tb = .main ∨ tb = .mask) (r0 j0 : ℕ) (hr : r0 < rowsOf s tb)
    (hj : j0 < 2 ^ lenOf codes s tb)
    (h : ∀ tb' r j, (tb' = .main ∨ tb' = .mask) → (tb', r, j) ≠ (tb, r0, j0) →
      rdAt V (s.mainDeg == 3) tb' r j = 0) :
    (K1.Msg.of codes s).form z β i (V.word s) =
      (K1.Msg.of codes s).weight z β i (partOf tb) (r0 + j0 * 2 ^ K1.clog (rowsOf s tb)) *
        rdAt V (s.mainDeg == 3) tb r0 j0 := by
  rcases ht with rfl | rfl
  · exact form_main_one codes s V z β i r0 j0 hr hj
      (fun r j hne => h .main r j (.inl rfl) fun e => hne (Prod.mk.inj e).2)
      fun r j => h .mask r j (.inr rfl) fun e => by cases (Prod.mk.inj e).1
  · exact form_mask_one codes s V z β i r0 j0 hr hj
      (fun r j => h .main r j (.inl rfl) fun e => by cases (Prod.mk.inj e).1)
      fun r j hne => h .mask r j (.inr rfl) fun e => hne (Prod.mk.inj e).2

variable {P ride} [inst : DecidableEq (CoinN P ride)]

/-- If the job fits its place (sendFits) and ride k' = none: at no data and the coins put (Pi.single
n x), an entry of the array main or mask of oracle message k' is 0, unless k' is n's oracle message
and n's slot is located at that entry. -/
theorem rd_single (hf : sendFits P ride = true) (n : CoinN P ride) (x : GF)
    (k' : Fin P.sent.size) (hr : ride k' = none) (tb' : Rd) (ht : tb' = .main ∨ tb' = .mask)
    (r' j' : ℕ)
    (hne : ¬ (k' = n.1 ∧
      (seatC P ride n).1.place P.codes (shapeAt P k') (ride k') = (tb', r', j'))) :
    rdAt (rowsR P ride (fun _ _ _ => none) (put P ride (Pi.single n x)) k')
      ((shapeAt P k').mainDeg == 3) tb' r' j' = 0 := by
  rcases rd_cases P ride hf k' k'.isLt hr (put P ride (Pi.single n x)) tb' ht r' j' with
    ⟨y, hy, hp, he⟩ | h0
  · rw [he]
    refine coinNo_put_zero P ride _ k' y hy (inMsg_of_place _ _ _ y tb' r' j' ht hp) ?_
    intro n' hk' hs'
    have hn : n' ≠ n := fun e => hne (by
      subst e
      exact ⟨hk'.symm, by rw [hs']; exact hp⟩)
    rw [Pi.single_apply, if_neg hn]
  · exact h0

/-- If the job fits its place (sendFits), k < P.sent.size and ride k = none: at the entry at which a
slot y within the sizes is located, the sender's rows at no data have the coin with the slot's
number. -/
theorem rd_at_seat (hf : sendFits P ride = true) (k : ℕ) (hk : k < P.sent.size)
    (hr : ride k = none) (c : Cs (dueR P ride)) (y : Seat)
    (hy : y.ok P.codes (shapeAt P k) (ride k)) (tb : Rd) (r j : ℕ)
    (hp : y.place P.codes (shapeAt P k) (ride k) = (tb, r, j)) :
    rdAt (rowsR P ride (fun _ _ _ => none) c k) ((shapeAt P k).mainDeg == 3) tb r j =
      coinNo c (y.inE (shapeAt P k)) (y.no P ride k) := by
  rw [← seat_reads P ride _ c k y hf hk hr hy, read_place, hp]

/-- If the job fits its place (sendFits), ride k = none, PadFacts holds for (k, i, s) at the slot y,
and n is a name of oracle message k at y with the coordinate co: at no data and put (Pi.single n x),
coordinate s' of θ ^ t times the slot's entry is x if s' = s, else 0. -/
theorem rd_single_at (hf : sendFits P ride = true) (k : Fin P.sent.size) (hr : ride k = none)
    (i : ℕ) (s : Fin 3) (y : Seat) (co t : ℕ) (tb : Rd) (r j : ℕ)
    (F : PadFacts P ride k i s y co t tb r j) (n : CoinN P ride) (hn : n.1 = k)
    (hs : seatC P ride n = (y, co)) (x : GF) (s' : Fin 3) :
    crd s' (readE (thetaE t) *
      rdAt (rowsR P ride (fun _ _ _ => none) (put P ride (Pi.single n x)) k)
        ((shapeAt P k).mainDeg == 3) tb r j) = if s' = s then x else 0 := by
  rw [rd_at_seat hf k k.isLt hr _ y F.ok tb r j F.place]
  rcases F.kind with ⟨hE, ht, hco⟩ | ⟨hE, ht, hco⟩
  · rw [coinNo_put_e P ride _ k y F.ok F.inMsg hE (fun t' => if t' = s then x else 0) ?_, ht,
      readE_theta_zero, one_mul, crd_against]
    intro t' n' hn' hs'
    show (Pi.single n x : CoinN P ride → GF) n' = if t' = s then x else 0
    by_cases e : t' = s
    · have : n' = n := seatC_inj P ride n' n (hn'.trans hn.symm) (by rw [hs', hs, hco, e])
      rw [this, Pi.single_eq_same, if_pos e]
    · have hne : n' ≠ n := fun h => e (by
        subst h
        rw [hs] at hs'
        exact Fin.ext ((Prod.mk.inj hs').2.symm.trans hco))
      rw [Pi.single_apply, if_neg hne, if_neg e]
  · rw [coinNo_put_f P ride _ k y F.ok F.inMsg hE x ?_, ht, mul_comm, crd_cast_mul, crd_theta]
    · by_cases e : s' = s
      · rw [if_pos e, if_pos e, mul_one]
      · rw [if_neg e, if_neg e, mul_zero]
    · intro n' hn' hs'
      have : n' = n := seatC_inj P ride n' n (hn'.trans hn.symm) (by rw [hs', hs, hco])
      rw [this, Pi.single_eq_same]

/-- If the job fits its place (sendFits) and no seed's factor is 0, then for each answer (k, i, s)
of the instance some name n of oracle message k is such that the family with the value x at n and 0
elsewhere contributes x to that answer and 0 to every other answer. -/
theorem share_of (hf : sendFits P ride = true) (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0)
    (k : Fin P.sent.size) (i : Fin (shapeAt P k).answers) (s : Fin 3) :
    ∃ n : CoinN P ride, n.1 = k ∧
      ∀ (k' : Fin P.sent.size) (i' : Fin (shapeAt P k').answers) (s' : Fin 3)
      (x : GF), (sender P ride).wt (wOf P ds) (Pi.single n x : CoinN P ride → GF)
        ⟨k', (i', s')⟩ = if k'.val = k.val ∧ i'.val = i.val ∧ s' = s then x else 0 := by
  obtain ⟨y, co, t, tb, r, j, F⟩ := pad_facts hf k i s k.isLt i.isLt
  obtain ⟨n, hn, hs⟩ := exists_name P ride k y co F.ok F.inMsg F.co3 F.co0
  refine ⟨n, hn, fun k' i' s' x => ?_⟩
  have hr' : ride k' = none := fits_noRide P ride k' hf k'.isLt (by have := i'.isLt; omega)
  have hy : (seatC P ride n).1 = y := by rw [hs]
  rw [wt_eq P ride ds hf]
  by_cases hk : k' = k
  · subst hk
    rw [form_one P.codes (shapeAt P k') _ _ _ _ tb F.tbs r j F.rlt F.jlt
      fun tb' r' j' ht hne => rd_single hf n x k' hr' tb' ht r' j' fun h => hne (by
        rw [← h.2, hy, F.place]), F.part, F.idx,
      K1.Msg.weight_pad _ _ _ i'.val i.val t i.isLt F.tlt]
    by_cases hi : i.val = i'.val
    · have hb : readE (seedAt P ds i'.val).2 ≠ 0 :=
        hβ _ (seedAt_mem P ds k' i'.val k'.isLt i'.isLt)
      rw [if_pos hi, mul_assoc]
      unfold bInv
      rw [inv_mul_cancel_left₀ hb, rd_single_at hf k' hr' i s y co t tb r j F n hn hs x s']
      by_cases e : s' = s
      · rw [if_pos e, if_pos ⟨rfl, hi.symm, e⟩]
      · rw [if_neg e, if_neg fun h => e h.2.2]
    · rw [if_neg hi, zero_mul, mul_zero, crd_zero, if_neg fun h => hi h.2.1.symm]
  · rw [form_none P.codes (shapeAt P k') _ _ _ _
      (fun r' j' => rd_single hf n x k' hr' .main (.inl rfl) r' j' fun h => hk (h.1.trans hn))
      (fun r' j' => rd_single hf n x k' hr' .mask (.inr rfl) r' j' fun h => hk (h.1.trans hn)),
      mul_zero, crd_zero, if_neg fun h => hk (Fin.ext h.1)]

omit inst in
/-- Two names in AnsN with the same oracle message, the same answer and the same coordinate are
equal. -/
theorem ans_ext (a b : AnsN P) (h1 : a.1.val = b.1.val) (h2 : a.2.1.val = b.2.1.val)
    (h3 : a.2.2 = b.2.2) : a = b := by
  obtain ⟨k', i', s'⟩ := a
  obtain ⟨k, i, s⟩ := b
  have hk : k' = k := Fin.ext h1
  subst hk
  have hi : i' = i := Fin.ext h2
  subst hi
  have hs : s' = s := h3
  subst hs
  rfl

omit inst in
/-- Proof of Spec.padsOf, from share_of, with every factor β equal to 1. Of the statement's four
premises it uses two: the job fits its place, and no seed's factor is 0. -/
theorem padsOf : Spec.padsOf := by
  intro P ride ds hf _ _ hβ
  choose pad hpad using fun a : AnsN P =>
    share_of (inst := (sender P ride).decCn) ds hf hβ a.1 a.2.1 a.2.2
  refine ⟨⟨pad, fun _ => 1, fun _ => one_ne_zero, fun a b x => ?_⟩⟩
  have h : (sender P ride).wt (wOf P ds) (Pi.single (pad b) x) a = _ :=
    (hpad b).2 a.1 a.2.1 a.2.2 x
  rw [h, one_mul]
  by_cases e : a = b
  · subst e
    rw [if_pos ⟨rfl, rfl, rfl⟩, if_pos rfl]
  · rw [if_neg e, if_neg fun hh => e (ans_ext a b hh.1 hh.2.1 hh.2.2)]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.share_of
#print axioms OnBytes.SendSim.At.padsOf
