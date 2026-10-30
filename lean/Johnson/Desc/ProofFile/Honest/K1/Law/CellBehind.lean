-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellBehind.lean:
THE SHARED "SENDING" (the kind K1) AT A MEMBER OF THE FIRST CHAIN: BEHIND THE MEMBER's STEP,
A CELL THAT THE LIBRARY's ONE ACCESSOR READS OFF THE THREAD's OWN WITNESS, AT AN ARRAY THAT LIES IN
ONE OF THE MEMBER's OWN MESSAGES, IS WHAT THE JOB's DATA SAYS AT THE PLACE AT WHICH THE LAYOUT LAYS
IT. One statement and its proof. No definition.

  cell_behind   under the kind's record K1Seated ("R"), the pair, the draws' fit and the member's
                step, at every continuation of the challenges: (dataQ own p (seatTab J.P.codes arr
                ms v)).cell at the element (i, cc) of an array a whose message is the job's number
                n: the job's data at (n, rp.1, rp.2), rp := the layout's place of (i, cc), read in
                the extension field

THE JOIN: cell_is_word (Johnson/Desc/ProofFile/Honest/K1/Law/CellIsWord.lean) · words_behind
(Johnson/Desc/ProofFile/Honest/K1/Law/ExchangeAtPins.lean) · held_is_data
(Johnson/Desc/ProofFile/Honest/K1/Law/CellIsData.lean). OF cell_is_word's ELEVEN PREMISES SIX ARE
PAID HERE, off R and the member's own accept: the witness's table at the message (hT), the book's
place (hq), the member of ms at the seat and its shape (hy, hsh: R.sits), the codes (hcs), the real
rows (hreal); and the equation of bits between the statement and the plan.

WHAT IS LEFT AS PREMISES. On the state behind (public): its open part p; the layout has the array
(ha); the frame finds its message as the statement's number of the job's message n (ho); the
programs' test on the array's layout at the statement's bits (hok); the seat lies in own (hown); two
on the verifier's book, as words_behind has them (hFits, hNum). On the layout: rp (hrp). On rp: the
four of held_is_data (hr, hj, hans, hpad).

It speaks at the state RIGHT BEHIND THE SENDING MEMBER. A message that was sent members earlier
wants the riding besides (wordsBy_congr, Johnson/Desc/Sound/WordsAt.lean).

Limits. A law under "Stepped": it has the cut from the frame, and holds of nothing at a book that
does not cover the part's count. R's fields on the Script (msgs, pads) and on the book's count are
spent, through words_behind. R has members at a made-up chain alone. No state is given at which the
premises hold together. An equation at each value of the run's coins: the right side does not name
them. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsWord
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsData
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import Johnson.Desc.First.Look.K3MaskOkTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem dataQ seatTab seatOf)
open VerifiableInference.Desc.First.Att.P (tableIndex)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt split_index)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **Behind the member's step a cell of the
thread's own witness, at an array of the member's own message number n, is the job's data.** -/
theorem cell_behind (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (c : Cs (dueR J.P J.ride)) (hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (n : ℕ) (hn : n < J.P.sent.size) (ds' : List Fmt.Drawn) (own : List (ℕ × ℕ))
    (hown : own.contains (seatAtMember L.bs b J.P n) = true) (p : K9.Part)
    (hp : K9.segAt? s' = some p) (c₀ : ℕ × String) (a : ReqArray) (i cc : ℕ) (rp : ℕ × ℕ)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n))
    (hok : laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
      (p.d.st.placeBits (s.st.oracles.size + n) .main) = true)
    (hrp : laidAt a i cc = some rp) (hr : rp.1 < (shapeAt J.P n).mainRows)
    (hj : rp.2 < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (hans : (shapeAt J.P n).answers ≠ 0)
    (hpad : rp ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n)) :
    (dataQ own p (seatTab J.P.codes arr ms
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).cell c₀.1 c₀.2 i cc =
      if (shapeAt J.P n).mainDeg == 3 then
        match J.data (wit m.st.input) { heard := m.st.heard, own := own₀, seen := .bare [] } n rp.1
          rp.2 with
        | some (.inr x) => x
        | some (.inl x) => algebraMap GF GE x
        | none => 0
      else
        algebraMap GF GE (match J.data (wit m.st.input)
          { heard := m.st.heard, own := own₀, seen := .bare [] } n rp.1 rp.2 with
        | some (.inl x) => x
        | _ => 0) := by
  obtain ⟨-, -, est, ebk⟩ := VerifiableInference.OnPublicFiles.segAt_parts hp
  obtain ⟨c₁, r₁, r₂, gs, -, hdec, -, -, -, -, -⟩ := step_at_block R Said hA hd hS
  have hB := R.books _ _ _ _ _ hdec
  obtain ⟨hcodes, x, hx, hxs, -⟩ := msg_at_block J.P R.isSend hdec hB n hn
  have hpl := place_behind R Said hA hd hS n hn
  have hseat := seatBy_behind R Said hA hd hS hFits hNum n hn
  have hbits : p.d.st.rowBits (s.st.oracles.size + n) .main =
      K1.clog (shapeAt J.P n).mainRows := by
    rw [est]
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows Part.main) = _
    rw [hxs]
    rfl
  have hreal : tableIndex (p.d.st.rowBits (s.st.oracles.size + n) .main) rp %
      2 ^ p.d.st.rowBits (s.st.oracles.size + n) .main <
      realRows p.d.st (s.st.oracles.size + n) .main := by
    rw [hbits, est]
    unfold realRows tableIndex
    rw [hx]
    show _ < x.shape.rows Part.main
    rw [hxs, Nat.mul_comm (2 ^ K1.clog (shapeAt J.P n).mainRows) rp.2,
      (split_index rp.1 rp.2 _ hr).1]
    exact hr
  obtain ⟨⟨x₀, hx₀, hs₀⟩, hall⟩ := R.sits n hn hans
  have hsome : (ms.find? fun z => decide (seatOf z = seatAtMember L.bs b J.P n)).isSome = true :=
    List.find?_isSome.2 ⟨x₀, hx₀, decide_eq_true hs₀⟩
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hsome
  have hy's : seatOf y' = seatAtMember L.bs b J.P n := of_decide_eq_true
    (List.find?_some (p := fun z : Mem => decide (seatOf z = seatAtMember L.bs b J.P n)) hy')
  have hsh := hall y' (List.mem_of_find?_eq_some hy') hy's
  have hT : Sound.tabAt p.d.st.codes arr (Sound.seatBy Sound.noFirst p.d.book) p.d.st
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) (s.st.oracles.size + n) =
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')).tab p.d.st.codes (shapeAt J.P n)
        (arr (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2)
        (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2 := by
    rw [est, ebk]
    unfold Sound.tabAt
    rw [hseat, hx]
    simp only [hxs]
  rw [cell_is_word J.P.codes arr ms own p _ c₀ a _ i cc rp (shapeAt J.P n)
    (seatAtMember L.bs b J.P n) y' ha ho hok hrp hT (by rw [ebk]; exact hpl) hown hy' hsh
    (by rw [est]; exact hcodes) hreal, hbits, est, ebk,
    words_behind R Said hA hd hS hFits hNum c hc n hn (fun _ _ _ => 0) ds' .main _,
    first_at_border L Said hA R.placeAt R.firstNo]
  exact held_is_data J own₀ c (wit m.st.input) m.st.heard _ n hn rp hr hj hans hpad

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cell_behind
