-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellLater.lean: THE SHARED
"SENDING" (the kind K1): A CELL THAT THE LIBRARY's ONE ACCESSOR READS OFF THE SCRIPT's WITNESS, AT
AN ARRAY THAT LIES IN ONE OF THE JOB's MESSAGES, IS THE VALUE THAT THE JOB's DATA ANSWERED WHEN THE
MESSAGE WAS SENT: AT ANY OPEN PART OF A STATE AT WHICH FIVE PUBLIC FACTS HOLD, AND AT ANY LIST OF
CHALLENGES NO SHORTER THAN THE ROUNDS IN FRONT OF THE MEMBER. One statement and its proof. No
definition.

  cell_later   under the kind's record K1Seated at the member b; one run's coins k, with the cut's
               equation hc; a valid input w; a list hd that is long enough (hN); the five facts on
               the part's statement and book at the message's number o; the layout's array a and its
               place rp; the row and place lie in the sender's shape, the message has a sample, off
               the pad; the job's data, at what had been heard in front of the member (hd.take ...),
               answers v:
               (dataQ own p (seatTab J.P.codes arr ms (L.Q.wit k w hd))).cell c₀.1 c₀.2 i cc =
               dataE (the message's main degree is 3) v

WHY. cell_behind and cell_is_val (Johnson/Desc/ProofFile/Honest/K1/Law/CellBehind.lean,
CellIsVal.lean) say this at the state behind the member's OWN step, where the five facts come of the
member's own yes. A later member's item (the tie at a segment's reads) reads cells of arrays that
were sent earlier (the first segment's opening). The thread is an invariant at one border and leads
to no earlier one; none is wanted: the record's two fields on the Script speak at every list of
challenges that is long enough. THE ROAD: cell_is_word (CellIsWord.lean) · words_at
(WordsAtFour.lean) · held_is_data (CellIsData.lean). cell_behind keeps its own proof: it is
not turned for this.

THE FIVE FACTS, PUBLIC, PAID BY NOBODY HERE: hcodes (the statement's codes are the plan's) · hx, hxs
(message o stands in the statement, with the plan's shape) · hpl (the book's place of o is the
member's message's seat) · hseat (the book seats o there).

An equation at one run's coins, every k; the cut never under a bare "there is"; no coin fixed; no
measure. Fields of R spent: msgs, pads (through words_at), sits. NOT UNDER "Stepped": whoever calls
it takes the cut from K1Seated.cut (Johnson/Desc/ProofFile/Honest/K1/SeatedLaw.lean), WHICH SPENDS
hasCoins BY NAME.

Limits. THE TIE (msgs, pads) IS A PREMISE. THE DATA STAND AT NOTHING SEEN AND AT own₀: that the
part's data at what it had seen are the same is the record's field heardOnly, which is not spent
here. No letters are given at which the premises hold together. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsVal
import Johnson.Desc.ProofFile.Honest.K1.Law.WordsAtFour

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
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

/-- **A cell of the Script's witness at an array of one of the job's
messages, at any part with the five facts and any list that is long enough.** The data stand at
nothing seen; that the part's data at what it had seen are the same: heardOnly, not spent here. IT
CARRIES dataE IN ITS END, AT ANY v AND EITHER DEGREE: the silent arm (dataE_silent) is not barred
here: whoever spends this law bars it. -/
theorem cell_later (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) (k : Coins Bk)
    (c : Cs (dueR J.P J.ride)) (hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (w : Local W₀ Rc Xi Tr) (hw : L.valid w) (hd : List Fmt.Drawn)
    (hN : L.thread.front + roundsTo L.bs b ≤ hd.length) (n : ℕ) (hn : n < J.P.sent.size)
    (own : List (ℕ × ℕ)) (hown : own.contains (seatAtMember L.bs b J.P n) = true) (p : K9.Part)
    (o : ℕ) (hcodes : p.d.st.codes = J.P.codes) (x : _) (hx : p.d.st.oracles[o]? = some x)
    (hxs : x.shape = shapeAt J.P n)
    (hpl : p.d.book.place[o]? = some (seatAtMember L.bs b J.P n))
    (hseat : Sound.seatBy Sound.noFirst p.d.book o = some (seatAtMember L.bs b J.P n))
    (c₀ : ℕ × String) (a : ReqArray) (i cc : ℕ) (rp : ℕ × ℕ)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some o)
    (hok : laidMatrixOk a (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true)
    (hrp : laidAt a i cc = some rp) (hr : rp.1 < (shapeAt J.P n).mainRows)
    (hj : rp.2 < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (hans : (shapeAt J.P n).answers ≠ 0)
    (hpad : rp ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n)) {v : GF ⊕ GE}
    (hv : J.data (wit w)
      { heard := hd.take (L.thread.front + roundsTo L.bs b), own := own₀, seen := .bare [] } n rp.1
      rp.2 = some v) :
    (dataQ own p (seatTab J.P.codes arr ms (L.Q.wit k w hd))).cell c₀.1 c₀.2 i cc =
      dataE ((shapeAt J.P n).mainDeg == 3) v := by
  have hbits : p.d.st.rowBits o .main = K1.clog (shapeAt J.P n).mainRows := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows Part.main) = _
    rw [hxs]
    rfl
  have hreal : tableIndex (p.d.st.rowBits o .main) rp % 2 ^ p.d.st.rowBits o .main <
      realRows p.d.st o .main := by
    rw [hbits]
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
      (L.Q.wit k w hd) o =
      (L.Q.wit k w hd).tab p.d.st.codes (shapeAt J.P n)
        (arr (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2)
        (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2 := by
    unfold Sound.tabAt
    rw [hseat, hx]
    simp only [hxs]
  rw [cell_is_word J.P.codes arr ms own p _ c₀ a o i cc rp (shapeAt J.P n)
    (seatAtMember L.bs b J.P n) y' ha ho hok hrp hT hpl hown hy' hsh hcodes hreal, hbits,
    words_at R k c hc w hw hd hN p.d.st p.d.book o n hn hcodes x hx hxs hseat (fun _ _ _ => 0)
      J.first .main _,
    held_is_data J own₀ c (wit w) _ _ n hn rp hr hj hans hpad, hv]
  cases h3 : ((shapeAt J.P n).mainDeg == 3) <;> cases v <;> simp [dataE]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cell_later
