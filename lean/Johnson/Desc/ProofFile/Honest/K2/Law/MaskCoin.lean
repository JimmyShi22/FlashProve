-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MaskCoin.lean: WHICH COIN STANDS AT WHICH ENTRY OF A MESSAGE's
MASK ROWS, in the sending as the code switch's part calls it: for a message that is no fold's fresh
mask. The definitions that the statements speak of, statements and proofs, on `messageRows` and
`rowsAll` (Honest/K2/Sending.lean) and on `dueBefore` and `sendingDue` (Honest/K2/Part.lean).

  `ownBase`      where, among one message's own coins, the entries of its mask rows begin
  `maskLength`   how many entries the mask rows of message number n have
  `maskBase`     where, among the sending's coins of the extension field, these entries begin
  `maskEntry`    the entry with the format's number ν = place * m + row (m mask rows), as `rowsAll`
                 lays it, as the program's element; the program's zero where `rowsAll` refuses
  `messageRows_reads`   what a message's laying that returns has read, and its mask rows
  `messageRows_mask`    in one message: entry i of mask row r is the stretch's coin number
                 e₀ + (i * m + r)
  `messageRows_again`, `rowsAll_again`   WHETHER THE LAYING REFUSES HANGS ON NO COIN, on no main row
                 and on no fresh mask's table
  `rowsAll_at`   message number n of a sending is laid of the cut at `dueBefore`
  `rowsAll_mask`   in a sending: the entry with the number ν is the sending's coin number
                 `maskBase` + ν
  `eAt_coinsE`   a coin, read by number, in the list of the coins as the program's elements
  `maskEntry_coin`, `maskEntry_in`   THE TWO SENTENCES AT A SENDING: at all coins and every ν below
                 `maskLength`: `maskEntry` at ν is member number `maskBase` + ν of that list; and
                 that number lies below the count
  `switchPart_takes`, `foldAt_switchFresh`, `switch_maskEntry_coin`, `switch_maskEntry_in`   the
                 same AT THE SWITCH's PART: its own count; every message but the last

THE PREMISE "ONE RUN". `rowsAll` can refuse, and there `maskEntry` is zero while the coin need not
be. So the two sentences ask that at SOME table, main rows and coins `rowsAll` returns: one run,
which can be evaluated at coins of zeros. `rowsAll_again` carries it to all.
Honest/K2/Law/MaskFits.lean pays it under the shared sending's public test.

Limits. The sentences are on `rowsAll`: the rows that `coreSender` encodes. `switchPart` takes its
sender as a letter: of another sender nothing is said. THEY HOLD FOR ALL ENTRIES OF THE MASK ROWS,
the places of an out-of-domain sample's pad among them. ν is the format's number of an entry: that a
slot's number in the verifier's statement is that number is not said here. WHICH message of a
switch bears the next segment's mask rows at a place of the plan is not said here: n is a letter.
What is WRITTEN where: no sentence on what a mask row or a coin is for. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Sending
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (Sizes zeroG)
open Johnson.Prover.Send (Rows)
open Reads

/-! ## 1 What the statements speak of -/

/-- Where, among ONE message's own coins of the extension field, the entries of its mask rows begin,
at a message that has a mask row: behind the main rows' tails where these lie over that field, else
at 0. (At such a message the pad lies in no main row.) -/
def ownBase (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Nat :=
  if s.mainDeg == 3 then s.mainRows * (codes.base.getD s.code default).r else 0

/-- How many entries the mask rows of message number n of a sending have: rows times the mask
code's message length. -/
def maskLength (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (n : Nat) : Nat :=
  (sent.getD n default).shape.maskRows *
    (codes.mask.getD (sent.getD n default).shape.maskCode default).ell

/-- Where, among a sending's coins of the extension field, the entries of message number n's mask
rows begin. -/
def maskBase (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n : Nat) : Nat :=
  (dueBefore codes sent fresh n).e + ownBase codes (sent.getD n default).shape

/-- **The entry with the format's number ν of message number n's mask rows**, as `rowsAll` lays it
of the sending's coins: row ν % m at place ν / m, m the message's mask rows; brought to the
program's element as `coinsE` brings a coin. The program's zero where `rowsAll` refuses. -/
def maskEntry (table : FreshTable) (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (data : Nat → Nat → Nat → Cb.Gl.E) (n : Nat)
    (c : Cs (sendingDue codes sent fresh)) (ν : Nat) : OnBytes.E :=
  match rowsAll table codes sent fresh data c with
  | .ok V =>
    OnBytes.E.ofTriple (OnBytes.Slice.ofE
      ((V n).mask (ν % (sent.getD n default).shape.maskRows)
        (ν / (sent.getD n default).shape.maskRows)))
  | .error _ => OnBytes.zeroE

/-! ## 2 One message -/

/-- **What a laying that returns has read of the mask rows' entries, and how it lays them.** At a
message that has a mask row and is no fresh mask. -/
theorem messageRows_reads {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    {fold : Option Nat} {data : Nat → Nat → Cb.Gl.E} {k : Stretch} {R : Rows} (hf : fold = none)
    (hm : s.maskRows ≠ 0) (h : messageRows table codes s fold data k = .ok R) :
    ∃ A : Array Cb.Gl.E,
      k.es (ownBase codes s) (s.maskRows * (codes.mask.getD s.maskCode default).ell) = .ok A ∧
      R.mask = fun r i =>
        if !(decide (r < s.maskRows) && decide (i < (codes.mask.getD s.maskCode default).ell))
        then zeroG else A.getD (i * s.maskRows + r) zeroG := by
  subst hf
  have hm' : (s.maskRows != 0) = true := bne_iff_ne.2 hm
  unfold messageRows at h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  simp only [if_pos hm', List.length_nil, Nat.add_zero] at hA
  exact ⟨A, hA, rfl⟩

/-- **In one message: entry i of mask row r is the stretch's coin number e₀ + (i * m + r).** -/
theorem messageRows_mask {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    {fold : Option Nat} {data : Nat → Nat → Cb.Gl.E} {k : Stretch} {R : Rows} (hf : fold = none)
    (h : messageRows table codes s fold data k = .ok R) {r i : Nat} (hr : r < s.maskRows)
    (hi : i < (codes.mask.getD s.maskCode default).ell) :
    k.coins.eAt (ownBase codes s + (i * s.maskRows + r)) = .ok (R.mask r i) := by
  obtain ⟨A, hA, hR⟩ :=
    messageRows_reads hf (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le r) hr)) h
  have hlt : i * s.maskRows + r < s.maskRows * (codes.mask.getD s.maskCode default).ell :=
    calc i * s.maskRows + r < i * s.maskRows + s.maskRows := Nat.add_lt_add_left hr _
      _ = (i + 1) * s.maskRows := (Nat.succ_mul i s.maskRows).symm
      _ ≤ (codes.mask.getD s.maskCode default).ell * s.maskRows := Nat.mul_le_mul_right _ hi
      _ = s.maskRows * (codes.mask.getD s.maskCode default).ell := Nat.mul_comm _ _
  have hv : R.mask r i = A.getD (i * s.maskRows + r) zeroG := by
    rw [hR]
    show (if (!(decide (r < s.maskRows) &&
        decide (i < (codes.mask.getD s.maskCode default).ell))) = true
      then zeroG else A.getD (i * s.maskRows + r) zeroG) = _
    rw [decide_eq_true hr, decide_eq_true hi]
    rfl
  rw [hv]
  exact es_at hA hlt zeroG

/-- **Whether a message's laying refuses hangs on no coin, on no main row and on no table.** -/
theorem messageRows_again {table table' : FreshTable} {codes : OnBytes.Codes}
    {s : OnBytes.OracleShape} {fold : Option Nat} {data data' : Nat → Nat → Cb.Gl.E}
    {k k' : Stretch} (hd : k'.due = k.due) {R : Rows}
    (h : messageRows table codes s fold data k = .ok R) :
    ∃ R', messageRows table' codes s fold data' k' = .ok R' := by
  cases hR : messageRows table' codes s fold data' k' with
  | ok R' => exact ⟨R', rfl⟩
  | error e =>
    exfalso
    unfold messageRows at h hR
    rcases ite_eq h with ⟨_, h⟩ | ⟨h1, h⟩
    · cases h
    rcases ite_eq hR with ⟨q, _⟩ | ⟨_, hR⟩
    · exact h1 q
    obtain ⟨_, _, h⟩ := bind_ok h
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · cases hx
    rcases ite_eq h with ⟨_, h⟩ | ⟨h2, h⟩
    · cases h
    rcases ite_eq hR with ⟨q, _⟩ | ⟨_, hR⟩
    · exact h2 q
    obtain ⟨_, _, h⟩ := bind_ok h
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · cases hx
    obtain ⟨_, hF, h⟩ := bind_ok h
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, hF'⟩ := fs_again hd hF
      cases hF'.symm.trans hx
    obtain ⟨_, hE, h⟩ := bind_ok h
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, hE'⟩ := es_again hd hE
      cases hE'.symm.trans hx
    obtain ⟨_, hM, h⟩ := bind_ok h
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, hM'⟩ := es_again hd hM
      cases hM'.symm.trans hx
    obtain ⟨_, hT, h⟩ := bind_ok h
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, hT'⟩ := es_again hd hT
      cases hT'.symm.trans hx
    rcases ite_eq h with ⟨_, h⟩ | ⟨h3, _⟩
    · cases h
    rcases ite_eq hR with ⟨q, _⟩ | ⟨_, hR⟩
    · rw [hd] at q
      exact h3 q
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · cases hx
    cases hR

/-! ## 3 A sending -/

/-- **Message number n of a sending is laid of the cut at `dueBefore`.** -/
theorem rowsAll_at {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (h : rowsAll table codes sent fresh data c = .ok V) {n : Nat} (hn : n < sent.size) :
    ∃ c' : Cs (messageDue codes (sent.getD n default).shape (foldAt fresh n)),
      c.cut (dueBefore codes sent fresh n)
        (messageDue codes (sent.getD n default).shape (foldAt fresh n)) = some c' ∧
      messageRows table codes (sent.getD n default).shape (foldAt fresh n) (data n) ⟨_, c'⟩ =
        .ok (V n) := by
  unfold rowsAll at h
  split at h
  · cases h
  obtain ⟨l, hl, rfl⟩ := map_ok h
  obtain ⟨R, hR, hg⟩ := mapM_at _ _ _ hl n n (range_at hn)
  obtain ⟨k, hk, hm⟩ := bind_ok' hg
  obtain ⟨c', hc', rfl⟩ := stretch_cut_ok hk
  refine ⟨c', hc', ?_⟩
  show _ = Except.ok (l.getD n zeroMessage)
  rw [List.getD_eq_getElem?_getD, hR, Option.getD_some]
  exact hm

/-- **Whether a sending's laying refuses hangs on no coin, on no main row and on no table.** -/
theorem rowsAll_again {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (h : rowsAll table codes sent fresh data c = .ok V) (table' : FreshTable)
    (data' : Nat → Nat → Nat → Cb.Gl.E) (c₂ : Cs (sendingDue codes sent fresh)) :
    ∃ V', rowsAll table' codes sent fresh data' c₂ = .ok V' := by
  unfold rowsAll at h
  split at h
  · cases h
  rename_i hs
  obtain ⟨l, hl, _⟩ := map_ok h
  obtain ⟨l', hl'⟩ := mapM_again _
    (fun k => ((Stretch.of c₂).cut (dueBefore codes sent fresh k)
      (messageDue codes (sent.getD k default).shape (foldAt fresh k))).bind
      (messageRows table' codes (sent.getD k default).shape (foldAt fresh k) (data' k)))
    _ _ hl fun k R _ hg => by
      obtain ⟨q, hq, hm⟩ := bind_ok' hg
      obtain ⟨c', hc', rfl⟩ := stretch_cut_ok hq
      obtain ⟨c₂', hc₂'⟩ := cut_again hc' c₂
      obtain ⟨R', hR'⟩ := messageRows_again (table' := table') (data' := data' k)
        (k := ⟨_, c'⟩) (k' := ⟨_, c₂'⟩) rfl hm
      refine ⟨R', ?_⟩
      show ((Stretch.of c₂).cut _ _).bind _ = _
      rw [stretch_cut_of hc₂']
      exact hR'
  refine ⟨fun k => l'.getD k zeroMessage, ?_⟩
  unfold rowsAll
  exact (if_neg hs).trans (congrArg (Except.map fun l k => l.getD k zeroMessage) hl')

/-- **In a sending: the entry with the format's number ν of message number n's mask rows is the
sending's coin number `maskBase` + ν.** -/
theorem rowsAll_mask {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (h : rowsAll table codes sent fresh data c = .ok V) {n : Nat} (hn : n < sent.size)
    (hf : foldAt fresh n = none) {ν : Nat} (hν : ν < maskLength codes sent n) :
    c.eAt (maskBase codes sent fresh n + ν) =
      .ok ((V n).mask (ν % (sent.getD n default).shape.maskRows)
        (ν / (sent.getD n default).shape.maskRows)) := by
  obtain ⟨c', hc', hm⟩ := rowsAll_at h hn
  have h0 : 0 < (sent.getD n default).shape.maskRows := by
    rcases Nat.eq_zero_or_pos (sent.getD n default).shape.maskRows with e | e
    · unfold maskLength at hν
      rw [e, Nat.zero_mul] at hν
      exact absurd hν (Nat.not_lt_zero _)
    · exact e
  have hx := cut_eAt hc' (messageRows_mask hf hm (Nat.mod_lt ν h0) (Nat.div_lt_of_lt_mul hν))
  rw [Nat.div_add_mod', ← Nat.add_assoc] at hx
  exact hx

/-! ## 4 The two sentences -/

/-- A coin that a read by number returns is the member of that number in the list of the coins as
the program's elements; the number lies below the count. -/
theorem eAt_coinsE {d : Due} {c : Cs d} {j : Nat} {x : Cb.Gl.E} (h : c.eAt j = .ok x) :
    j < d.e ∧ (coinsE c).getD j OnBytes.zeroE = OnBytes.E.ofTriple (OnBytes.Slice.ofE x) := by
  obtain ⟨hj, rfl⟩ := eAt_ok h
  refine ⟨hj, ?_⟩
  unfold coinsE
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj, Option.getD_some]

/-- **The sender lays its own coin.** At a sending whose laying returns in one run; at a message of
it that is no fold's fresh mask; at all coins, and at whatever main rows and table: the entry with
the format's number ν, below the mask rows' count of entries, is the coin number `maskBase` + ν. -/
theorem maskEntry_coin {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hone : ∃ table₀ data₀ c₀ V₀, rowsAll table₀ codes sent fresh data₀ c₀ = .ok V₀) {n : Nat}
    (hn : n < sent.size) (hf : foldAt fresh n = none) (table : FreshTable)
    (data : Nat → Nat → Nat → Cb.Gl.E) :
    ∀ (cs : Cs (sendingDue codes sent fresh)) (ν : Nat), ν < maskLength codes sent n →
      maskEntry table codes sent fresh data n cs ν =
        (coinsE cs).getD (maskBase codes sent fresh n + ν) OnBytes.zeroE := by
  intro cs ν hν
  obtain ⟨_, _, _, _, h₀⟩ := hone
  obtain ⟨V, hV⟩ := rowsAll_again h₀ table data cs
  rw [(eAt_coinsE (rowsAll_mask hV hn hf hν)).2]
  unfold maskEntry
  split
  · rename_i V' e
    obtain rfl := Except.ok.inj (hV.symm.trans e)
    rfl
  · rename_i e
    cases hV.symm.trans e

/-- **These numbers lie below the sending's count.** -/
theorem maskEntry_in {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hone : ∃ table₀ data₀ c₀ V₀, rowsAll table₀ codes sent fresh data₀ c₀ = .ok V₀) {n : Nat}
    (hn : n < sent.size) (hf : foldAt fresh n = none) :
    ∀ ν : Nat, ν < maskLength codes sent n →
      maskBase codes sent fresh n + ν < (sendingDue codes sent fresh).e := by
  intro ν hν
  obtain ⟨_, _, _, _, h₀⟩ := hone
  exact (eAt_coinsE (rowsAll_mask h₀ hn hf hν)).1

/-! ## 5 At the switch's part -/

/-- The part's own count is the count of the switch's sending, at every sender. -/
theorem switchPart_takes (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) :
    (switchPart Sd Z others k carries).takes =
      sendingDue Z.codes (switchSent Z others) (switchFresh Z others k) :=
  rfl

/-- Every message of a switch but the last is no fold's fresh mask. -/
theorem foldAt_switchFresh (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat) {n : Nat}
    (hl : n ≠ (switchSent Z others).size - 1) : foldAt (switchFresh Z others k) n = none := by
  show (if ((switchSent Z others).size - 1 == n) = true then some k else none) = none
  rw [if_neg fun e => hl (beq_iff_eq.1 e).symm]

/-- **The sender lays its own coin, at the switch's part.** cs: the part's own coins. Of the part
its count alone is read, which hangs on no sender: the sentence is on `rowsAll`, not on Sd. -/
theorem switch_maskEntry_coin (Sd : Sender) {Z : Sizes} {others : Array OnBytes.OracleNotice}
    {k : Nat} (carries : List (String × Due))
    (hone : ∃ table₀ data₀ c₀ V₀,
      rowsAll table₀ Z.codes (switchSent Z others) (switchFresh Z others k) data₀ c₀ = .ok V₀)
    {n : Nat} (hn : n < (switchSent Z others).size) (hl : n ≠ (switchSent Z others).size - 1)
    (table : FreshTable) (data : Nat → Nat → Nat → Cb.Gl.E) :
    ∀ (cs : Cs (switchPart Sd Z others k carries).takes) (ν : Nat),
      ν < maskLength Z.codes (switchSent Z others) n →
      maskEntry table Z.codes (switchSent Z others) (switchFresh Z others k) data n cs ν =
        (coinsE cs).getD (maskBase Z.codes (switchSent Z others) (switchFresh Z others k) n + ν)
          OnBytes.zeroE :=
  maskEntry_coin hone hn (foldAt_switchFresh Z others k hl) table data

/-- **These numbers lie below the part's own count.** Of the part its count alone is read. -/
theorem switch_maskEntry_in (Sd : Sender) {Z : Sizes} {others : Array OnBytes.OracleNotice}
    {k : Nat} (carries : List (String × Due))
    (hone : ∃ table₀ data₀ c₀ V₀,
      rowsAll table₀ Z.codes (switchSent Z others) (switchFresh Z others k) data₀ c₀ = .ok V₀)
    {n : Nat} (hn : n < (switchSent Z others).size) (hl : n ≠ (switchSent Z others).size - 1) :
    ∀ ν : Nat, ν < maskLength Z.codes (switchSent Z others) n →
      maskBase Z.codes (switchSent Z others) (switchFresh Z others k) n + ν <
        (switchPart Sd Z others k carries).takes.e :=
  maskEntry_in hone hn (foldAt_switchFresh Z others k hl)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.messageRows_reads
#print axioms ProofFile.Honest.K2.messageRows_mask
#print axioms ProofFile.Honest.K2.messageRows_again
#print axioms ProofFile.Honest.K2.rowsAll_at
#print axioms ProofFile.Honest.K2.rowsAll_again
#print axioms ProofFile.Honest.K2.rowsAll_mask
#print axioms ProofFile.Honest.K2.eAt_coinsE
#print axioms ProofFile.Honest.K2.maskEntry_coin
#print axioms ProofFile.Honest.K2.maskEntry_in
#print axioms ProofFile.Honest.K2.switchPart_takes
#print axioms ProofFile.Honest.K2.foldAt_switchFresh
#print axioms ProofFile.Honest.K2.switch_maskEntry_coin
#print axioms ProofFile.Honest.K2.switch_maskEntry_in
#print axioms ProofFile.Honest.K2.ownBase
#print axioms ProofFile.Honest.K2.maskLength
#print axioms ProofFile.Honest.K2.maskBase
#print axioms ProofFile.Honest.K2.maskEntry
