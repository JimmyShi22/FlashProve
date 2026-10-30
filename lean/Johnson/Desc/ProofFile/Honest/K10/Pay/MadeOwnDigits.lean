-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnDigits.lean: the digits' data (`K1.digitsFill`, Honest/K1/LotFill.lean: the arrays "BZ" and "ZZ" of a segment's moment 2)
are ready at every list of challenges that fits the declared rounds and reaches the sending, where the public data fit.
General in the public part, the ground and the parameter mats: no head, no thread.

  `DigitsFit Z G mats a`   THE NAMED PREMISE, on public data alone, at an address a: a is the address of a seat s of "BZ" · the
                     segment has its public data b · the layout's and the message's own tests · `bzFitsOne` at s · the
                     sampling round is the last in front of the sending · it is declared to sample as many entries as the
                     digits read · that count is the declared round's own · for "ZZ": the plan's state tl, mats' length, the
                     round's number in the list of the rounds "RNG", the count again, and `inside`
  `trits_of_fit`      what a challenge that fits a declared round has: the declared count of sampled entries, each -1, 0 or 1
  `bz_ready`, `zz_ready`   the two fillings' field `ready`, at a list that has such a challenge at the sampling round's number
  **`digits_ready`**   `readyAt` of the joined filling

A challenge's value is not read: of a challenge the two tests read the count of its sampled entries and that each is -1, 0
or 1, which the frame's test of form `drawFit` (Honest/Frame.lean) holds.

Limits. `DigitsFit` is a premise: shown of no public data here. Nothing on what the data hold.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotFill
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes.HonestTrace (Seat BzAt seatsOf seatAt pairOf heardOf bzAtOf bzRows bzFitsOne)
open OnBytes.Model (HTailF2)
open ProofFile.Honest.K2 (roundNumbers drawnAt)
open ProofFile.Honest.K8 (zzDataAt zzVals zzPubOf bearsZz columnsOf)

/-- **The named premise on public data**, at an address. -/
def DigitsFit (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) (a : MsgAddr) :
    Prop :=
  ∃ (s : Seat) (b : BzAt) (tl : HTailF2) (d : Fmt.DeclaredRound),
    seatAt (seatsOf Z G "BZ") a = some s ∧ bzAtOf Z G mats s.seg = some b ∧
    layFits G.first.shape G.first.layout = true ∧
    msgFits G.first.codes G.first.shape G.first.layout s.seg s.array.message = true ∧
    bzFitsOne (bzAtOf Z G mats) s = true ∧
    b.rng + 1 = s.heard ∧ b.wanted = d.entry.trits ∧ Z.D.1[b.rng]? = some d ∧
    (G.built[s.seg]?).map (·.tl) = some tl ∧ (mats s.seg).length = tl.NM ∧
    (roundNumbers Z.D.1 "RNG")[s.seg]? = some b.rng ∧ columnsOf tl * tl.tau = d.entry.trits ∧
    (zzVals (zzPubOf G Z.D.1 mats)).inside G.first.layout s.seg = true

/-- What a challenge that fits a declared round has of sampled entries. -/
theorem trits_of_fit {d : Fmt.DeclaredRound} {R : Fmt.Drawn} (h : drawFit d R = true) :
    R.trits.length = d.entry.trits ∧
      (R.trits.all fun t => t == -1 || t == 0 || t == 1) = true := by
  unfold drawFit at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, h5⟩, -⟩, -⟩, -⟩ := h
  exact ⟨beq_iff_eq.1 h3, h5⟩

section
variable {Z : Pub} {G : Ground} {mats : Nat → List (Nat × String × Nat)} {a : MsgAddr}
  {s : Seat} {b : BzAt} {tl : HTailF2} {d : Fmt.DeclaredRound}

theorem bz_heardAt (hs : seatAt (seatsOf Z G "BZ") a = some s) :
    (bzRows Z G mats).heardAt a = s.heard := by
  show heardOf (seatsOf Z G "BZ") a = s.heard
  unfold heardOf
  rw [hs]
  rfl

/-- The field `ready` of the filling of "BZ". -/
theorem bz_ready (hs : seatAt (seatsOf Z G "BZ") a = some s) (hb : bzAtOf Z G mats s.seg = some b)
    (hlay : layFits G.first.shape G.first.layout = true)
    (hmsg : msgFits G.first.codes G.first.shape G.first.layout s.seg s.array.message = true)
    (hone : bzFitsOne (bzAtOf Z G mats) s = true) (hw : b.wanted = d.entry.trits)
    {hd : List Fmt.Drawn} {R : Fmt.Drawn} (hR : hd[b.rng]? = some R) (hf : drawFit d R = true) :
    (bzRows Z G mats).ready hd a = true := by
  obtain ⟨t1, t2⟩ := trits_of_fit hf
  have hp : pairOf (seatsOf Z G "BZ") a = some (s.seg, s.array.message) := by
    unfold pairOf
    rw [hs]
    rfl
  have hfind : ((seatsOf Z G "BZ").map fun s => (s.addr, bzFitsOne (bzAtOf Z G mats) s)).find?
      (fun x => x.1 == a) = some (s.addr, bzFitsOne (bzAtOf Z G mats) s) := by
    rw [List.find?_map]
    have hs' : (seatsOf Z G "BZ").find? (fun s => s.addr == a) = some s := hs
    show Option.map _ ((seatsOf Z G "BZ").find? fun s => s.addr == a) = _
    rw [hs']
    rfl
  have hrd : b.ready hd = true := by
    unfold BzAt.ready BzAt.sampled
    rw [hR]
    simp only [Option.map_some, Option.any_some, Bool.and_eq_true, beq_iff_eq]
    exact ⟨t1.trans hw.symm, t2⟩
  show (((pairOf (seatsOf Z G "BZ") a).all fun x =>
      layFits G.first.shape G.first.layout &&
        msgFits G.first.codes G.first.shape G.first.layout x.1 x.2 &&
        (bzAtOf Z G mats x.1).any fun b => b.ready hd) &&
    (((seatsOf Z G "BZ").map fun s => (s.addr, bzFitsOne (bzAtOf Z G mats) s)).find?
      fun x => x.1 == a).all (·.2)) = true
  rw [hp, hfind]
  simp only [Option.all_some, hlay, hmsg, hb, Option.any_some, hrd, hone, Bool.and_self]

/-- How many challenges the filling of "ZZ" says have been heard: none, or up to the sampling
round. -/
theorem zz_heardAt (hs : seatAt (seatsOf Z G "BZ") a = some s)
    (hrng : (roundNumbers Z.D.1 "RNG")[s.seg]? = some b.rng) :
    ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a = b.rng + 1 ∧
        bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a = some (s.seg, s.array.message)) ∨
      ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a = 0 ∧
        bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a = none) := by
  have hp : pairOf (seatsOf Z G "BZ") a = some (s.seg, s.array.message) := by
    unfold pairOf
    rw [hs]
    rfl
  have hH : (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a =
      (match (bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a).bind fun x =>
          (roundNumbers Z.D.1 "RNG")[x.1]? with
        | some n => n + 1
        | none => 0) := rfl
  cases hz : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a with
  | none =>
    refine Or.inr ⟨?_, rfl⟩
    rw [hH, hz]
    rfl
  | some x =>
    have hx : x = (s.seg, s.array.message) := by
      unfold bearsZz at hz
      rw [hp] at hz
      exact Option.some.inj (Option.filter_eq_some_iff.1 hz).1.symm
    subst hx
    refine Or.inl ⟨?_, rfl⟩
    rw [hH, hz]
    show (match (roundNumbers Z.D.1 "RNG")[s.seg]? with
      | some n => n + 1
      | none => 0) = _
    rw [hrng]

/-- The field `ready` of the filling of "ZZ". -/
theorem zz_ready (hlay : layFits G.first.shape G.first.layout = true)
    (hmsg : msgFits G.first.codes G.first.shape G.first.layout s.seg s.array.message = true)
    (htl : (G.built[s.seg]?).map (·.tl) = some tl) (hm : (mats s.seg).length = tl.NM)
    (hrng : (roundNumbers Z.D.1 "RNG")[s.seg]? = some b.rng)
    (hc : columnsOf tl * tl.tau = d.entry.trits)
    (hin : (zzVals (zzPubOf G Z.D.1 mats)).inside G.first.layout s.seg = true)
    {hd : List Fmt.Drawn}
    (hz : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a = none ∨
      (bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a = some (s.seg, s.array.message) ∧
        ∃ R, hd[b.rng]? = some R ∧ drawFit d R = true)) :
    (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).ready hd a = true := by
  show (((bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a).all fun x =>
      layFits G.first.shape G.first.layout &&
        msgFits G.first.codes G.first.shape G.first.layout x.1 x.2 &&
        (zzVals (zzPubOf G Z.D.1 mats)).ready hd x.1) &&
    (bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a).all fun x =>
      (zzVals (zzPubOf G Z.D.1 mats)).inside G.first.layout x.1) = true
  rcases hz with hz | ⟨hz, R, hR, hf⟩
  · rw [hz]
    rfl
  · obtain ⟨t1, -⟩ := trits_of_fit hf
    have hrd : (zzVals (zzPubOf G Z.D.1 mats)).ready hd s.seg = true := by
      show (((G.built[s.seg]?).map (·.tl)).any fun tl =>
        (mats s.seg).length == tl.NM &&
          (drawnAt (roundNumbers Z.D.1 "RNG") hd s.seg).toOption.any fun t =>
            t.length == columnsOf tl * tl.tau) = true
      have hdr : drawnAt (roundNumbers Z.D.1 "RNG") hd s.seg = .ok R.trits := by
        unfold drawnAt
        rw [hrng]
        show (match hd[b.rng]? with
          | some d => Except.ok d.trits
          | none => Except.error "a segment's matrix has not been drawn") = _
        rw [hR]
      rw [htl, hdr]
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, Except.toOption]
      exact ⟨hm, t1.trans hc.symm⟩
    rw [hz]
    simp only [Option.all_some, hlay, hmsg, hrd, hin, Bool.and_self]

end

/-- **THE DIGITS' DATA ARE READY** at every list of challenges that fits the declared rounds and
reaches the sending. -/
theorem digits_ready {Z : Pub} {G : Ground} {mats : Nat → List (Nat × String × Nat)} {a : MsgAddr}
    (F : DigitsFit Z G mats a) {heard : List Fmt.Drawn}
    (hfit : drawsFit (Z.D.1.take heard.length) heard = true)
    (hlen : ∀ s, seatAt (seatsOf Z G "BZ") a = some s → s.heard ≤ heard.length) :
    (K1.digitsFill Z G mats).readyAt heard a = true := by
  obtain ⟨s, b, tl, d, hs, hb, hlay, hmsg, hone, hr1, hw, hd, htl, hm, hrng, hc, hin⟩ := F
  have hl := hlen s hs
  have hlt : b.rng < heard.length := by omega
  obtain ⟨R, hR, hf⟩ := drawn_at hfit (by rw [List.getElem?_take_of_lt hlt]; exact hd)
  have e1 := bz_heardAt (mats := mats) hs
  have key : ∀ n m, b.rng < n → b.rng < m → ((heard.take n).take m)[b.rng]? = some R := by
    intro n m h1 h2
    rw [List.getElem?_take_of_lt h2, List.getElem?_take_of_lt h1]
    exact hR
  show (decide (max ((bzRows Z G mats).heardAt a)
        ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a) ≤ heard.length) &&
    ((bzRows Z G mats).ready ((heard.take (max ((bzRows Z G mats).heardAt a)
        ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a))).take
          ((bzRows Z G mats).heardAt a)) a &&
      (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).ready
        ((heard.take (max ((bzRows Z G mats).heardAt a)
          ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a))).take
            ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).heardAt a)) a)) = true
  rw [e1]
  rcases zz_heardAt (mats := mats) hs hrng with ⟨e2, hz⟩ | ⟨e2, hz⟩
  · rw [e2, hr1, Nat.max_self]
    rw [bz_ready hs hb hlay hmsg hone hw (key _ _ (by omega) (by omega)) hf,
      zz_ready hlay hmsg htl hm hrng hc hin
        (Or.inr ⟨hz, R, key _ _ (by omega) (by omega), hf⟩)]
    simp only [Bool.and_self, Bool.and_true, decide_eq_true_eq]
    exact hl
  · rw [e2, Nat.max_eq_left (Nat.zero_le _)]
    rw [bz_ready hs hb hlay hmsg hone hw (key _ _ (by omega) (by omega)) hf,
      zz_ready (b := b) hlay hmsg htl hm hrng hc hin (Or.inl hz)]
    simp only [Bool.and_self, Bool.and_true, decide_eq_true_eq]
    exact hl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.trits_of_fit
#print axioms ProofFile.Honest.K10.bz_heardAt
#print axioms ProofFile.Honest.K10.bz_ready
#print axioms ProofFile.Honest.K10.zz_heardAt
#print axioms ProofFile.Honest.K10.zz_ready
#print axioms ProofFile.Honest.K10.digits_ready
