-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/Hands354.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12)
ON THE PROOF FILE's FIRST CHAIN: THE SECOND
TIE (T2At, H2K12/Frame354.lean): behind an accept of the test the table's promise holds at
the next border. A sure step: no chance is counted. Statements and proofs.
Main names:
  held_stays      "the verifier's state holds the out-of-domain (OOD) sample of the tenant at a
                  seat" (smpHeld, Johnson/Desc/SmpRows.lean) rides past an accept of the test at the
                  first chain's finish: by smpHeld_rides and k12_places
                  (Johnson/Desc/K12/Coin/HeldThrough.lean), k12_smp
                  (Johnson/Desc/K12/Coin/SamplesThrough.lean), k12_out
                  (Johnson/Desc/K12/Law/OutK.lean). k12_smp speaks of every older message but the
                  one that holds the first fold's mask: a message whose sample is held is marked as
                  sampled, and the test's own front refuses a mask's message that is
                  (block_front_holds, Johnson/Desc/K12/SeatLaws.lean; sampled_no_mask,
                  H2K12/AcrossOfSits.lean).
  t2_at           THE SECOND TIE, at whichever number k of the list the test has, WHERE BEHIND IT
                  JUST FOUR ITEMS ARE OPEN ("no mark", the stored table's pin, the pending rows, the
                  index masks' pin) AND NO PUBLIC ITEM. The promise's clauses, one by one:
                  "decodes": a premise in the tie's own letters (hDec) · the four tests on the state
                  and the plan's numbers: k12_grownAt (Johnson/Desc/K12/Coin/K12Grows.lean) with
                  goOn_of_B (Johnson/Desc/K12/Coin/GoOnTest.lean) · "in order": the public part
                  rides (hin) · the two public items tied to the index masks' pin, "no collision":
                  across_of_sits (H2K12/AcrossOfSits.lean) · "held": held_stays · "shown", "no
                  collision": the strings below the piece's base stay (stays_behind,
                  Johnson/Top/H0/Walk/StaysBehind.lean).
Limits. (1) A JOINING OVER LETTERS: it pays no law of the kind. (2) hFacts (FactsF and "the state's
codes are the data's") is asked at every state inside the promise and the condition Rch, without a
mark: five fields of FoldFacts (Johnson/Desc/First/FoldFacts.lean). (3) Premises on letters: hDec,
hin, hII, hIT, hheld, hshown, hnc, hsmp (the meaning's and the reader's texts) · hL, hft, hB, hfen
(numbers of the plan) · hk, hk', hp', hOb, hQb, hpinI (the table's lists). (4) WHETHER ALL PREMISES
CAN BE MET TOGETHER IS SHOWN NOWHERE HERE; evaluations alone speak for hOb, hQb, hpinI and hB. At
Rch := "never" the tie is free
and says nothing.

(Where this and lean/THEOREM.md differ, the page holds.)
hl
(the way out lays the statement, the book and the count of roots alone) is a premise here: this file
reads no text of the seat's way out (H2K12/FirstSeatForm.lean).
No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.GoOnTest
import Johnson.Desc.K12.Coin.HeldThrough
import Johnson.Desc.K12.Law.OutK
import Johnson.Desc.Sound.HeldShift
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Loose.H2K12.AcrossOfSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (FileDescription Place Block)
open VerifiableInference.Desc.Sound (Mem Sending strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (ModelPart Item Numbers)

/-- **"The state holds the sample" rides past an accept of the proximity test at the first chain's
finish.** -/
theorem held_stays {Cl : Type} (π : VerifiableInference.Desc.K12.P12) (he : π.early = true)
    (ha : π.answers = 1) (B : Block VerifiableInference.Desc.First.S Cl)
    (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S)
    (hS : H2K.JointK.Sits B (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      π : Block VerifiableInference.Desc.K12.T12 Unit) VerifiableInference.Desc.K12.enterFinish
      leave)
    (hl : VerifiableInference.Desc.K12.Coin.LaysOnly leave) (ft : ℕ)
    (s s' : VerifiableInference.Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (n : ℕ) (hY : B.step ft s rs cols = .ok (s', n))
    (hin : VerifiableInference.Desc.Sound.PlacesInBook s.book) (z t : ℕ)
    (h : VerifiableInference.Desc.smpHeld s.st s.book z t = true) :
    VerifiableInference.Desc.smpHeld s'.st s'.book z t = true := by
  obtain ⟨t0, t', e1, e2, e3⟩ := hS.step ft s s' rs cols n hY
  obtain ⟨gs, hd⟩ := VerifiableInference.Desc.K12.Coin.step_decide _ ft t0 t' _ _ n e2
  have eb := hl _ _ _ e3
  obtain ⟨o, _, _, _, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s t0 e1
  have O := H2K.Out.k12_out π he ha _ t' _ gs hd
  have hfr := (VerifiableInference.Desc.K12.Seat.block_front_holds π _ t' _ gs hd).2.1
  have hz : z < s.book.trees.size := by
    by_contra hc
    have e0 := VerifiableInference.Desc.Sound.oracleNo_high s.book hin z t (Nat.le_of_not_lt hc)
    unfold VerifiableInference.Desc.smpHeld VerifiableInference.Desc.smpSeed at h
    rw [e0] at h
    simp at h
  rw [eb]
  show VerifiableInference.Desc.smpHeld t'.st t'.book z t = true
  rw [VerifiableInference.Desc.K12.Coin.smpHeld_rides s.st t'.st s.book t'.book
    (VerifiableInference.Desc.K12.Coin.k12_places π he ha _ t' _ gs hd) hin O.codes z t hz ?_]
  · exact h
  intro i hi
  have h' := h
  unfold VerifiableInference.Desc.smpHeld VerifiableInference.Desc.smpSeed
    VerifiableInference.Desc.smpRows at h'
  rw [hi] at h'
  simp only [Option.bind_some] at h'
  cases hx : s.st.oracles[i]? with
  | none =>
    rw [hx] at h'
    simp at h'
  | some x =>
    rw [hx] at h'
    simp only [Option.bind_some] at h'
    have hsm : x.sampled = true := by
      by_contra hc
      simp [hc] at h'
    rw [← hx]
    exact VerifiableInference.Desc.K12.Coin.k12_smp π he ha _ t' _ gs hd i
      (Array.getElem?_eq_some_iff.1 hx).1 (sampled_no_mask hfr hx hsm)

section
variable {Xi P W Cl : Type} {Fr : VerifiableInference.Desc.Sound.Frame} (cs : OnBytes.Codes)
  (G : FileDescription Xi) (π : VerifiableInference.Desc.K12.P12)
  (d : VerifiableInference.Desc.First.FoldData)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart)
  (ps : List Place)

/-- **THE SECOND TIE, AT WHICHEVER NUMBER OF THE LIST THE TEST HAS**: behind an accept of the test
the table's promise holds at the next border. -/
theorem t2_at (k : ℕ)
    (q : VerifiableInference.Desc.Sound.Piece (_root_.Run.ckP .two) Fr
      (P × VerifiableInference.Desc.First.S) Cl W)
    (B : Block VerifiableInference.Desc.First.S Cl)
    (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S)
    (hb : q.b = VerifiableInference.Desc.Sound.held (P := P) B) (h0 : q.back = [])
    (hS : H2K.JointK.Sits B (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      π : Block VerifiableInference.Desc.K12.T12 Unit) VerifiableInference.Desc.K12.enterFinish
      leave)
    (hl : VerifiableInference.Desc.K12.Coin.LaysOnly leave) (he : π.early = true)
    (ha : π.answers = 1)
    (hpinI : Item.pinI ∈ VerifiableInference.Desc.K13.Law.openAt links ps k)
    (hII : ∀ x, Mg.pub .indexIs x = VerifiableInference.Desc.K13.indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = VerifiableInference.Desc.K13.indexThereC x.2)
    (hheld : Mg.held = fun j t x => VerifiableInference.Desc.smpHeld x.2.st x.2.book j t)
    (hL : d.L.places[N.indexNo]? = some N.index) (hft : d.ft = 0)
    (hsmp : ∀ a o x, ListedAt ms d.L.places o x → smp a x.1 x.2 =
      VerifiableInference.Desc.K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o)
    (hp : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts π :
      Block VerifiableInference.Desc.K12.T12 Unit).planOk = true)
    (ho : π.nums.ownMask = false) (p p' : Place) (hk : ps[k]? = some p)
    (hk' : ps[k + 1]? = some p')
    (hp' : VerifiableInference.Desc.First.standAt links p' = .fin)
    (hOb : (VerifiableInference.Desc.First.openSets links ps
      (VerifiableInference.Desc.First.start links))[k + 1]?.getD [] =
      [.unmarked, .pinW, .pile, .pinI])
    (hQb : (VerifiableInference.Desc.First.pubSets Mg.more links ps)[k + 1]?.getD [] = [])
    (hB : VerifiableInference.Desc.K12.Coin.goOnB N p p' π
      (VerifiableInference.Desc.K12.Door.toTree d.L) d.sent.codes = true)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2))
    (hin : ∀ x y : P × VerifiableInference.Desc.First.S, y.1 = x.1 → Mg.inOrder x = true →
      Mg.inOrder y = true)
    (hshown : Mg.shown = VerifiableInference.Desc.Sound.shownJT cs G ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hfen : N.index.1 < q.base)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (hFacts : ∀ a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str,
      VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a → Rch k a →
      ¬ a.1.2.failed ≠ none → FactsF d a.1.2 ∧ a.1.2.st.codes = d.sent.codes) :
    T2At N Mg links ps Rch k q := by
  intro a τ b hon hr hm hout
  have hm0 : a.1.2.failed = none := not_not.1 hm
  obtain ⟨F, hcod⟩ := hFacts a hon hr hm
  have A := across_of_sits cs π d smp ms N Mg links ps k q B leave hb h0 hS hl he ha hpinI hII hIT
    hheld hL hft hsmp a b τ hon hm0 hout F
  -- the accept, as a step of the sub-protocol that the piece holds
  obtain ⟨_, n, hst, _⟩ := VerifiableInference.Desc.K12.Coin.yes_step q h0 a τ b hout
  rw [hb] at hst
  obtain ⟨h1, _⟩ := VerifiableInference.Desc.K12.Coin.step_of_held B Fr.ft a.1 b.1 _ _ n hst
  -- the strings below the piece's base stay
  have hstay : Johnson.Desc.First.Walk.Tied.Stays q.base (strsOf Fr a.2) (strsOf Fr b.2) := by
    rw [VerifiableInference.Desc.LinkJoin.out_strs hout]
    exact Johnson.Desc.First.Walk.Tied.stays_behind (_root_.Run.ckP .two) Fr q.base q.ds a.2 τ
  -- the promise in front, clause by clause
  obtain ⟨hii, hit, hbk, _⟩ := VerifiableInference.Desc.K13.Law.promise_index N Mg links ps
    (fun x : P × VerifiableInference.Desc.First.S => x) k hpinI a hon hm0
  obtain ⟨hd, hrest⟩ := hon
  obtain ⟨hB6, hsam, hsn, _⟩ := hrest.resolve_left (fun h => h hm0)
  simp only [Bool.and_eq_true] at hB6
  have hIdx : N.index ∈ VerifiableInference.Desc.First.sampledIn N
      ((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []) :=
    List.mem_flatMap.2 ⟨.pinI, hpinI, by simp⟩
  have hheldA :
      VerifiableInference.Desc.smpHeld a.1.2.st a.1.2.book N.index.1 N.index.2 = true := by
    have := List.all_eq_true.1 hsam N.index hIdx
    rwa [hheld] at this
  obtain ⟨hsh, hno⟩ := hsn N.index hIdx
  -- the four tests on the state and the plan's numbers
  rw [hk] at hbk
  obtain ⟨_, g2, g3, g4, g5, _, _⟩ := VerifiableInference.Desc.K12.Coin.k12_grownAt links N p p'
    [.unmarked, .pinW, .pile, .pinI] π hp ho he ha hp' rfl B leave hS hl d.L Fr.ft a.1.2 b.1.2 _ _ n
    (VerifiableInference.Desc.K12.Coin.goOn_of_B hB a.1.2 hcod hbk) h1
  have hPl : VerifiableInference.Desc.Sound.PlacesInBook a.1.2.book := fun i x hx => by
    obtain ⟨T, hT, -⟩ := (VerifiableInference.Desc.Sound.bookFitsB_iff a.1.2.book).1 F.fits i x hx
    exact (Array.getElem?_eq_some_iff.1 hT).1
  show VerifiableInference.Desc.First.onAt N Mg links ps[k + 1]? _ _ b.1 (strsOf Fr b.2)
  rw [hk', hOb, hQb]
  refine ⟨hDec a τ b hout hd, Or.inr ⟨?_, ?_, ?_, fun x hx => absurd hx (List.not_mem_nil)⟩⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨g2, g3⟩, g4⟩, hin a.1 b.1 A.pub hB6.1.1.2⟩, ?_⟩, g5 hbk⟩
    have e1 : Mg.pub .indexIs b.1 = true := by
      rw [hII] at hii ⊢
      unfold VerifiableInference.Desc.K13.indexIsC at hii ⊢
      rw [A.idx]
      exact hii
    have e2 : Mg.pub .indexThere b.1 = true := by
      rw [hIT] at hit ⊢
      unfold VerifiableInference.Desc.K13.indexThereC at hit ⊢
      rw [A.idx]
      have e := congrArg Option.isSome A.shape
      rw [Option.isSome_map, Option.isSome_map] at e
      rw [e]
      exact hit
    simp [VerifiableInference.Desc.First.pubHeld, VerifiableInference.Desc.First.pubOfItems, e1, e2]
  · have e3 : Mg.held N.index.1 N.index.2 b.1 = true := by
      rw [hheld]
      exact held_stays π he ha B leave hS hl Fr.ft a.1.2 b.1.2 _ _ n h1 hPl _ _ hheldA
    simp [VerifiableInference.Desc.First.samplesHeld, VerifiableInference.Desc.First.sampledIn, e3]
  · intro x hx
    obtain rfl : x = N.index := by
      simpa [VerifiableInference.Desc.First.sampledIn] using hx
    rw [hshown] at hsh ⊢
    rw [hnc] at hno ⊢
    refine ⟨VerifiableInference.Desc.Sound.shownJT_col cs G ms _ _ (strsOf Fr a.2) (strsOf Fr b.2)
      (fun y => hstay.2 N.index.1 y hfen) hsh, fun z hz hs => ?_⟩
    obtain ⟨v, hv, r⟩ := VerifiableInference.Desc.Sound.noCollJT_col cs G smp ms _ _ a.1
      (strsOf Fr a.2) (strsOf Fr b.2) (fun y => hstay.2 N.index.1 y hfen) hno z hz hs
    exact ⟨v, (A.smpI z hz hs).trans hv, r⟩

end

end H2K12

#print axioms H2K12.held_stays
#print axioms H2K12.t2_at
