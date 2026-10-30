-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtShared.lean: kind K14: WHAT THE MAKERS OF THE BOOK OF COINS
(Honest/Book*.lean) READ OF THE SHARED CHAIN's FIRST NINE SUB-PROTOCOLS: the places of the two
sendings and the names of the declared rounds; and what follows, for every list of that form
(SharedForm), for the makers' first steps: which rounds are "SEND seed", which addresses hold them,
which pairs of a round and a sending are no switch's, where a fold's round can stand, and which
rounds stand at the two sendings' places. Common to both sendings' owners. Three definitions (forms,
no code); statements with their proofs.

  SharedForm xs   the list begins with nine sub-protocols that declare 0, 1, 2, 0, 1, 2, 0, 1, 1
                  rounds, named "LIN point" · "SEND seed", "SEND answer" · "LOC" · "SEND seed",
                  "SEND answer" · "LIN zeta" · "SPLIT"; the third stands at "send o_u"'s place, and
                  none but the third; the sixth at "send o_omega"'s, and none but the sixth
  sharedForm_of_flat   lists of the form FlatOf (Johnson/Desc/K14/Honest/FlatForm.lean), at a shape
                  that splits, are such lists, WHERE NO MEMBER BEHIND THE SIXTH STANDS AT ONE OF THE
                  TWO SENDINGS' PLACES (paid at the proof file's IOP as written in Lean:
                  form_at_files, Honest/K14/BookAtOmegaHead.lean); the four names: the library's
                  entry_names, Johnson/Desc/K14/Honest/ChainStepsMet.lean
  SharedSends p1 codes sentU sentO   the library's list of the shared chain's sendings begins with
                  "the folded row" and "Omega", with these codes and notices; these two are no
                  switches and all behind are (isSwitch, Honest/BookRows.lean: the test's verdicts
                  stand here as clauses; at the library's written list they are shown:
                  Honest/K14/SwitchLabels.lean, Honest/K14/SharedSendsWritten.lean)
  form_rounds, form_seeds, form_pairs   the rounds; the numbers of the rounds "SEND seed": 1, 4, and
                  others; **the pairs that are no switch's: (1, "the folded row"), (4, "Omega")**
  cut_send, form_addr   the frame's cut of a sending's two rounds is one part (an evaluation in
                  Lean's kernel); the addresses of the rounds 1 and 4: the two sendings' parts; the
                  round 7 has one
  addr_passes, form_at_sendings   **an address at "send o_u"'s place is that of the round 1 or 2;
                  one at "send o_omega"'s that of the round 4 or 5**
  fold_round_late, own_not_at   a round named "FOLD epsilon" has a number from 8 on; so no fold's
                  own fresh table is owned at one of the two sendings' places
  form_skip8, form_skip9, rounds_behind_nine   the rounds from 7 on, and from 8 on, are those of the
                  list behind its first eight, and nine, members; the list of places falls into two
                  stretches: the round 7's part stands at a place of the first, the parts of all
                  rounds from 8 on at places of the second (in the proof: the first nine; the rest)
  CarriedRunAt o ms e, carriedRunAt_of_form   what is shown of an entry that carries: it is carried;
                  and where its owner is o its run is one of the list ms

What is not claimed. Nothing on the sub-protocols behind the ninth but their places. Nothing on what
is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookMakers
import Johnson.Desc.ProofFile.Honest.K14.DataMade
import Johnson.Desc.K14.Honest.ChainStepsMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (P14 St blocks)
open Desc.K14.Law (entryAt)
open Desc.K14.Honest (FlatOf)
open ProofFile.Honest.BookShared

/-- **What the book's makers read of the shared chain's first nine sub-protocols.** -/
def SharedForm {S Cl : Type} (xs : List (Block S Cl)) : Prop :=
  ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Block S Cl) (tl : List (Block S Cl))
    (r1 s2 a2 r4 s5 a5 r7 r8 : Fmt.DeclaredRound),
    xs = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl ∧
    (x0.rounds = [] ∧ x1.rounds = [r1] ∧ x2.rounds = [s2, a2] ∧ x3.rounds = [] ∧
      x4.rounds = [r4] ∧ x5.rounds = [s5, a5] ∧ x6.rounds = [] ∧ x7.rounds = [r7] ∧
      x8.rounds = [r8]) ∧
    (r1.entry.name = "LIN point" ∧ s2.entry.name = "SEND seed" ∧ a2.entry.name = "SEND answer" ∧
      r4.entry.name = "LOC" ∧ s5.entry.name = "SEND seed" ∧ a5.entry.name = "SEND answer" ∧
      r7.entry.name = "LIN zeta" ∧ r8.entry.name = "SPLIT") ∧
    (x2.place = sendPlace 2 ∧ x5.place = sendPlace 5) ∧
    (∀ y ∈ x6 :: x7 :: x8 :: tl, y.place ≠ sendPlace 5 ∧ y.place ≠ sendPlace 2) ∧
    (x0.place ≠ sendPlace 5 ∧ x1.place ≠ sendPlace 5 ∧ x3.place ≠ sendPlace 5 ∧
      x4.place ≠ sendPlace 5) ∧
    (x0.place ≠ sendPlace 2 ∧ x1.place ≠ sendPlace 2 ∧ x3.place ≠ sendPlace 2 ∧
      x4.place ≠ sendPlace 2)

/-- **The library's list of the shared chain's sendings**, as far as the book's makers read it at
the two sendings. -/
def SharedSends (p1 : Johnson.G.ChainSends) (codes : OnBytes.Codes)
    (sentU sentO : List OnBytes.OracleNotice) : Prop :=
  p1.codes = codes ∧ ∃ (sU sO : Johnson.G.Sending) (rest : List Johnson.G.Sending),
    p1.sends = sU :: sO :: rest ∧ sU.label = "the folded row" ∧ sU.sent = sentU ∧
    sO.label = "Omega" ∧ sO.sent = sentO ∧ isSwitch sU.label = false ∧
    isSwitch sO.label = false ∧ ∀ s ∈ rest, isSwitch s.label = true

/-- **Lists of the form FlatOf, at a shape that splits, are such lists**, where no member behind the
sixth stands at one of the two sendings' places. -/
theorem sharedForm_of_flat {Cl : Type} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {xs : List (Block St Cl)}
    (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true)
    (hno : ∀ y ∈ xs.drop 6, y.place ≠ sendPlace 5 ∧ y.place ≠ sendPlace 2) : SharedForm xs := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, p4, -, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, -⟩ := places2 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, pU, -, pO⟩ := send_declares P 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨sentU, -, e2, e5⟩ := Desc.K14.Law.two_sendings P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, -, r4, -, r7, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨r3, -, r6, -, -⟩ := declares_none P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, r8, -⟩ := declares_split P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
  obtain ⟨⟨_, e0⟩, ⟨_, e1⟩, ⟨_, e3⟩, ⟨_, e4⟩⟩ := Desc.K14.Honest.entry_names P hS
  have n0 : (entryAt P 0).name = "LIN point" := by rw [e0]
  have n1 : (entryAt P 1).name = "LOC" := by rw [e1]
  have n2 : (entryAt P 2).name = "LIN zeta" := by rw [e3]
  have n3 : (entryAt P 3).name = "SPLIT" := by rw [e4]
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, _, _, _, _, _, _, _, _, rfl,
    ⟨l0.rounds, l1.rounds.trans r1, l2.rounds.trans (by rw [e2]; rfl), l3.rounds.trans r3,
      l4.rounds.trans r4, l5.rounds.trans (by rw [e5]; rfl), l6.rounds.trans r6,
      l7.rounds.trans r7, l8.rounds.trans r8⟩,
    ⟨n0, rfl, rfl, n1, rfl, rfl, n2, n3⟩, ⟨l2.place.trans pU, l5.place.trans pO⟩, hno,
    ⟨by rw [q0]; decide, by rw [l1.place, p1]; decide, by rw [l3.place, p3]; decide,
      by rw [l4.place, p4]; decide⟩,
    ⟨by rw [q0]; decide, by rw [l1.place, p1]; decide, by rw [l3.place, p3]; decide,
      by rw [l4.place, p4]; decide⟩⟩

variable {S Cl : Type}

/-- The rounds of such a list. -/
theorem form_rounds {xs : List (Block S Cl)} (h : SharedForm xs) :
    ∃ (r1 s2 a2 r4 s5 a5 r7 r8 : Fmt.DeclaredRound) (T : List Fmt.DeclaredRound),
      xs.flatMap (·.rounds) = r1 :: s2 :: a2 :: r4 :: s5 :: a5 :: r7 :: r8 :: T ∧
      r1.entry.name = "LIN point" ∧ s2.entry.name = "SEND seed" ∧
      a2.entry.name = "SEND answer" ∧ r4.entry.name = "LOC" ∧ s5.entry.name = "SEND seed" ∧
      a5.entry.name = "SEND answer" ∧ r7.entry.name = "LIN zeta" ∧ r8.entry.name = "SPLIT" := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩, -⟩ := h
  exact ⟨r1, s2, a2, r4, s5, a5, r7, r8, tl.flatMap (·.rounds),
    by simp [List.flatMap_cons, h0, h1, h2, h3, h4, h5, h6, h7, h8], n1, n2, n3, n4, n5, n6, n7, n8⟩

/-- The numbers of the rounds "SEND seed": 1, 4, and others. -/
theorem form_seeds {xs : List (Block S Cl)} (h : SharedForm xs) :
    ∃ more, seedRounds xs = 1 :: 4 :: more := by
  obtain ⟨r1, s2, a2, r4, s5, a5, r7, r8, T, hR, n1, n2, n3, n4, n5, n6, n7, n8⟩ := form_rounds h
  refine ⟨((T.zipIdx 8).filter fun r => r.1.entry.name == "SEND seed").map (·.2), ?_⟩
  unfold seedRounds
  rw [hR]
  simp [List.zipIdx_cons, n1, n2, n3, n4, n5, n6, n7, n8]

/-- **The pairs of a round "SEND seed" and a sending that are no switch's.** -/
theorem form_pairs {xs : List (Block S Cl)} (h : SharedForm xs) {sU sO : Johnson.G.Sending}
    {rest : List Johnson.G.Sending} (hU : isSwitch sU.label = false)
    (hO : isSwitch sO.label = false) (hr : ∀ s ∈ rest, isSwitch s.label = true) :
    ((seedRounds xs).zip (sU :: sO :: rest)).filter (fun x => !isSwitch x.2.label) =
      [(1, sU), (4, sO)] := by
  obtain ⟨more, hm⟩ := form_seeds h
  rw [hm]
  simp only [List.zip_cons_cons, List.filter_cons, hU, hO, Bool.not_false, if_true]
  congr 2
  refine List.filter_eq_nil_iff.2 fun x hx => ?_
  rw [hr x.2 (List.of_mem_zip hx).2]
  simp

/-- The cut of a sending's two rounds: one part. -/
theorem cut_send : cutOfNames .K1 ["SEND seed", "SEND answer"] = [2] := by decide +kernel

/-- **The addresses of the rounds 1 and 4: the two sendings' parts**; the round 7 has an address. -/
theorem form_addr {xs : List (Block S Cl)} (h : SharedForm xs) :
    addrOfRound xs 1 = some { place := sendPlace 2, part := 0 } ∧
      addrOfRound xs 4 = some { place := sendPlace 5, part := 0 } ∧
      (addrOfRound xs 7).isSome = true := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩, ⟨p2, p5⟩, -⟩ := h
  have c2 : partsCut x2 = [2] := by
    unfold partsCut
    rw [h2, p2]
    simp only [List.map_cons, List.map_nil, n2, n3]
    exact cut_send
  have c5 : partsCut x5 = [2] := by
    unfold partsCut
    rw [h5, p5]
    simp only [List.map_cons, List.map_nil, n5, n6]
    exact cut_send
  refine ⟨?_, ?_, ?_⟩
  · rw [addrOfRound_skip _ _ _ (by rw [h0]; simp), addrOfRound_skip _ _ _ (by rw [h0, h1]; simp),
      addrOfRound, if_pos (by rw [h0, h1, h2]; simp), c2, p2]
    simp [h0, h1]
  · rw [addrOfRound_skip _ _ _ (by rw [h0]; simp), addrOfRound_skip _ _ _ (by rw [h0, h1]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3, h4]; simp),
      addrOfRound, if_pos (by rw [h0, h1, h2, h3, h4, h5]; simp), c5, p5]
    simp [h0, h1, h2, h3, h4]
  · rw [addrOfRound_skip _ _ _ (by rw [h0]; simp), addrOfRound_skip _ _ _ (by rw [h0, h1]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3, h4]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3, h4, h5]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3, h4, h5, h6]; simp),
      addrOfRound_skip _ _ _ (by rw [h0, h1, h2, h3, h4, h5, h6, h7]; simp),
      addrOfRound, if_pos (by rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]; simp)]
    rfl

/-- A sub-protocol at another place than the address's is passed. -/
theorem addr_passes (b : Block S Cl) (bs : List (Block S Cl)) (j : Nat) (a : Addr)
    (hb : b.place ≠ a.place) (hj : addrOfRound (b :: bs) j = some a) :
    b.rounds.length ≤ j ∧ addrOfRound bs (j - b.rounds.length) = some a := by
  rw [addrOfRound] at hj
  split at hj
  · refine absurd ?_ hb
    rw [← Option.some.inj hj]
  · exact ⟨by omega, hj⟩

/-- **An address at "send o_u"'s place is that of the round 1 or 2; one at "send o_omega"'s place
that of the round 4 or 5.** -/
theorem form_at_sendings {xs : List (Block S Cl)} (h : SharedForm xs) (i : Nat) (a : Addr)
    (ha : addrOfRound xs i = some a) :
    (a.place = sendPlace 2 → i = 1 ∨ i = 2) ∧ (a.place = sendPlace 5 → i = 4 ∨ i = 5) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, -, ⟨p2, p5⟩, hno, ⟨q0, q1, q3, q4⟩,
    ⟨u0, u1, u3, u4⟩⟩ := h
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨g0, ha⟩ := addr_passes _ _ _ a (by rw [hp]; exact u0) ha
    obtain ⟨g1, ha⟩ := addr_passes _ _ _ a (by rw [hp]; exact u1) ha
    rw [h0, h1] at *
    simp only [List.length_nil, List.length_cons] at *
    rw [addrOfRound] at ha
    split at ha
    · rename_i hlt
      rw [h2] at hlt
      simp only [List.length_nil, List.length_cons] at hlt
      omega
    · have hm := addrOfRound_place _ _ _ ha
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      have hy2 : y.place = sendPlace 2 := e.trans hp
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · exact absurd hy2 u3
      · exact absurd hy2 u4
      · rw [p5] at hy2
        exact absurd hy2 (by decide)
      · exact absurd hy2 (hno y (by simpa only [List.mem_cons] using hy)).2
  · obtain ⟨g0, ha⟩ := addr_passes _ _ _ a (by rw [hp]; exact q0) ha
    obtain ⟨g1, ha⟩ := addr_passes _ _ _ a (by rw [hp]; exact q1) ha
    obtain ⟨g2, ha⟩ := addr_passes _ _ _ a (by rw [hp, p2]; decide) ha
    obtain ⟨g3, ha⟩ := addr_passes _ _ _ a (by rw [hp]; exact q3) ha
    obtain ⟨g4, ha⟩ := addr_passes _ _ _ a (by rw [hp]; exact q4) ha
    rw [h0, h1, h2, h3, h4] at *
    simp only [List.length_nil, List.length_cons] at *
    rw [addrOfRound] at ha
    split at ha
    · rename_i hlt
      rw [h5] at hlt
      simp only [List.length_nil, List.length_cons] at hlt
      omega
    · have hm := addrOfRound_place _ _ _ ha
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      exact absurd (e.trans hp) (hno y hy).1

/-- A round named "FOLD epsilon" has a number from 8 on. -/
theorem fold_round_late {xs : List (Block S Cl)} (hX : SharedForm xs) {e : Nat} {ρ : Fmt.DeclaredRound}
    (h : (xs.flatMap (·.rounds))[e]? = some ρ) (hn : ρ.entry.name = "FOLD epsilon") : 8 ≤ e := by
  obtain ⟨r1, s2, a2, r4, s5, a5, r7, r8, T, hR, n1, n2, n3, n4, n5, n6, n7, n8⟩ := form_rounds hX
  rw [hR] at h
  have no : ∀ (x : Fmt.DeclaredRound) (w : String), x.entry.name = w → w ≠ "FOLD epsilon" →
      x = ρ → False := fun x w hw hne hx => hne (by rw [← hw, hx, hn])
  rcases Nat.lt_or_ge e 8 with hlt | hge
  · exfalso
    interval_cases e
    · exact no r1 _ n1 (by decide) (Option.some.inj h)
    · exact no s2 _ n2 (by decide) (Option.some.inj h)
    · exact no a2 _ n3 (by decide) (Option.some.inj h)
    · exact no r4 _ n4 (by decide) (Option.some.inj h)
    · exact no s5 _ n5 (by decide) (Option.some.inj h)
    · exact no a5 _ n6 (by decide) (Option.some.inj h)
    · exact no r7 _ n7 (by decide) (Option.some.inj h)
    · exact no r8 _ n8 (by decide) (Option.some.inj h)
  · exact hge

/-- **No fold's own fresh table is owned at one of the two sendings' places**: its owner holds a
round "FOLD epsilon". -/
theorem own_not_at {xs : List (Block S Cl)} (hX : SharedForm xs) :
    ∀ w ∈ ownFreshIn xs, w.fold.place ≠ sendPlace 2 ∧ w.fold.place ≠ sendPlace 5 := by
  intro w hw
  unfold ownFreshIn at hw
  dsimp only at hw
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.1 hw
  split at hr
  · cases hr
  · obtain ⟨pq, hpq, hr⟩ := opt_bind hr
    obtain ⟨f, -, hr⟩ := opt_map hr
    obtain ⟨e, s, ρ, hρ, hn, -, hp, -⟩ := behindFold_rounds (p := pq.1) (q := pq.2) hpq
    have e1 : w.fold = pq.1 := by rw [← hr]
    rw [planOf_rounds] at hρ
    rw [addrIn_planOf] at hp
    have h8 := fold_round_late hX hρ hn
    obtain ⟨f2, f5⟩ := form_at_sendings hX e pq.1 hp
    rw [e1]
    exact ⟨fun g => by have := f2 g; omega, fun g => by have := f5 g; omega⟩

/-- The rounds from 7 on are those of the list behind its first eight members. -/
theorem form_skip8 {xs : List (Block S Cl)} (hX : SharedForm xs) (j : Nat) :
    addrOfRound xs (7 + j) = addrOfRound (xs.drop 8) j := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, -⟩ := hX
  have step : ∀ (b : Block S Cl) (bs : List (Block S Cl)) (i n : Nat), b.rounds.length = n →
      n ≤ i → addrOfRound (b :: bs) i = addrOfRound bs (i - n) := by
    intro b bs i n hb hi
    subst hb
    exact addrOfRound_skip b bs i hi
  rw [step x0 _ _ 0 (by rw [h0]; rfl) (by omega), step x1 _ _ 1 (by rw [h1]; rfl) (by omega),
    step x2 _ _ 2 (by rw [h2]; rfl) (by omega), step x3 _ _ 0 (by rw [h3]; rfl) (by omega),
    step x4 _ _ 1 (by rw [h4]; rfl) (by omega), step x5 _ _ 2 (by rw [h5]; rfl) (by omega),
    step x6 _ _ 0 (by rw [h6]; rfl) (by omega), step x7 _ _ 1 (by rw [h7]; rfl) (by omega)]
  show addrOfRound (x8 :: tl) _ = addrOfRound (x8 :: tl) j
  congr 1
  omega

/-- The rounds from 8 on are those of the list behind its first nine members. -/
theorem form_skip9 {xs : List (Block S Cl)} (hX : SharedForm xs) (j : Nat) :
    addrOfRound xs (8 + j) = addrOfRound (xs.drop 9) j := by
  have h := form_skip8 hX (1 + j)
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
    ⟨-, -, -, -, -, -, -, -, h8⟩, -⟩ := hX
  have e : 7 + (1 + j) = 8 + j := by omega
  rw [e] at h
  rw [h]
  show addrOfRound (x8 :: tl) (1 + j) = addrOfRound tl j
  rw [addrOfRound_skip x8 tl _ (by rw [h8]; simp), h8]
  congr 1
  simp

/-- **The list of places falls into two stretches: the round 7's part stands at a place of the
first; the parts of all rounds from 8 on stand at places of the second** (in the proof: the first
nine places; the rest); the round 7 is the first that is named "SPLIT". -/
theorem rounds_behind_nine {xs : List (Block S Cl)} (hX : SharedForm xs) :
    ∃ (l₁ l₂ : List Place) (s : Addr), xs.map (·.place) = l₁ ++ l₂ ∧
      addrOfRound xs 7 = some s ∧ s.place ∈ l₁ ∧
      (xs.flatMap (·.rounds)).findIdx (fun r => r.entry.name == "SPLIT") = 7 ∧
      ∀ i a, 8 ≤ i → addrOfRound xs i = some a → a.place ∈ l₂ := by
  have k8 := form_skip8 hX 0
  have k9 := form_skip9 hX
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, -⟩ := hX
  obtain ⟨n, hn⟩ : ∃ n, addrOfRound (x8 :: tl) 0 = some ⟨x8.place, n⟩ := by
    rw [addrOfRound, if_pos (by rw [h8]; exact Nat.one_pos)]
    exact ⟨_, rfl⟩
  refine ⟨[x0, x1, x2, x3, x4, x5, x6, x7, x8].map (·.place), tl.map (·.place), ⟨x8.place, n⟩,
    by simp, k8.trans hn, by simp, ?_, fun i a hi ha => ?_⟩
  · simp [List.flatMap_cons, h0, h1, h2, h3, h4, h5, h6, h7, h8, List.findIdx_cons, m1, m2, m3, m4,
      m5, m6, m7, m8]
  · have e : 8 + (i - 8) = i := by omega
    have h9 := k9 (i - 8)
    rw [e, ha] at h9
    exact addrOfRound_place _ _ _ h9.symm

/-- What is shown of an entry that carries: it is carried; and where its owner is o its run is one
of the list ms. -/
def CarriedRunAt (o : Addr) (ms : List (Due × Due)) (e : Ahead) : Prop :=
  e.once = false ∧ (e.owner = o → (e.start, e.count) ∈ ms)

/-- From the form of carrying entries, where the carried messages are among the listed ones. -/
theorem carriedRunAt_of_form {o : Addr} {ms : List (Due × Due)} {L G : List SentMsg}
    {own : Option SentMsg} {r : List Ahead}
    (hm : ∀ m ∈ L, m.sender = o → (m.start, m.count) ∈ ms)
    (hf : ∀ e ∈ r, ∃ m, (m ∈ G ∨ own = some m) ∧ e.owner = m.sender ∧ e.start = m.start ∧
      e.count = m.count ∧ e.once = false)
    (hG : ∀ m ∈ G, m ∈ L) (ho : ∀ m, own = some m → m ∈ L) :
    ∀ e ∈ r, CarriedRunAt o ms e := by
  intro e he
  obtain ⟨m, hmem, e1, e2, e3, e4⟩ := hf e he
  refine ⟨e4, fun hown => ?_⟩
  rw [e2, e3]
  exact hm m (hmem.elim (hG m) (ho m)) (e1 ▸ hown)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sharedForm_of_flat
#print axioms ProofFile.Honest.K14.form_rounds
#print axioms ProofFile.Honest.K14.form_seeds
#print axioms ProofFile.Honest.K14.form_pairs
#print axioms ProofFile.Honest.K14.cut_send
#print axioms ProofFile.Honest.K14.form_addr
#print axioms ProofFile.Honest.K14.addr_passes
#print axioms ProofFile.Honest.K14.form_at_sendings
#print axioms ProofFile.Honest.K14.fold_round_late
#print axioms ProofFile.Honest.K14.own_not_at
#print axioms ProofFile.Honest.K14.form_skip8
#print axioms ProofFile.Honest.K14.form_skip9
#print axioms ProofFile.Honest.K14.rounds_behind_nine
#print axioms ProofFile.Honest.K14.carriedRunAt_of_form
