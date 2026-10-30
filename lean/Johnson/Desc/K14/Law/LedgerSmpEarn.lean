-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSmpEarn.lean: smpY IS EARNED AT A YES OF THE SENDING's PIECE: a proof of
SmpEarnAtOwed (Johnson/Desc/K14/Law/LedgerSmpOwed.lean) AS IT IS TYPED: at any
piece that holds the sending in the wrap, with no word on the piece's written rounds.


HOW. A yes of a piece x with x.b = heldW c is a yes of Block.step at the rounds shown, typed or laid
back. It holds three things:
  (i)   roundsFit at these rounds (the step's first test; c.rounds are the sending's): so they are
        two, and the first draws seeds * (coordinates + 1) elements (K1.draw_len);
  (ii)  viewWordsBelowPrime of them (the wrap's own test: heldW is lift of `below`): so every drawn element's
        words are below the prime;
  (iii) the sending's decision's yes: among what it asks: no seed's factor has all words 0
        (K1.decideSend_iff: asks).
(ii) and (iii) give, by isZeroE_iff (ProgField.lean), that each factor reads as a nonzero element: a
unit. So the first round READS AS the seeds read off it (reads_of_ok). Then K1.seedIs_behind_len ·
seedAt_of_seedIs (SeedAtSeam.lean) · sampleL_of_seed (SampleOfSeed.lean), its six premises: PlanY.

Main names.
  okE_of_below    words below the prime: the program's okE
  cut_factor      a seed cut off a list: its factor is the list's member, or zeroE
  reads_of_ok     ReadsAs at SOME seeds, from (ii) and (iii) alone
  ok_of_seedIs    the sendings' invariant, Tie and PlanY give sampleL's yes at seatY
  piece_step_at   a piece's yes is its block's step's yes at the rounds shown, BY NAME
  smpEarnAt       SmpEarnAtOwed

IS IT EMPTY? An implication at all letters. Its premises on the plan (planOk · condPort ·
sampledAt · PlanY) are tests with code or plain facts on shapes; whether the written plan meets
PlanY's second clause (rows of one kind alone) is K14's files' to evaluate. A yes of such a piece:
the honest file's.
NOT HERE: SmpEarnOwed (the bare decision, without the wrap): there (ii) lacks.

Nothing on soundness.
-/
import Johnson.Desc.K14.Law.LedgerSmp
import Johnson.Desc.K12.Law.SampleOfSeed
import Johnson.Desc.Sound.SeedAtSeam
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.Plain.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Wit noDigest viewWordsBelowPrime fieldPrimeWord roundsFit foldConsOk chainAtOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt Seeds ReadsAs seedsOf cutSeeds
  decideSend decideSend_iff sendOwn condPort cond_tie seedIs_behind_len SeedIs draw_len
  cutSeeds_length)

/-- Words below the prime: the program's own test on an element. -/
theorem okE_of_below (t : UInt64 × UInt64 × UInt64)
    (h : (decide (t.1 < fieldPrimeWord) && decide (t.2.1 < fieldPrimeWord) && decide (t.2.2 < fieldPrimeWord)) = true) :
    okE (E.ofTriple t) = true := h

/-- A seed cut off a list: its factor is a member of the list, or zeroE. -/
theorem cut_factor (v : ℕ) : ∀ (n : ℕ) (l : List E) (sd : List E × E), sd ∈ cutSeeds v n l →
    sd.2 ∈ l ∨ sd.2 = zeroE
  | 0, _, _, h => by simp [cutSeeds] at h
  | n + 1, l, sd, h => by
    simp only [cutSeeds, List.mem_cons] at h
    rcases h with rfl | h
    · cases hd : l.drop v with
      | nil => exact Or.inr rfl
      | cons a t =>
        refine Or.inl ?_
        have : a ∈ l.drop v := by rw [hd]; exact List.mem_cons_self
        simpa [hd] using List.mem_of_mem_drop this
    · rcases cut_factor v n (l.drop (v + 1)) sd h with h' | h'
      · exact Or.inl (List.mem_of_mem_drop h')
      · exact Or.inr h'

/-- **The first round reads as the seeds that are read off it**, where its drawn elements' words are
below the prime and no seed's factor has all words 0. -/
theorem reads_of_ok (P : VerifiableInference.Desc.K1.Par) (r₁ : Fmt.RoundView)
    (hok : ∀ t ∈ r₁.drawn.elems, okE (E.ofTriple t) = true)
    (hnz : ∀ s ∈ seedsOf P r₁, isZeroE s.2 = false) : ∃ ρ : Seeds P, ReadsAs P r₁ ρ := by
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hex : ∀ i : Fin P.seeds, ∃ sd, (seedsOf P r₁)[i.val]? = some sd ∧ readE sd.2 ≠ 0 := by
    intro i
    have hi : i.val < (seedsOf P r₁).length := by
      rw [hlen]
      exact i.isLt
    obtain ⟨sd, hsd⟩ : ∃ sd, (seedsOf P r₁)[i.val]? = some sd := ⟨_, List.getElem?_eq_getElem hi⟩
    have hm : sd ∈ seedsOf P r₁ := List.mem_of_getElem? hsd
    have hz := hnz sd hm
    refine ⟨sd, hsd, fun h0 => ?_⟩
    rcases cut_factor _ _ _ sd hm with h' | h'
    · obtain ⟨t, ht, e⟩ := List.mem_map.1 h'
      have hokE : okE sd.2 = true := by
        rw [← e]
        exact hok t ht
      rw [(isZeroE_iff _ hokE).2 h0] at hz
      cases hz
    · rw [(isZeroE_eq sd.2).2 h'] at hz
      cases hz
  choose sd hsd hne using hex
  exact ⟨fun i => (fun t => readL (sd i).1 t.val, Units.mk0 (readE (sd i).2) (hne i)),
    fun i => ⟨sd i, hsd i, fun _ => rfl, (Units.val_mk0 (hne i)).symm⟩⟩

/-- **The sendings' invariant gives the test's yes.** -/
theorem ok_of_seedIs {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    {ρ : (Fin (Johnson.Pack.bitsZ cs sh) → GE) × GEˣ} {y : GE}
    (hT : VerifiableInference.Desc.K1.Tie cs sh) (hP : PlanY cs sh) (h : SeedIs cs sh St o ρ y) :
    ∃ x, St.oracles[o]? = some x ∧ H2K.Pin.ok (H2K.Pin.sampleL cs (seatY sh o) x) = true := by
  obtain ⟨x, seed, row0, tt, β, hx, hs, hf, hr, hl, hb⟩ := Fence.seedAt_of_seedIs hT h
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
  exact ⟨x, hx, H2K.Pin.sampleL_of_seed cs (seatY sh o) x seed row0 tt β hs hf hr hl hb p1 p2 p3 p4
    p5 p6⟩

/-- **A piece's yes is its block's step's yes at the rounds shown, by name.** After
piece_decides_at (Johnson/Desc/Plain/PieceYes.lean), one line earlier in its proof. -/
theorem piece_step_at {S Cl W : Type} {C : PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str)
    (hb : p.ior.red.out a τ = some b) :
    ∃ k, p.b.step F.ft a.1 (rvT C p.ds τ ++ p.back) (sView C p.stage a.2 τ).opened =
      .ok (b.1, k) := by
  obtain ⟨s', k, hst, H'⟩ := foldConsOk (chainAtOk (pieceOk p a τ b hb))
  have e : (s', (rvT C p.ds τ ++ p.back).drop p.b.rounds.length, _) =
      (b.1, ([] : List Fmt.RoundView), ([] : List VerifiableInference.Desc.OpenedColumn)) := Except.ok.inj H'
  have e₁ : s' = b.1 := congrArg Prod.fst e
  have e₂ : (rvT C p.ds τ ++ p.back).drop p.b.rounds.length = [] := congrArg (fun x => x.2.1) e
  have e₃ : (rvT C p.ds τ ++ p.back).take p.b.rounds.length = rvT C p.ds τ ++ p.back :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 e₂)
  rw [e₃, e₁] at hst
  exact ⟨k, hst⟩

/-- The wrap, opened at a yes, WITH ITS OWN TEST: the rounds shown are below the prime. -/
theorem wrap_below {U σ Cl : Type} (b : Block σ Cl) (x x' : U × σ) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.lift Prod.snd (fun x s => (x.1, s)) (below b)).decide x rs gs = .ok x') :
    viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true := by
  have hd : ((below b).decide x.2 rs gs).map (fun s => (x.1, s)) = .ok x' := h
  cases hB : (below b).decide x.2 rs gs with
  | error e => rw [hB] at hd; cases hd
  | ok s =>
    have hB' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then
        b.decide x.2 rs gs else .error "a word is not below the prime") = .ok s := hB
    split at hB'
    · assumption
    · cases hB'

/-- **A yes of the sending's piece earns smpY.** -/
theorem smpEarnAt : SmpEarnAtOwed := by
  intro P₁ Cl Cells Tok Fr Q n K inFront groups behind hbk _ rad hC k hk hPl c hc hr x hx a τ y hout
    k₀ j
  obtain ⟨kk, hst⟩ := piece_step_at x a τ y hout
  rw [hx] at hst
  obtain ⟨hfit, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ _ _ _ _ _ _ hst
  -- the rounds are the sending's two
  have hfit' : roundsFit (VerifiableInference.Desc.K1.rounds K) (rvT (ckP .two) x.ds τ ++ x.back) =
      true := by
    have e : (heldW (U := P₁) c).rounds = VerifiableInference.Desc.K1.rounds K := hr
    rw [← e]
    exact hfit
  -- the wrap's test, and the sending's own yes
  have hview := wrap_below c a.1 y.1 _ gs hdec
  have hyes := (wrap_decide c a.1 y.1 _ gs hdec).1
  rw [hc] at hyes
  simp only [sendAt, Block.inside] at hyes
  obtain ⟨t, ht, hyes⟩ := ebind_ok hyes
  cases ht
  obtain ⟨t', ht', hyes⟩ := ebind_ok hyes
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx2, rfl⟩ := emap_ok ht'
  obtain ⟨e1, _, _⟩ := hbk _ _ _ (named_some hyes)
  obtain ⟨r₁, r₂, hrs⟩ := decideSend_two K none _ _ _ hx2
  rw [hrs] at hx2 hview
  -- what the first round draws
  obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ q₂, rvT (ckP .two) x.ds τ ++ x.back = [q₁, q₂] := by
    cases hl : rvT (ckP .two) x.ds τ ++ x.back with
    | nil => rw [hl] at hrs; cases hrs
    | cons q₁ l =>
      cases l with
      | nil => rw [hl] at hrs; cases hrs
      | cons q₂ l =>
        cases l with
        | nil => exact ⟨q₁, q₂, rfl⟩
        | cons _ _ => rw [hl] at hrs; cases hrs
  rw [hq] at hrs hfit'
  obtain ⟨rfl, rfl⟩ : noDigest q₁ = r₁ ∧ noDigest q₂ = r₂ := by
    have := List.cons.inj hrs
    exact ⟨this.1, (List.cons.inj this.2).1⟩
  have hlen : ((noDigest q₁).drawn.elems.map E.ofTriple).length = K.seeds * (K.coordinates + 1) :=
    draw_len K q₁ q₂ hfit'
  have hokE : ∀ t ∈ (noDigest q₁).drawn.elems, okE (E.ofTriple t) = true := by
    intro t ht
    unfold viewWordsBelowPrime at hview
    simp only [Bool.and_eq_true, List.all_eq_true] at hview
    exact okE_of_below t (by
      have := (hview.1 (noDigest q₁) List.mem_cons_self).1 t ht
      simpa [Bool.and_eq_true] using this)
  obtain ⟨⟨_, _, hnz, _, _⟩, _, _⟩ := (decideSend_iff K none _ x2 _ _ ids).1 hx2
  obtain ⟨ρ, hρ⟩ := reads_of_ok K (noDigest q₁) hokE hnz
  obtain ⟨yy, hS⟩ := seedIs_behind_len K rad none _ x2 _ _ ids hC hlen hx2 ρ hρ k hk
  obtain ⟨xo, hxo, hokS⟩ := ok_of_seedIs (cond_tie K rad hC k hk) hPl hS
  refine (smpY_iff _ _ _ _ _ _).2 (Or.inr ⟨xo, ?_, hokS⟩)
  rw [e1]
  exact hxo

end Desc.K14.Law

#print axioms Desc.K14.Law.reads_of_ok
#print axioms Desc.K14.Law.ok_of_seedIs
#print axioms Desc.K14.Law.smpEarnAt
