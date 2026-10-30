-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsSig.lean: no place of a stored set is known
at which all premises hold together. The lookup on the digits of a link's smallness test AT THE
TABLE OF JOINTS: THE ROW's THREE PREMISES ON THE SIGNATURE (fCf, fPin, pinBack of
k3_digits_seatLawsR) PAID AT THE TABLE's OWN
FILLING OF ITS LETTERS ON THE READING OF THE ORACLES (meaningSig: pin := pinJT, noColl := noCollJT:
Johnson/Desc/Sound/BordersFill.lean, MeaningSig.lean), under named conditions on the plan and on the
table's reader of samples. Statements and proofs. Ties: no error term. NO SOUNDNESS IS CLAIMED.
After the pattern at the lookup on a link's calls (K3CallsFill.lean: calls_cf, calls_pinIn). pinBack
CALLS pinJT_rides (Johnson/Desc/Sound/SigRides.lean),
at the record's type First.S and the reader fun s => smpT (z, s).
  ReadsOutside π · reads_*: π does not turn where the record's fields «here» and «failed» are laid
  anew; the record's writers that the kind's two seats and its three steps without a round use leave
  such a π.
  stated_reads: **A YES OF THE WHOLE SEATED BLOCK (the value of K3.theStated at any address) LEAVES
  EVERY SUCH π.** No premise on the plan.
  digSending: the link's own list as ONE sending S0 := (digList x D rad, seatT).
  DigSits: what is asked of the plan and of the two readers of samples: some · bySeat · sent · fits
  · smpIs.
  digits_cf | digits_pinIn | digits_pinBack: THE THREE. digits_samples: a yes of the piece at the
  seat leaves every sample, under hread.
OBJECT: no text that runs, but in stated_reads (K3.theStated's value): the table's letters pin,
noColl against the library's CfAt, PinSig at the link's own list. USER: digMeanR_of_rest
(K3DigitsRestR.lean) calls digits_cf, digits_pinIn, digits_pinBack and digits_samples.
LETTERS: cs := D.codes · smpT, ms: the table's · smp: the row's, which has no public part · seatT,
rad, arr: the row's (at the lookups' layer: L.seat x.link true, L.rad, L.arr).
THE CONDITIONS. some: each member of the link's list has an alike member (ONE SHAPE, ONE RADIUS, one
seat) in the table's list ms: so rad must be the radius that the table's members bear · bySeat: at
alike members the record holds one sample · sent: every seat of the list is a tenant that segment m
sends at one of its three moments · fits: SeatFits ·
smpIs: THE TIE OF THE TWO READERS: the row's smp is the table's smpT at S0, at every public part ·
for pinBack: hbase: every tenant that segment m sends sits in a tree below the piece's base · hread:
the table's reader reads of the record st and book alone.
Limits. NONE OF THE CONDITIONS IS SHOWN AT ANY PLAN OR FILLING. Not claimed: anything on soundness,
completeness or hiding.
Read for this comment in a state that need not be this library's:
Johnson/Desc/Block.lean · First/State.lean ·
First/Borders.lean · Sound/MeaningSig.lean ·
Sound/BordersFill.lean · Sound/TiedSeat.lean ·
Look/K3Caller.lean · Look/K3OwnIs.lean ·
Look/K3QuietLaws.lean · Look/K3ReplyLeaves.lean · Top/H/K3PieceHears.lean.
Compiled with the whole library.
-/
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.Sound.SigRides
import Johnson.Top.H.K3PieceHears
import Johnson.Desc.First.Borders
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.TiedSeat
import Johnson.Desc.First.Look.K3Caller
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.Desc.First.Look.K3QuietLaws
import Johnson.Desc.First.Look.K3ReplyLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice Run
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Numbers S)

/-! ## A yes of the whole seated block leaves what lies outside «here» and «failed» -/

section Reads
variable {α : Type}

/-- π does not turn where «here» and «failed» are laid anew. -/
def ReadsOutside (π : S → α) : Prop :=
  ∀ (s : S) (h : Desc.First.Here) (f : Option String), π { s with here := h, failed := f } = π s

theorem reads_putFork (π : S → α) (hπ : ReadsOutside π) (s : S) (G : Fork) :
    π (s.putFork G) = π s := by
  unfold S.putFork
  split
  · exact hπ s _ s.failed
  · exact hπ s _ s.failed
  · split
    · exact hπ s _ s.failed
    · rfl
  · rfl

theorem reads_putTl (π : S → α) (hπ : ReadsOutside π) (s : S) (tl : HTailF2) :
    π (s.putTl tl) = π s := by
  unfold S.putTl
  split
  · exact hπ s _ s.failed
  · exact hπ s _ s.failed
  · split
    · exact hπ s _ s.failed
    · rfl
  · rfl

theorem reads_mark (π : S → α) (hπ : ReadsOutside π) (s : S) (m : String) :
    π (s.mark m) = π s := by
  unfold S.mark
  split
  · rfl
  · exact hπ s s.here (some m)

theorem reads_hearLook (π : S → α) (hπ : ReadsOutside π) (s : S) (g : Forest.Heard) :
    π (s.hearLook g) = π s := by
  unfold S.hearLook
  split
  · split
    · exact reads_mark π hπ s _
    · exact hπ s _ s.failed
  · split
    · exact reads_mark π hπ s _
    · exact hπ s _ s.failed
  · split
    · exact reads_mark π hπ s _
    · split
      · exact reads_mark π hπ s _
      · exact hπ s _ s.failed
  · exact reads_mark π hπ s _

theorem reads_digits_put {Cl : Type} (π : S → α) (hπ : ReadsOutside π) (claim : Aff → Cl) (s : S)
    (g : Forest.Heard) (G : Fork) : π ((Desc.K3.seatDigits claim).put s g G) = π s := by
  simp only [Desc.K3.seatDigits]
  split
  · rw [reads_putFork π hπ, reads_putTl π hπ]
  · exact reads_mark π hπ s _

theorem reads_calls_put {Cl : Type} (π : S → α) (hπ : ReadsOutside π) (claim : Aff → Cl) (s : S)
    (g : Forest.Heard) (G : Fork) : π ((Desc.K3.seatCalls claim).put s g G) = π s := by
  show π ((s.putFork G).hearLook g) = π s
  rw [reads_hearLook π hπ, reads_putFork π hπ]

theorem reads_quietHead (π : S → α) (hπ : ReadsOutside π) (X : Verify.Public) (s t : S)
    (h : Desc.K3.quietHead X s = .ok t) : π t = π s := by
  obtain ⟨a, c, -, -, rfl⟩ := Desc.K3.quietHead_ok X s t h
  exact hπ s _ s.failed

theorem reads_quietLook (π : S → α) (fs : Forest.Shape) (s t : S)
    (h : Desc.K3.quietLook fs s = .ok t) : π t = π s := by
  obtain ⟨rfl, -⟩ := Desc.K3.quietLook_ok fs s t h
  rfl

theorem reads_quietDigits (π : S → α) (hπ : ReadsOutside π) (used claims : ℕ) (s t : S)
    (h : Desc.K3.quietDigits used claims s = .ok t) : π t = π s := by
  obtain ⟨F, -, -, rfl⟩ := Desc.K3.quietDigits_ok used claims s t h
  exact reads_putFork π hπ s _

theorem reads_quietAt (π : S → α) (hπ : ReadsOutside π) (X : Verify.Public) (i : ℕ) (d : Bool)
    (f : S → Except String S) (hf : Desc.K3.quietAt X i d = some f) (s t : S) (h : f s = .ok t) :
    π t = π s := by
  unfold Desc.K3.quietAt at hf
  try dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain rfl := Option.some.inj hf
       exact reads_quietHead π hπ X s t h)
    | (obtain rfl := Option.some.inj hf
       exact reads_quietLook π _ s t h)
    | (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact reads_quietDigits π hπ _ _ s t h)
    | exact absurd hf (by simp)

/-- **A YES OF THE WHOLE SEATED BLOCK LEAVES EVERY READER OUTSIDE «here» AND «failed».** -/
theorem stated_reads {Cl : Type} (π : S → α) (hπ : ReadsOutside π) (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hdec : B.decide s rs gs = .ok s') : π s' = π s := by
  obtain ⟨B₁, h1, -, ed, -, -⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hw⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i, digits, p, sent, laid, -, -, -, -, -, -, edb, -, -⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  rw [ed] at hdec
  have own : ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      b.decide s rs gs = .ok s' → π s' = π s := by
    intro s s' rs gs hdc
    rw [edb] at hdc
    obtain ⟨g, G, rfl⟩ := Desc.K3.blockVia_put _ a.piece laid sent p [] hdc
    cases digits with
    | false =>
      have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim false = Desc.K3.seatCalls claim := by
        simp [Desc.K3.seatOfLookupOnDigitsOrCalls]
      rw [e]
      exact reads_calls_put π hπ claim s g G
    | true =>
      have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim true = Desc.K3.seatDigits claim := by
        simp [Desc.K3.seatOfLookupOnDigitsOrCalls]
      rw [e]
      exact reads_digits_put π hπ claim s g G
  rcases hw with ⟨-, rfl⟩ | ⟨f, hf, rfl⟩
  · exact own s s' rs gs hdec
  · obtain ⟨i', -, hf'⟩ := Option.bind_eq_some_iff.1 hf
    have hdec' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s₁ => f s₁) = .ok s' := hdec
    cases hb1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error e =>
      rw [hb1] at hdec'
      have k : (Except.error e : Except String S) = .ok s' := hdec'
      cases k
    | ok s₁ =>
      rw [hb1] at hdec'
      have hq : f s₁ = .ok s' := hdec'
      exact (reads_quietAt π hπ X i' _ f hf' s₁ s' hq).trans (own s s₁ _ _ hb1)

theorem stBook_outside : ReadsOutside (fun s : S => (s.st, s.book)) := fun _ _ _ => rfl

end Reads

/-! ## The row's three premises on the signature -/

section
variable {P Cells Tok Xi : Type} (G : Desc.FileDescription Xi) (x : Desc.First.Look.Place)
  (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smpT : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp)
  (smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- The link's own list as one sending. -/
def digSending : Sending := ⟨digList x D rad, seatT⟩

/-- **What is asked of the plan and of the two readers of samples.** -/
structure DigSits : Prop where
  some : ∀ i, ∃ y ∈ ms, Alike y ⟨digSending x D rad seatT, i⟩
  bySeat : SmpBySeat D.codes smpT
  sent : ∀ i, ∃ t ∈ [2, 0, 1], seatT i ∈ N.sent m t
  fits : Desc.Sound.SeatFits G D.codes (digList x D rad) seatT
  smpIs : ∀ (z : P) (s : S) i, smp s i = smpT (z, s) (digSending x D rad seatT) i

variable {x D rad seatT smpT smp ms N m}

theorem DigSits.smpEq (T : DigSits G x D rad seatT smpT smp ms N m) (z : P) :
    smp = fun s => smpT (z, s) (digSending x D rad seatT) :=
  funext fun s => funext fun i => T.smpIs z s i

/-- **fCf.** -/
theorem digits_cf (T : DigSits G x D rad seatT smpT smp ms N m) (z : P) (i) (s : S) (y : Strs)
    (h : noCollJT D.codes G smpT ms (seatT i).1 (seatT i).2 (z, s) y) :
    CfAt G D.codes (digList x D rad) seatT smp i s y := by
  obtain ⟨u, hu, hA⟩ := T.some i
  have hs : SitsAt u (seatT i).1 (seatT i).2 := hA.2
  rw [T.smpEq G z]
  exact (cf_move D.codes G smpT u ⟨digSending x D rad seatT, i⟩ hA (z, s)
    (T.bySeat (z, s) _ _ hA) y).1 (h u hu hs)

/-- **fPin.** -/
theorem digits_pinIn (T : DigSits G x D rad seatT smpT smp ms N m) (z : P) (s : S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent m t, pinJT D.codes G arr smpT ms e.1 e.2 (z, s) y w) :
    PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) s y w := by
  rw [T.smpEq G z]
  refine ⟨T.fits, fun i _ => ?_⟩
  obtain ⟨u, hu, hA⟩ := T.some i
  obtain ⟨t, ht, hm⟩ := T.sent i
  have hs : SitsAt u (seatT i).1 (seatT i).2 := hA.2
  exact (pin_move D.codes G arr smpT u ⟨digSending x D rad seatT, i⟩ hA (z, s)
    (T.bySeat (z, s) _ _ hA) y w).1 ((h t ht (seatT i) hm).2 u hu hs)

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (cs : Codes) (G : Desc.FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smpT : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **A yes of the piece at the seat leaves every sample**, where the table's reader reads of the
record st and book alone. -/
theorem digits_samples (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a₀ : Desc.Place)
    (Bst : Desc.Block S Cl) (h : Desc.K3.theStated claim readers X codes shape a₀ = some Bst)
    (q : Piece (ckP .two) Fr (P × S) Cl (Desc.Wit Cells Tok MsgT)) (hback : q.back = [])
    (f : P → Statement × TreeBook → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (hread : ∀ z s, smpT (z, s) = f z (s.st, s.book)) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      smpT (z, v.1) = smpT (z, u.1) := by
  intro B' hB' z u τ v hc
  obtain ⟨-, -, -, cols, hd⟩ := piece_hears_below
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr S Cl (Desc.Wit Cells Tok MsgT)) B' rfl hback u τ v hc
  have e1 : (v.1.st, v.1.book) = (u.1.st, u.1.book) :=
    stated_reads (fun s : S => (s.st, s.book)) stBook_outside claim readers X codes shape a₀ Bst h
      u.1 v.1 _ cols (hB'.1.2 _ _ _ _ hd)
  rw [hread, hread, e1]

/-- **pinBack.** -/
theorem digits_pinBack (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a₀ : Desc.Place)
    (Bst : Desc.Block S Cl) (h : Desc.K3.theStated claim readers X codes shape a₀ = some Bst)
    (q : Piece (ckP .two) Fr (P × S) Cl (Desc.Wit Cells Tok MsgT)) (hback : q.back = [])
    (hbase : ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent m t, e.1 < q.base)
    (f : P → Statement × TreeBook → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (hread : ∀ z s, smpT (z, s) = f z (s.st, s.book)) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b (w : Desc.Wit Cells Tok MsgT),
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent m t,
      pinJT cs G arr smpT ms e.1 e.2 (z, b.1) (strsOf Fr b.2) w →
        pinJT cs G arr smpT ms e.1 e.2 (z, a.1) (strsOf Fr a.2) w := by
  intro B' hB' z a τ b w hout t ht e he hp
  exact (pinJT_rides cs G arr (fun s => smpT (z, s))
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr S Cl (Desc.Wit Cells Tok MsgT)) ms e.1 e.2 (hbase t ht e he) a b τ hout
    (fun u _ _ => by
      show smpT (z, b.1) u.1 u.2 = smpT (z, a.1) u.1 u.2
      rw [digits_samples cs smpT claim readers X codes shape a₀ Bst h q hback f hread B' hB' z a τ b
        hout]) w).1 hp

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.stated_reads
#print axioms VerifiableInference.OnPublicFiles.digits_cf
#print axioms VerifiableInference.OnPublicFiles.digits_pinIn
#print axioms VerifiableInference.OnPublicFiles.digits_samples
#print axioms VerifiableInference.OnPublicFiles.digits_pinBack
