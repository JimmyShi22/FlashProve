-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Good2.lean: the law of kind K13's joined block at its place, with a pin that
fixes no more than was committed in front of the draws. Statements with their proofs.

The law of Johnson/Desc/K13/Law/Good.lean asks that the pin fixes a value at every mask entry of
every message. At a reader that takes all mask entries from one world no real run can pay that:
messages are sent behind the batching's draws, and their mask entries are fixed by nothing in front.
Here the pin fixes the matrix and the mask entries of the index masks' message alone (`AgreeAt`).
What pays for it is a test of the kind's front: every mask entry of every row of the pile is of that
message.
Main names:
  `frontB_fit`, `onLedger_of_fit`, `enter_out`, `atM3_ledger`: where the joined block says yes, the
    pile's rows name the entries of the index masks' message alone.
  `pieceM3_key`: what the piece's yes gives (the same as inside the proof of `atM3_goodIn`).
  `atM3_goodIn2`: **the law.**
  `pinOf2`, `atM3_goodIn_pins`: the law at the block's own entries, at any local decoder, typed at
    the plan's number of column variables, with the promise `FrontOk P` behind.
Used of `verify-on-bytes`: `memberRowsFit`, as a pure function; what Johnson/Desc/K13/Law/Good.lean
names.

What is not claimed. What Johnson/Desc/K13/Law/Good.lean says is not claimed, but for the premise on
the pin, which is the weaker one here. The condition in front in `atM3_goodIn_pins`: the record's
number of the index masks' message is the one that the pin speaks of. `Declared` is a test on a
plan's written rounds: an evaluation at two stored sets' public files, a small and a full-size one,
said yes, and five controls said no; no theorem says it of a plan. `Local` asks only that the
decoder reads the stored table and the earlier trees: every such function meets it. A decoder that
reads the oracles alone singles out one member of a list whatever the samples in the record say: so
the laws at such a decoder are idle for the witness that the samples pin. The form to carry on is
that of Johnson/Desc/K13/Law/PinA.lean. The number nR of the matrix's rows is a free letter: that it
is the plan's is said nowhere but in Johnson/Desc/K13/Law/Caller.lean. That the piece is owed just
its stretch and that its trees are listed: Johnson/Desc/K13/Law/Tile.lean, under a test on data.

-/
import Johnson.Desc.K13.Law.Agree
import Johnson.Desc.K13.Law.M3K

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- one proof serves the lens with and without the arm "between": one alternative stays unused
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- Where the front says yes, the pile has passed the test on its form, at the part behind. -/
theorem frontB_fit {T : Type} (X : Lens T) (P : Where) {t t' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (frontB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ p : Part, X.enter t = some t' ∧ X.get? t' = some p ∧
      memberRowsFit p.d.st P.lin p.indexMasks p.pile = true := by
  simp only [frontB, still, front_is, bind_ok, there_ok, need_ok, pure_ok, Lens.part] at h
  obtain ⟨t₁, h1, p, hp, _, ⟨_, _, _, _, h3⟩, rfl⟩ := h
  exact ⟨p, h1, hp, h3⟩

/-- The test on the pile's form: every mask entry of every row is of the index masks' message. -/
theorem onLedger_of_fit {st : Statement} {Sh : LinShape} {idx : ℕ} {pile : List TensorRow}
    (h : memberRowsFit st Sh idx pile = true) : ∀ r ∈ pile, OnLedger idx r := by
  unfold memberRowsFit at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    exact fun r hr t ht => (h.2 r hr).1.1 t ht

/-- The chain's coming to its end leaves what the links have handed on. -/
theorem enter_out {s s₁ : S} (he : atS.enter s = some s₁) : s₁.out = s.out := by
  cases hs : s.here with
  | fin a =>
    have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
    rw [e1] at he
    rw [← Option.some.inj he]
    simp only [S.enterMem, hs]
  | between =>
    first
      | (have e1 : atS.enter s = none := by simp only [atS, hs]
         rw [e1] at he
         cases he)
      | (have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
         rw [e1] at he
         rw [← Option.some.inj he]
         simp only [S.enterMem, hs])
  | lay a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he
  | att a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he
  | head a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he
  | mem a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he

/-- **Where the joined block says yes, the pile's rows name the entries of the index masks' message
alone.** -/
theorem atM3_ledger {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∀ r ∈ s.out.pending, OnLedger s.out.indexMasks r := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, _⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, _⟩ := ebind_ok.1 h12
  obtain ⟨p, he, hp, hfit⟩ := frontB_fit atS P h1
  have ho := enter_out he
  obtain ⟨m₁, hs1, _, _, _⟩ := get_mem hp
  simp only [atS, hs1] at hp
  rw [← Option.some.inj hp] at hfit
  have hfit' : memberRowsFit s₁.st P.lin s₁.out.indexMasks s₁.out.pending = true := hfit
  rw [ho] at hfit'
  exact onLedger_of_fit hfit'

/-- What the piece's yes gives. -/
theorem pieceM3_key (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hk : P.lin.kCol = ds.length) (a : S × F.E.Str) :
    ∀ τ b, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
      (mapsOf dZ d0 ds).pass τ = true ∧
      ∃ r rs' out, (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest = r :: rs' ∧
        batt (owedOf a.1) ds.length P.rows a.1.out.pending a.1.out.indexMasks (dOf a.1)
          (r :: rs') = .ok out ∧
        a.1.rows = a.1.out.pending ∧ b.1.rows = [out.1] := by
    intro τ b hb
    have hb' : (if sTests (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ
        then (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).run a.1
          (sView (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ)
        else none).map (fun xo =>
          (xo, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.imp a.2 τ)) = some b := hb
    by_cases ht : sTests (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ
        = true
    · rw [if_pos ht] at hb'
      cases hrun : (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).run a.1
          (sView (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ) with
      | none =>
        rw [hrun] at hb'
        cases hb'
      | some s' =>
        rw [hrun] at hb'
        obtain rfl := Option.some.inj hb'
        simp only [sTests, Bool.and_eq_true] at ht
        refine ⟨(maps_pass dZ d0 ds τ).trans ht.1.1, ?_⟩
        obtain ⟨gs, _, hdec⟩ := single_ok hrun
        obtain ⟨out, hbt, hr1, hr2⟩ := atM3_ok hdec
        have e1 : ((rvT (ckP .two) (dZ :: d0 :: ds) τ ++ []).map noDigest).take
            (2 + P.lin.kCol) = (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest := by
          rw [List.append_nil]
          refine List.take_of_length_le ?_
          rw [List.length_map, rvT_len, hk]
          simp
          omega
        have hbt' : batt (owedOf a.1) P.lin.kCol P.rows a.1.out.pending a.1.out.indexMasks
            (dOf a.1) (((rvT (ckP .two) (dZ :: d0 :: ds) τ ++ []).map noDigest).take
              (2 + P.lin.kCol)) = .ok out := hbt
        rw [e1, hk] at hbt'
        obtain ⟨mZ, cZ, τ1⟩ := τ
        exact ⟨_, _, out, rfl, hbt', hr1, hr2⟩
    · rw [if_neg ht] at hb'
      cases hb'

/-- **The law**, with a pin that fixes the matrix and the mask entries of the index masks' message
alone. on: any condition in front under which the pin does so. -/
theorem atM3_goodIn2 (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hk : P.lin.kCol = ds.length) {nZ n0 aZ a0 : ℕ}
    (hZ : SendsDraws (toRD dZ) nZ 1 0 aZ) (h0 : SendsDraws (toRD d0) n0 1 0 a0)
    (hs : ∀ d ∈ ds, ∃ n a, SendsDraws (toRD d) n 1 0 a)
    (rw : W → Wit GE nR ds.length) (Pin : F.E.Str → W → Prop) (on : S × F.E.Str → Prop)
    (hdet : ∀ a w w', on a → Pin a.2 w → Pin a.2 w' →
      AgreeAt a.1.out.indexMasks (rw w) (rw w'))
    (hback : ∀ a τ b w, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
      Pin b.2 w → Pin a.2 w) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn on (FrontOk P)
      (RowsHold rw Pin) (RowsHold rw Pin) := by
  intro a ha
  have key := pieceM3_key (Cl := Cl) (W := W) F P base dZ d0 ds hk a
  by_cases hn : a.1.out.pending.length = P.rows
  · by_cases hl : ∀ r ∈ a.1.out.pending, OnLedger a.1.out.indexMasks r
    · have hD := batt_sound2 ρg nR ds.length W rw (Pin a.2) a.1.out.indexMasks
        (fun w w' => hdet a w w' ha) (owedOf a.1) P.rows a.1.out.pending (dOf a.1) F.E a.2 hl
      have hfit : (mapsOf dZ d0 ds).carry.Fits (errK a.1.out.pending.length ds.length)
          ((mapsOf dZ d0 ds).err (errK P.rows ds.length)) := by
        rw [hn]
        exact (mapsOf dZ d0 ds).fits (mapsOf_ok hZ h0 hs) _
      refine CarryS.doomed (mapsOf dZ d0 ds).carry _ _ hfit _ _ ?_ ?_ hD
      · intro τ hτ b hb
        rw [Maps.tr_of_pass _ τ (key τ b hb).1] at hτ
        cases hτ
      · intro τ τ' hτ hbad b hb
        obtain ⟨hp, r, rs', out, e, hbt, hr1, hr2⟩ := key τ b hb
        rw [Maps.tr_of_pass _ τ hp] at hτ
        obtain rfl := Option.some.inj hτ
        obtain ⟨r1, rs1, x, t, hd, o, e1, _, _, hx, _, _, hh, _, _, _⟩ := batt_ok hbt
        obtain ⟨rfl, rfl⟩ := List.cons.inj e1
        obtain ⟨rs₀, gs₀, hdec⟩ := piece_ok _ hb
        refine ⟨atM3_front b.2 hdec, fun w hw => ⟨hback a τ b w hb hw.1, ?_⟩⟩
        rw [hr1]
        exact hbad r rs' x hd out hx hh (whole_read nR _ F.E dZ d0 ds τ r rs' x hd e hx hh) hbt w
          (hback a τ b w hb hw.1) (hw.2 out.1 (by rw [hr2]; exact List.mem_singleton.2 rfl))
    · refine Doomed.of_forall _ _ fun τ b hb => ?_
      obtain ⟨rs₀, gs₀, hdec⟩ := piece_ok _ hb
      exact absurd (atM3_ledger hdec) hl
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨_, r, rs', out, _, hbt, _, _⟩ := key τ b hb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hlen, _⟩ := batt_ok hbt
    exact absurd hlen hn

/-- The witness's matrix and its mask entries of the message idx are what a decoder makes of the
oracles. -/
def pinOf2 {F : Frame} {k : ℕ} (idx : ℕ) (rw : W → Wit GE nR k) (dec : F.E.Str → Wit GE nR k) :
    F.E.Str → W → Prop := fun y w => AgreeAt idx (rw w) (dec y)

/-- The law at the block's own entries and at any local decoder, at any number k that is the number
of the variables' written rounds. -/
theorem atM3_goodIn_pins_k (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx k : ℕ) (hk : ds.length = k) (rw : W → Wit GE nR k)
    (dec : F.E.Str → Wit GE nR k) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun a => a.1.out.indexMasks = idx)
      (FrontOk P) (RowsHold rw (pinOf2 idx rw dec)) (RowsHold rw (pinOf2 idx rw dec)) := by
  subst hk
  obtain ⟨nZ, aZ, hZ⟩ := sends_of_entry (d := dZ) (by rw [hD.sigma.1]; rfl)
    (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; exact Nat.zero_le 1)
    (by rw [hD.sigma.1]; exact Nat.zero_le 64) hD.sigma.2.1 hD.sigma.2.2
  obtain ⟨n0, a0, h0⟩ := sends_of_entry (d := d0) (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; rfl)
    (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; exact Nat.zero_le 1)
    (by rw [hD.eps.1]; exact Nat.zero_le 64) hD.eps.2.1 hD.eps.2.2
  refine atM3_goodIn2 F P base dZ d0 ds hD.len hZ h0 (fun d hd => ?_) rw (pinOf2 idx rw dec) _
    (fun a w w' ha h h' => by rw [ha]; exact h.trans h'.symm) ?_
  · obtain ⟨he, hk⟩ := hD.vars d hd
    exact sends_of_entry (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
      (by rw [he]; exact Nat.zero_le 1) (by rw [he]; exact Nat.zero_le 64) hk.1 hk.2
  · exact back_of_reads _ (pinOf2 idx rw dec) fun y y' w h1 h2 hw => by
      have e : dec y = dec y' := hloc y y' h1 h2
      show AgreeAt idx (rw w) (dec y')
      rw [← e]
      exact hw

/-- **The law at the plan's own number of column variables.** -/
theorem atM3_goodIn_pins (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx : ℕ) (rw : W → Wit GE nR P.lin.kCol)
    (dec : F.E.Str → Wit GE nR P.lin.kCol) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun a => a.1.out.indexMasks = idx)
      (FrontOk P) (RowsHold rw (pinOf2 idx rw dec)) (RowsHold rw (pinOf2 idx rw dec)) :=
  atM3_goodIn_pins_k F P base dZ d0 ds hD idx P.lin.kCol hD.len.symm rw dec hloc

end VerifiableInference.Desc.K13.Law
