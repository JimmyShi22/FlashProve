-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastYesLays.lean: THE LEDGER's LAW `yesLays` OF THE LAST CHAIN's FIELD IS PAID:
`OwnYesLays p R π` (LastBehind.lean) HOLDS AT EVERY p, R, π AND EVERY TYPE OF CLAIMS: where
the book-keeping's test at border 2 says yes of the record in front and the proximity test's block,
seated on the last chain's record (`onOwn`), says yes: the own group's test has begun, the codes are
as they were, the statement is tidy. A walk along K12's files' own lemmas; no premise on the place.
  `calls_grows`: along a run of the ground's plain calls (`H2K.Out.Calls`) the statement only grows
    (`Grows`, Johnson/Desc/Grows.lean): so a group that bears the mark "its test has begun" keeps
    it. By `Calls.keeps`, `groundKeeps_grows` and `beginRunP_grows`.
  `begun_inRun`, `batJ_begun`: the batching's yes begins the test OF THE RECORD's OWN GROUP (t.g):
    along the text of `batJ`, as `batJ_calls` walks it; with `beginRunP_inv`.
  `start_codes`: the start's yes (`start₃E`) says that the plan's codes' lengths are in order and
    that the record's codes are the plan's.
  `ownYesLays`: **the law.** The seat: `enterOwn` lays the record's own group as t.g and `leaveOwn`
    takes the statement over. The mark: `batJ_begun`, then `calls_grows` at `stages_calls`. The
    codes and "tidy": `k12_calls` with `calls_walk`: TIDY IS KEPT, NOT MADE: that the statement in
    front is tidy, and that the codes' lengths are in order, are CLAUSES OF THE BOOK-KEEPING's TEST
    AT BORDER 2 (`behindOk_of_two`; `start_codes`). From one type of claims to another: `k12_alike`
    (Johnson/Flat/Last/AnyClaims.lean).
Beside it, K12's files' own, at the kind's own record and under two premises on the place (early;
one answer): `k12_out` (the codes), `k12_out2` (the own group behind the yes, to the field); and
their `k12_grows`, which this file does not use: `calls_grows` at `k12_calls` says the same.
Limits. It stands under a yes of the block's decision and a yes of the book-keeping's test: no
member of either is shown here. Nothing on what the yes means. Nothing on soundness.
-/
import Johnson.LLT25R.LastBehind
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.Law.CallsWalkG
import Johnson.Flat.Last.AnyClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Last VerifiableInference.Desc.Third
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open H2K.Out H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)

/-- **Along a run of the ground's calls the statement only grows.** -/
theorem calls_grows {ft : ℕ} {d d' : DS} (h : Calls ft d d') : Grows d.st d'.st :=
  Calls.keeps (R := fun a b => Grows a.st b.st) (fun d => Grows.refl _)
    (fun _ _ _ => Grows.trans) (fun a b s => by
      cases s with
      | newGroup h => exact groundKeeps_grows.newGroup _ _ _ _ _ h
      | recv h => exact groundKeeps_grows.recv _ _ _ _ _ h
      | admit _ _ _ _ h => exact groundKeeps_grows.admit _ _ _ _ h
      | join h => exact groundKeeps_grows.join _ _ _ _ _ h
      | addRow h => exact groundKeeps_grows.addRow _ _ _ _ h
      | closeLedger h => exact groundKeeps_grows.closeLedger _ _ _ h
      | spend h => exact groundKeeps_grows.spendAsMask _ _ _ h
      | begin h => exact beginRunP_grows _ _ _ _ h
      | count t => exact Grows.refl _
      | cols l => exact Grows.refl _) h

/-- Where a group's test is begun, the group bears the mark. -/
theorem begun_inRun (S : Statement) (g : ℕ) (G : Group) (h : S.groups[g]? = some G) :
    ∃ G', (begun S g G).groups[g]? = some G' ∧ G'.inRun = true := by
  obtain ⟨G₁, h₁, -⟩ := (grows_closeLedgers G.members.toList S).2.1 g G h
  refine ⟨{ G₁ with inRun := true, rows := #[] }, ?_, rfl⟩
  show ((closeLedgers S G.members.toList).groups.modify g _)[g]? = _
  rw [Array.getElem?_modify, if_pos rfl, h₁]
  rfl

/-- **The batching's yes begins the test of the record's own group.** -/
theorem batJ_begun (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) :
    ∃ G, t1.st.groups[t.g]? = some G ∧ G.inRun = true := by
  unfold batJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨⟨row, L⟩, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.batE at hx
    split at hx
    · obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨⟨row', L', S'⟩, hb, hx⟩ := bind_ok hx
      cases hx
      have hb' := mapError_ok hb
      unfold First.Close.bat at hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨⟨input, d⟩, hbeg, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      cases hb'
      obtain ⟨G, hG, -, e⟩ := OnBytes.Means.beginRunP_inv (got_ok hbeg)
      show ∃ G, d.st.groups[t.g]? = some G ∧ G.inRun = true
      rw [e]
      exact begun_inRun _ _ _ hG
    · cases hx
  · cases h

/-- What the start's yes says of the codes. -/
theorem start_codes {codes : Codes} {S : LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    codes.lengthsOk = true ∧ s₀.st.codes = codes := by
  unfold start₃E at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i s₁ hs
        obtain rfl := Except.ok.inj h
        unfold start₃ at hs
        split at hs
        · rename_i hk
          obtain rfl := Option.some.inj hs
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
          simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at hc
          exact ⟨hc.1, hk.1.1⟩
        · cases hs

/-- **THE LEDGER's LAW yesLays.** -/
theorem ownYesLays {Cl' : Type} (p : P₁₄) (R : List Fmt.DeclaredRound) (π : P12) :
    OwnYesLays (Cl' := Cl') p R π := by
  intro f o s s' rs gs hk hd
  have h' : ((enterOwn s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts π : Block T12 Cl').decide t rs gs).bind (leaveOwn s)) = .ok s' := hd
  obtain ⟨t0, ht0, h2⟩ := bindOk h'
  obtain ⟨tE, hE, h3⟩ := bindOk h2
  have e : ({ s with st := tE.st, book := tE.book, roots := tE.roots } : S₃) = s' :=
    Except.ok.inj h3
  have e0 : t0.st = s.st ∧ t0.g = s.loc.own := by
    obtain rfl : _ = t0 := Except.ok.inj ht0
    exact ⟨rfl, rfl⟩
  have hU : (proximityTestKind guardedProximityTestParts π : Blk').decide t0 rs gs = .ok tE := by
    rw [(k12_alike (Cl' := Unit) (Cl := Cl') guardedProximityTestParts π).2.2]
    exact hE
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨hl, hc⟩ := start_codes B.start
  have hl0 : (dT t0 []).st.codes.lengthsOk = true := by
    show t0.st.codes.lengthsOk = true
    rw [e0.1, L.codes, hc]
    exact hl
  have hT0 : Means.Tidy (dT t0 []).st := by
    show Means.Tidy t0.st
    rw [e0.1]
    exact B.tidy
  have C := k12_calls π t0 tE rs gs hU [] []
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts π t0 tE rs gs hU
  have hF : tF = t0 := by
    have hfr' := (like_P5 π).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  rw [hF] at hbat
  obtain ⟨G₁, hG₁, hr₁⟩ := batJ_begun π _ _ _ _ _ ((like_P5 π).bat _ _ _ _ _ hbat)
  obtain ⟨G₂, hG₂, -, -, hrun, -⟩ :=
    (calls_grows (stages_calls π rest 0 first _ _ tE _ _ hst [] [])).2.1 _ G₁ hG₁
  obtain ⟨W, hcodes⟩ := calls_walk OnBytes.Model.Reading.gl C hl0
  have hcodes' : tE.st.codes = t0.st.codes := hcodes
  rw [← e, ← e0.2, ← e0.1]
  exact ⟨⟨G₂, hG₂, hrun hr₁⟩, hcodes', W.tidy hT0⟩

end LLT25

#print axioms LLT25.calls_grows
#print axioms LLT25.batJ_begun
#print axioms LLT25.start_codes
#print axioms LLT25.ownYesLays
