-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLedgerSixteen.lean: where a thread over the key file's first chain stands at
the border 16, in scope, the index-mask message's shape and ledger are the closed term T16's: one
mask row, 48 takes. So take number j behind it hands out entry 48 + j.

  run16_six, shape16_of_thr   the state's shape is T16, after shape15_of_thr
  t16_zero                    message 0 of T16, by the kernel
  ledger_of_shape16           LedgerAt at 48, one mask row
  takes_at16                  the numbers that takeMasksP hands out

Nothing on any property.
-/
import E2E.KeyRangesShape15
import E2E.KeyMaskTakes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open H2K.Member (nKRFull)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces lookupPlace)
open VerifiableInference.Desc.K13.Law (LedgerAt nextAt)

/-- The guards' run over the first sixteen. -/
theorem run16_full (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    runL (gsF.take 16) T0 = .ok T16 := by
  have e : gsF.take 16 = gsF.take 15 ++ [gRng QF nKRFull] := rfl
  rw [e, runL_append _ _ _ _ (run15_full h0 h1), runL_cons _ _ _ _ step15]
  rfl

theorem run16_six {Q : Pub1} (h : Six Q) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    (Z₁W Q CF D told nKRFull v).run 16 T0 = .ok T16 := by
  unfold Z₁W
  rw [gAll₁_six h]
  rw [run_take (sh₁B Q CF) gsF v T0 16 (by decide)]
  exact run16_full h0 h1

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Where a thread stands at the border 16 the state's shape is T16**, in scope. -/
theorem shape16_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 16 k e m E) :
    sh₁B (pubOf X) CF e = T16 := by
  obtain ⟨hN, -, -, hlen, hsh0, -, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h6 := six_sourced hs scope
  have h16 := shape_at T₁ (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) (a₀ := T0)
    (n := 19) (b := 16) (le_of_eq (by rw [hbs, hlen])) (by decide) hyes
    (fun k w h s₀ h1 h2 => by
      obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
      exact (start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hsh0)
    (fun j => by
      rw [hbs]
      exact carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N T₁.ft _ bw hw he ha j) h
  subst hN
  have q0 := entries_six X nKRFull P hs.named.plan h6 0 (by decide)
  have q1 := entries_six X nKRFull P hs.named.plan h6 1 (by decide)
  exact Except.ok.inj (h16.symm.trans (run16_six h6 _ _ _ q0 q1))

/-- **Message 0 of T16**: one mask row, one answer, its ledger behind 48 takes, 255 free entries. -/
def t16Ok : Bool :=
  match T16.1.st.oracles[0]? with
  | some o =>
    o.shape.maskRows == 1 && o.shape.answers == 1 &&
      Send.freeMaskEntries o.shape.maskRows (CF.mask.getD o.shape.maskCode default).ell
        o.shape.answers == 255 &&
      match o.ledger with
      | some l => l.next == 48 && l.left == 207 && l.rows == 1 && l.logRows == 0
      | none => false
  | none => false

theorem t16_ok : t16Ok = true := by decide +kernel

/-- **Behind the border 16 message 0's ledger stands at 48 takes, with one mask row.** -/
theorem ledger_of_shape16 {Q : Pub1} {e : FirstState} (h : sh₁B Q CF e = T16) :
    LedgerAt e.d.st 0 48 ∧ ∃ x : OnBytes.Oracle, e.d.st.oracles[0]? = some x ∧
      x.shape.maskRows = 1 := by
  have h1 : shD e.d = T16.1 := congrArg Prod.fst h
  have hst : stSh e.d.st = T16.1.st := congrArg (·.st) h1
  have hc : e.d.st.codes = CF := (congrArg (·.codes) hst).trans codes16
  have ho : (e.d.st.oracles[0]?).map orcSh = T16.1.st.oracles[0]? := by
    have := congrArg (fun S => S.oracles[0]?) hst
    simpa [stSh] using this
  have hk := t16_ok
  unfold t16Ok at hk
  rw [← ho] at hk
  obtain ⟨x, hx⟩ : ∃ x, e.d.st.oracles[0]? = some x := by
    cases hx : e.d.st.oracles[0]? with
    | none =>
      rw [hx] at hk
      cases hk
    | some x => exact ⟨x, rfl⟩
  rw [hx] at hk
  simp only [Option.map_some, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨⟨⟨a', b'⟩, fr⟩, hl⟩ := hk
  have a₁ : x.shape.maskRows = 1 := a'
  have b₁ : x.shape.answers = 1 := b'
  have f₁ : Send.freeMaskEntries x.shape.maskRows (CF.mask.getD x.shape.maskCode default).ell
      x.shape.answers = 255 := fr
  obtain ⟨l, hl', e1, e2, e3, e4⟩ : ∃ l, x.ledger = some l ∧ l.next = 48 ∧ l.left = 207 ∧ l.rows = 1 ∧
      l.logRows = 0 := by
    have hl₂ : (match x.ledger with
      | some l => l.next == 48 && l.left == 207 && l.rows == 1 && l.logRows == 0
      | none => false) = true := hl
    cases hxl : x.ledger with
    | none =>
      rw [hxl] at hl₂
      cases hl₂
    | some l =>
      rw [hxl] at hl₂
      simp only [Bool.and_eq_true, beq_iff_eq] at hl₂
      exact ⟨l, rfl, hl₂.1.1.1, hl₂.1.1.2, hl₂.1.2, hl₂.2⟩
  refine ⟨⟨x, l, hx, hl', by omega, by omega, by omega, ?_, ?_, ?_⟩, x, hx, a₁⟩
  · rw [a₁, e4]
    rfl
  · rw [hc, e2, f₁]
  · rw [a₁, e1, AtPublicFiles.FirstH.nextAt_one]

/-- **Take number j behind the border 16 is entry 48 + j.** -/
theorem takes_at16 {Q : Pub1} {e : FirstState} (h : sh₁B Q CF e = T16) {n : Nat}
    {t : List Nat × _}
    (ht : takeMasksP e.d 0 n = some t) {j : Nat} (hj : j < n) : t.1.getD j 0 = 48 + j := by
  obtain ⟨hk, x, hx, hm⟩ := ledger_of_shape16 h
  have e1 := AtPublicFiles.FirstH.takeMasksInto_numbers 0 n e.d #[] t 48 x hx hk ht
  rw [e1, hm]
  simp [hj, List.getD_eq_getElem?_getD, AtPublicFiles.FirstH.takenNo_one]

end AtPublicFiles.AtFiles.Full
