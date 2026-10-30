-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieShared.lean: the closing of a segment (K10): the one equation that the field tie of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean) is brought down to in Pay/XchOwedMembers.lean, at a member that the shared sending
(the kind K1) has sent and in which no table rides: a segment's messages of its later moments, and the first segment's own.

The shared sending lays a message's rows by a text of its own (`K1.rowsR`, Honest/K1/Coins.lean); the closing's job makes them
anew by the code switch's (`messageRows`, Honest/K2/Sending.lean). That the two lay the same rows is the library's
(`laid_shared`, `rowsR_shared`, Honest/K2/Law/SameRows.lean). What is added here: the two callers hand their data in two forms.

  `shared_asRow`     the shared text's rows are the same at data O and at O read "as a row of its field takes it" (`asRow`,
                   Honest/K2/Half.lean) and handed back in the switch's form (`asShared`)
  `member_shared`    what `messageRows` returns at a cut of coins c is the shared text's rows at c and the cut's start
  **`tab_of_shared`**  the witness's table of the message is `K1.rowsMsg` of the rows Rr that the closing's job has made anew. From:
      hm, hp    the two ties on the script, at the shared sending's own texts (`tab_rows`, Honest/K1/ScriptTie.lean, has them)
      hc        the sender's cut off the run's coins
      hRr       Rr is `messageRows`' return at the sender's codes, the message's shape, data and a stretch kk
      hCoins    kk is the cut of the sender's coins at the message's start
      hData     data are the sender's job's data, read as a row of its field takes them
      hride, hpad, hword   public: no table rides in the message; its pad is no longer than a row; it has no main row or is
                sampled

Limits. The premises named are shown here of no script, book or run. No head and no thread is named.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SameRows
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie
import Johnson.Desc.ProofFile.Honest.K1.AgreeTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K2.Honest (zeroG)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open ProofFile.Honest.K2 (Stretch messageRows freshTable sharedRows asShared asRow coinAtShared)

/-- The shared text's rows at data O, and at O read as a row of its field takes it. -/
theorem shared_asRow {d : Due} (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (ρ : Option K1.Ride) (a : Due)
    (O : Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs d) :
    sharedRows codes s ρ a (asShared s fun r j => asRow (s.mainDeg == 3) (O r j)) c = sharedRows codes s ρ a O c := by
  have z0 : zeroG = 0 := K2.zeroG_eq
  refine K2.rows_ext _ _ ?_ ?_ rfl rfl rfl rfl
  · funext r j
    unfold sharedRows asShared
    dsimp only
    by_cases h3 : (s.mainDeg == 3) = true
    · cases coinAtShared codes s ρ r j with
      | some i => rfl
      | none =>
        rcases O r j with _ | (x | x)
        · simp [h3, asRow, z0]
        · simp [h3, asRow, K1.asE_inl]
        · simp [h3, asRow]
    · simp [h3]
  · funext r j
    unfold sharedRows asShared
    dsimp only
    by_cases h3 : (s.mainDeg == 3) = true
    · simp [h3]
    · cases coinAtShared codes s ρ r j with
      | some i => rfl
      | none =>
        rcases O r j with _ | (x | x)
        · simp [h3, asRow, z0]
        · simp [h3, asRow, K1.asE_inl]
        · simp [h3, asRow, z0]

/-- What `messageRows` returns at a cut of coins is the shared text's rows at the coins and the cut's start. -/
theorem member_shared {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {data : Nat → Nat → Cb.Gl.E} {d a N : Due}
    {c : Cs d} {c' : Cs N} {Rr : Johnson.Prover.Send.Rows} (hcut : c.cut a N = some c')
    (h : messageRows freshTable codes s none data ⟨N, c'⟩ = .ok Rr)
    (hpad : (K1.stepsOf codes s none).pad ≤ (codes.base.getD s.code default).ell)
    (hword : s.mainRows = 0 ∨ s.answers ≠ 0) :
    Rr = sharedRows codes s none a (asShared s data) c := by
  obtain ⟨hs, hr, -, cF, cE, cM, cT, hF, hE, hM, hT, rfl⟩ := K2.messageRows_laid h
  exact K2.laid_shared ⟨hs, hpad, hr⟩ hword (fun _ _ _ _ _ => rfl) hcut hF hE hM hT

variable {Bk : ProverCoinCounts} {W Wl X Cells Tok : Type}

/-- **At a member that the shared sending has sent, the witness's table is the rows that the closing's job has made
anew.** -/
theorem tab_of_shared (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N : Nat) (wit : Wl → W)
    (J : K1.SendJob W X) (own₀ : X) (front n num j t : Nat)
    (hm : OwnMsgs Q Vd N num front (K1.msgTxt 0 wit J own₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => K1.padTxt 0 J n k))
    (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    {data : Nat → Nat → Cb.Gl.E} {kk : Stretch} {Rr : Johnson.Prover.Send.Rows}
    (hRr : messageRows freshTable J.P.codes (shapeAt J.P n) none data kk = .ok Rr)
    {M : Due} {c' : Cs M} (hcut : c.cut (K1.startR J.P J.ride n) M = some c') (hCoins : kk = ⟨M, c'⟩)
    (hData : data = fun r i => asRow ((shapeAt J.P n).mainDeg == 3)
      (J.data (wit w) { heard := hd.take front, own := own₀, seen := .bare [] } n r i))
    (hride : J.ride n = none)
    (hpad : (K1.stepsOf J.P.codes (shapeAt J.P n) none).pad ≤
      (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (hword : (shapeAt J.P n).mainRows = 0 ∨ (shapeAt J.P n).answers ≠ 0) :
    (Q.wit k w hd).tab J.P.codes (shapeAt J.P n) num j t = K1.rowsMsg (shapeAt J.P n) Rr := by
  have h1 := K1.tab_rows Q Vd N 0 wit J own₀ front n num j t hm hp k c hc w hw hd hN
  subst hCoins hData
  have e := member_shared hcut hRr hpad hword
  rw [shared_asRow] at e
  have e2 : K1.rowsLaid J own₀ c (wit w) (hd.take front) n = Rr := by
    rw [e]
    show K1.rowsR J.P J.ride _ c n = _
    rw [K2.rowsR_shared, hride]
  rw [h1, e2]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.shared_asRow
#print axioms ProofFile.Honest.K10.member_shared
#print axioms ProofFile.Honest.K10.tab_of_shared
